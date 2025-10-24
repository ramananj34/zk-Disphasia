use serde::{Deserialize, Serialize, Deserializer, Serializer};
use curve25519_dalek_ng::{ristretto::*, scalar::Scalar, traits::Identity, constants::RISTRETTO_BASEPOINT_POINT};
use frost_ristretto255 as frost;
use ed25519_dalek::{SigningKey, VerifyingKey, Signature, Signer, Verifier};
use zeroize::Zeroize;
use subtle::{Choice, ConditionallySelectable};
use rand::rngs::OsRng;
use rand::RngCore;
use std::collections::{HashMap, HashSet, BTreeMap};
use std::error::Error;

pub const PROOF_EXPIRY: u64 = 300;
pub const MAX_DEVICES: usize = 10000;
pub const RATE_WINDOW: u64 = 10;
pub const MAX_MSGS_PER_WINDOW: u32 = 10;
pub const MAX_TOTAL_RATE: u32 = 50;
pub const MAX_CLOCK_SKEW: u64 = 60;
pub const MAX_NONCES_PER_DEVICE: usize = 100;
pub const MAX_STORED_PROOFS: usize = 10000;
pub const MAX_STORED_PARTIALS: usize = 10000;
pub const PROTOCOL_VERSION: u8 = 1;

//Simple error enum
#[derive(Debug)]
pub enum AggError { InvalidProof(String), ExpiredProof, ThresholdNotMet, CryptoError(String), DkgIncomplete, RateLimited } //Simple error enum
impl std::fmt::Display for AggError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self { Self::InvalidProof(s) => write!(f, "Invalid proof: {}", s), Self::ExpiredProof => write!(f, "Proof expired"), Self::ThresholdNotMet => write!(f, "Need more participants"), Self::CryptoError(s) => write!(f, "Crypto error: {}", s), Self::DkgIncomplete => write!(f, "DKG not done yet"), Self::RateLimited => write!(f, "Too many requests") }
    }
} impl Error for AggError {} //Turn it into an error

//Custom wrapper for serialization
macro_rules! serde_wrapper {
    ($name:ident, $inner:ty, $size:expr, $from:expr) => {
        #[derive(Debug, Clone)]
        pub struct $name(pub $inner);
        impl Serialize for $name { fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> { s.serialize_bytes(self.0.as_bytes()) } }
        impl<'de> Deserialize<'de> for $name {
            fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
                let b = Vec::<u8>::deserialize(d)?;
                if b.len() != $size { return Err(serde::de::Error::custom("bad length")); }
                let mut a = [0u8; $size]; a.copy_from_slice(&b);
                Ok($name($from(a)))
            }
        }
        impl From<$inner> for $name { fn from(v: $inner) -> Self { $name(v) } }
        impl From<$name> for $inner { fn from(v: $name) -> Self { v.0 } }
    };
}
serde_wrapper!(SerCompressed, CompressedRistretto, 32, CompressedRistretto);
serde_wrapper!(SerScalar, Scalar, 32, Scalar::from_bytes_mod_order);

#[derive(Debug, Clone)]
struct VerifiedCiphertext {
    timestamp: u64,
    c1: RistrettoPoint,
    c2: RistrettoPoint,
}

#[derive(Debug, Clone)]
struct VerifiedPartial {
    device_id: u32,
    timestamp: u64,
    partial: RistrettoPoint
}

fn timestamp() -> u64 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).expect("System clock is before Unix epoch").as_secs()
}

fn frost_to_point(k: &frost::VerifyingKey) -> Result<RistrettoPoint, AggError> {
    CompressedRistretto::from_slice(&k.serialize()).decompress().ok_or_else(|| AggError::CryptoError("bad frost key".into()))
}

fn frost_share_to_point(s: &frost::keys::VerifyingShare) -> Result<RistrettoPoint, AggError> {
    CompressedRistretto::from_slice(&s.serialize()).decompress().ok_or_else(|| AggError::CryptoError("bad frost share".into()))
}

fn frost_to_scalar(s: &frost::keys::SigningShare) -> Result<Scalar, AggError> {
    Ok(Scalar::from_bytes_mod_order(s.serialize().as_slice().try_into().map_err(|_| AggError::CryptoError("bad share len".into()))?))
}

//Baby-step giant-step discrete log solver (constant-time)
fn bsgs_dlog(target: RistrettoPoint, base: RistrettoPoint) -> Result<usize, AggError> {
    let m = ((MAX_DEVICES as f64).sqrt() as usize) + 1;
    //Baby steps: build lookup table
    let mut baby_table = HashMap::with_capacity(m);
    let mut cur = RistrettoPoint::identity();
    for i in 0..m {
        baby_table.insert(cur.compress().to_bytes(), i);
        cur += base;
    }
    //Giant steps
    let factor = base * Scalar::from(m as u64);
    let mut gamma = target;
    let mut found_i = 0u64;
    let mut found_j = 0u64;
    let mut found = Choice::from(0u8);
    for j in 0..m {
        let gb = gamma.compress().to_bytes();
        if let Some(&i) = baby_table.get(&gb) {
            let res = j * m + i;
            let valid = Choice::from((res <= MAX_DEVICES) as u8);
            let not_found_yet = !found;
            let should_update = valid & not_found_yet;
            let i64 = i as u64;
            let j64 = j as u64;
            found_i = u64::conditional_select(&found_i, &i64, should_update);
            found_j = u64::conditional_select(&found_j, &j64, should_update);
            found |= should_update;
        }
        gamma -= factor;
    }
    //check if found
    if bool::from(found) {
        let result = (found_j * (m as u64) + found_i) as usize;
        Ok(result)
    } else {
        Err(AggError::CryptoError("dlog not found".into()))
    }
}

//FROST DKG setup - generates threshold keys for all participants
pub fn setup_dkg(n: usize, t: usize) -> Result<Vec<(u32, frost::keys::KeyPackage, frost::keys::PublicKeyPackage)>, AggError> {
    let mut rng = OsRng;
    let mut r1_pkgs = BTreeMap::new();
    let mut r1_secs = HashMap::new();
    for i in 1..=n {
        let id = frost::Identifier::try_from(i as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
        let (sec, pkg) = frost::keys::dkg::part1(id, n as u16, t as u16, &mut rng).map_err(|e| AggError::CryptoError(e.to_string()))?;
        r1_secs.insert(i as u32, sec);
        r1_pkgs.insert(id, pkg);
    }
    let mut r2_pkgs = HashMap::new();
    for (i, sec) in &r1_secs {
        let mut rcvd = r1_pkgs.clone();
        let id = frost::Identifier::try_from(*i as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
        rcvd.remove(&id);
        let (r2_sec, pkgs) = frost::keys::dkg::part2(sec.clone(), &rcvd).map_err(|e| AggError::CryptoError(e.to_string()))?;
        r2_pkgs.insert(*i, (r2_sec, pkgs));
    }
    let mut results = Vec::new();
    for i in 1..=n {
        let id = frost::Identifier::try_from(i as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
        let (r2_sec, _) = r2_pkgs.get(&(i as u32)).ok_or(AggError::DkgIncomplete)?;
        let mut rcvd_r2 = BTreeMap::new();
        for (j, (_, pkgs)) in &r2_pkgs {
            if *j != i as u32 {
                if let Some(p) = pkgs.get(&id) {
                    let sid = frost::Identifier::try_from(*j as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
                    rcvd_r2.insert(sid, p.clone());
                }
            }
        }
        let mut rcvd_r1 = r1_pkgs.clone();
        rcvd_r1.remove(&id);
        let (key_pkg, pub_pkg) = frost::keys::dkg::part3(r2_sec, &rcvd_r1, &rcvd_r2).map_err(|e| AggError::CryptoError(e.to_string()))?;
        results.push((i as u32, key_pkg, pub_pkg));
    }
    Ok(results)
}

//DKG Phase 1 - Generate commitments (self-contained)
pub fn dkg_phase1(device_id: u32,n: usize,t: usize) -> Result<(frost::keys::dkg::round1::SecretPackage, frost::keys::dkg::round1::Package), AggError> {
    let mut rng = OsRng;
    let id = frost::Identifier::try_from(device_id as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
    frost::keys::dkg::part1(id, n as u16, t as u16, &mut rng).map_err(|e| AggError::CryptoError(e.to_string()))
}

//DKG Phase 2 - Receive & verify shares from n-1 peers
pub fn dkg_phase2(secret_package: frost::keys::dkg::round1::SecretPackage,received_packages: &BTreeMap<frost::Identifier, frost::keys::dkg::round1::Package>,) -> Result<(frost::keys::dkg::round2::SecretPackage, BTreeMap<frost::Identifier, frost::keys::dkg::round2::Package>), AggError> {
    frost::keys::dkg::part2(secret_package, received_packages).map_err(|e| AggError::CryptoError(e.to_string()))
}

//DKG Phase 3 - Combine shares into key package
pub fn dkg_phase3(round2_secret: &frost::keys::dkg::round2::SecretPackage,round1_packages: &BTreeMap<frost::Identifier, frost::keys::dkg::round1::Package>,round2_packages: &BTreeMap<frost::Identifier, frost::keys::dkg::round2::Package>) -> Result<(frost::keys::KeyPackage, frost::keys::PublicKeyPackage), AggError> {
    frost::keys::dkg::part3(round2_secret, round1_packages, round2_packages).map_err(|e| AggError::CryptoError(e.to_string()))
}