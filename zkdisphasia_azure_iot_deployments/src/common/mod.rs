use serde::{Deserialize, Serialize, Deserializer, Serializer};
use serde_with::{serde_as, Bytes};
use curve25519_dalek_ng::{ristretto::*, scalar::Scalar, traits::Identity, constants::RISTRETTO_BASEPOINT_POINT};
use merlin::Transcript;
use frost_ristretto255 as frost;
use ed25519_dalek::{SigningKey, VerifyingKey, Signature, Signer, Verifier};
use zeroize::Zeroize;
use subtle::{Choice, ConditionallySelectable};
use rand::rngs::OsRng;
use std::collections::{HashMap, BTreeMap};
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

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifiedCiphertext {
    pub timestamp: u64,
    #[serde(serialize_with = "ser_point", deserialize_with = "de_point")]
    pub c1: RistrettoPoint,
    #[serde(serialize_with = "ser_point", deserialize_with = "de_point")]
    pub c2: RistrettoPoint,
}
fn ser_point<S>(point: &RistrettoPoint, serializer: S) -> Result<S::Ok, S::Error> where S: Serializer, { serializer.serialize_bytes(point.compress().as_bytes()) }
fn de_point<'de, D>(deserializer: D) -> Result<RistrettoPoint, D::Error> where D: Deserializer<'de>,{let bytes: Vec<u8> = Deserialize::deserialize(deserializer)?;if bytes.len() != 32 {return Err(serde::de::Error::custom("Invalid point length"));}CompressedRistretto::from_slice(&bytes).decompress().ok_or_else(|| serde::de::Error::custom("Invalid RistrettoPoint"))}

#[derive(Debug, Clone)]
pub struct VerifiedPartial {
    pub device_id: u32,
    pub timestamp: u64,
    pub partial: RistrettoPoint
}

pub fn timestamp() -> u64 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).expect("System clock is before Unix epoch").as_secs()
}

pub fn frost_to_point(k: &frost::VerifyingKey) -> Result<RistrettoPoint, AggError> {
    CompressedRistretto::from_slice(&k.serialize()).decompress().ok_or_else(|| AggError::CryptoError("bad frost key".into()))
}

pub fn frost_share_to_point(s: &frost::keys::VerifyingShare) -> Result<RistrettoPoint, AggError> {
    CompressedRistretto::from_slice(&s.serialize()).decompress().ok_or_else(|| AggError::CryptoError("bad frost share".into()))
}

pub fn frost_to_scalar(s: &frost::keys::SigningShare) -> Result<Scalar, AggError> {
    Ok(Scalar::from_bytes_mod_order(s.serialize().as_slice().try_into().map_err(|_| AggError::CryptoError("bad share len".into()))?))
}

//Baby-step giant-step discrete log solver (constant-time)
pub fn bsgs_dlog(target: RistrettoPoint, base: RistrettoPoint) -> Result<usize, AggError> {
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

//Schnorr proof for partial decryption
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SchnorrProof {
    pub commitment_g: SerCompressed,
    pub commitment_c: SerCompressed,
    pub response: SerScalar,
}
impl SchnorrProof {
    //Prove: partial = sum_c1 * secret  (discrete log equality)
    pub fn prove(secret: &Scalar, sum_c1: &RistrettoPoint, partial: &RistrettoPoint, public_key_share: &RistrettoPoint, ts: u64, id: u32) -> Self {
        let g = RISTRETTO_BASEPOINT_POINT;
        let mut r = Scalar::random(&mut OsRng);
        let commit_g = g * r;
        let commit_c = sum_c1 * r;
        let c = Self::challenge(sum_c1, partial, public_key_share, &commit_g, &commit_c, ts, id);
        let result = Self { commitment_g: commit_g.compress().into(),commitment_c: commit_c.compress().into(),response: (r + c * secret).into() };
        r.zeroize();
        result
    }
    pub fn verify(&self, sum_c1: &RistrettoPoint, partial: &RistrettoPoint, public_key_share: &RistrettoPoint, ts: u64, id: u32) -> bool {
        let g = RISTRETTO_BASEPOINT_POINT;
        let Some(commit_g) = self.commitment_g.0.decompress() else { return false };
        let Some(commit_c) = self.commitment_c.0.decompress() else { return false };
        let c = Self::challenge(sum_c1, partial, public_key_share, &commit_g, &commit_c, ts, id);
        let check1 = g * self.response.0 == commit_g + public_key_share * c;
        let check2 = sum_c1 * self.response.0 == commit_c + partial * c;
        check1 && check2
    }
    fn challenge(sum_c1: &RistrettoPoint, partial: &RistrettoPoint, public_key_share: &RistrettoPoint, commit_g: &RistrettoPoint, commit_c: &RistrettoPoint, ts: u64, id: u32) -> Scalar {
        let mut t = Transcript::new(b"schnorr-dlog-equality");
        t.append_message(b"protocol_version", &[PROTOCOL_VERSION]);
        t.append_u64(b"timestamp", ts);
        t.append_u64(b"device", id as u64);
        t.append_message(b"sum_c1", sum_c1.compress().as_bytes());
        t.append_message(b"partial", partial.compress().as_bytes());
        t.append_message(b"public_key_share", public_key_share.compress().as_bytes());
        t.append_message(b"commitment_g", commit_g.compress().as_bytes());
        t.append_message(b"commitment_c", commit_c.compress().as_bytes());
        let mut b = [0u8; 64];
        t.challenge_bytes(b"challenge", &mut b);
        Scalar::from_bytes_mod_order_wide(&b)
    }
}

//Partial decryption from a threshold participant
#[serde_as]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PartialDecryption {
    pub device_id: u32,
    pub timestamp: u64,
    pub partial: SerCompressed,
    pub proof: SchnorrProof,
    #[serde_as(as = "Bytes")]
    pub signature: [u8; 64],
}

//Sign with signature
pub fn sign(sig_key: &SigningKey, parts: &[&[u8]]) -> [u8; 64] {
    let mut d = Vec::new();
    for p in parts { d.extend_from_slice(p); }
    sig_key.sign(&d).to_bytes()
}
//Verify signature
pub fn verify_sig(k: &VerifyingKey, parts: &[&[u8]], sig: &[u8; 64]) -> Result<(), AggError> {
    let mut d = Vec::new();
    for p in parts { d.extend_from_slice(p); }
    let s = Signature::try_from(&sig[..]).map_err(|_| AggError::InvalidProof("bad sig".into()))?;
    k.verify(&d, &s).map_err(|_| AggError::InvalidProof("sig verify failed".into()))
}
//Rate limiting check
pub fn check_rate(id: u32, rates: &mut HashMap<u32, (u64, u32)>) -> Result<(), AggError> {
    let now = timestamp();
    //Global rate limit
    let total_msgs: u32 = rates.values().filter(|(ts, _)| now < ts.saturating_add(RATE_WINDOW)).map(|(_, count)| count).sum();
    if total_msgs >= MAX_TOTAL_RATE { return Err(AggError::RateLimited); }
    //Per-device rate limit
    let e = rates.entry(id).or_insert((now, 0));
    //Reset window if expired
    if now >= e.0.saturating_add(RATE_WINDOW) { *e = (now, 0); }
    if e.1 >= MAX_MSGS_PER_WINDOW { return Err(AggError::RateLimited); }
    e.1 = e.1.saturating_add(1);
    //Cleanup
    if rates.len() > 1000 {
        let cutoff = now.saturating_sub(RATE_WINDOW * 2);
        rates.retain(|_, (ts, _)| *ts > cutoff);
    }
    Ok(())
}

pub fn generate_partial_decryption(device_id: u32,key_package: &frost::keys::KeyPackage,public_key_package: &frost::keys::PublicKeyPackage,sig_key: &SigningKey,verified_ciphertexts: &[VerifiedCiphertext]) -> Result<PartialDecryption, AggError> {
    if verified_ciphertexts.is_empty() { return Err(AggError::ThresholdNotMet); }
    let agg_c1: RistrettoPoint = verified_ciphertexts.iter().map(|vc| vc.c1).sum();
    let ts = timestamp();
    let secret_share = frost_to_scalar(key_package.signing_share())?;
    let partial = agg_c1 * secret_share;
    let my_id = frost::Identifier::try_from(device_id as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
    let verification_share = public_key_package.verifying_shares().get(&my_id).ok_or_else(|| AggError::CryptoError("no verification share".into()))?;
    let verification_point = frost_share_to_point(verification_share)?;
    let cp_proof = SchnorrProof::prove(&secret_share, &agg_c1, &partial, &verification_point, ts, device_id);
    let sig = sign(sig_key,&[&ts.to_le_bytes(),&device_id.to_le_bytes(),partial.compress().as_bytes()]);
    Ok(PartialDecryption {
        device_id,
        timestamp: ts,
        partial: partial.compress().into(),
        proof: cp_proof,
        signature: sig,
    })
}

pub fn receive_partial(partial: PartialDecryption,peer_keys: &HashMap<u32, VerifyingKey>,public_key_package: &frost::keys::PublicKeyPackage,verified_ciphertexts: &[VerifiedCiphertext],verified_partials: &mut Vec<VerifiedPartial>,rates: &mut HashMap<u32, (u64, u32)>) -> Result<VerifiedPartial, AggError> {
    if verified_partials.len() >= MAX_STORED_PARTIALS {
        let now = timestamp();
        let cutoff = now.saturating_sub(PROOF_EXPIRY * 2);
        verified_partials.retain(|vp| vp.timestamp > cutoff);
        if verified_partials.len() >= MAX_STORED_PARTIALS {return Err(AggError::RateLimited);}
    }
    check_rate(partial.device_id, rates)?;
    let now = timestamp();
    let adjusted_now = now + MAX_CLOCK_SKEW;
    if partial.timestamp > adjusted_now {return Err(AggError::InvalidProof("Timestamp too far in future".into()));}
    if partial.timestamp + PROOF_EXPIRY < now.saturating_sub(MAX_CLOCK_SKEW) {return Err(AggError::ExpiredProof);}
    let peer_key = peer_keys.get(&partial.device_id).ok_or_else(|| AggError::InvalidProof("Unknown device".into()))?;
    let agg_c1: RistrettoPoint = verified_ciphertexts.iter().map(|vc| vc.c1).sum();
    let partial_point = partial.partial.0.decompress().ok_or_else(|| AggError::InvalidProof("Invalid partial point".into()))?;
    verify_sig(peer_key,&[&partial.timestamp.to_le_bytes(),&partial.device_id.to_le_bytes(),partial.partial.0.as_bytes()],&partial.signature)?;
    let peer_id = frost::Identifier::try_from(partial.device_id as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
    let verification_share = public_key_package.verifying_shares().get(&peer_id).ok_or_else(|| AggError::CryptoError("Unknown participant".into()))?;
    let verification_point = frost_share_to_point(verification_share)?;
    if !partial.proof.verify(&agg_c1, &partial_point, &verification_point, partial.timestamp, partial.device_id) {return Err(AggError::InvalidProof("Schnorr proof verification failed".into()));}
    let verified = VerifiedPartial {device_id: partial.device_id,timestamp: partial.timestamp,partial: partial_point};
    verified_partials.push(verified.clone());
    Ok(verified)
}

pub fn compute_aggregate(threshold: usize,verified_ciphertexts: &[VerifiedCiphertext],verified_partials: &[VerifiedPartial]) -> Result<(usize, usize), AggError> {
    if verified_partials.len() < threshold {return Err(AggError::ThresholdNotMet);}
    let agg_c2: RistrettoPoint = verified_ciphertexts.iter().map(|vc| vc.c2).sum();
    let ids_scalars: Vec<Scalar> = verified_partials.iter().take(threshold).map(|vp| Scalar::from(vp.device_id as u64)).collect();
    let mut interpolated = RistrettoPoint::identity();
    for i in 0..threshold {
        let mut lambda = Scalar::one();
        for j in 0..threshold {
            if i != j {
                let diff = ids_scalars[i] - ids_scalars[j];
                if diff == Scalar::zero() {return Err(AggError::CryptoError("Cannot compute Lagrange with duplicate IDs".into()));}
                let inv = diff.invert();
                lambda *= -ids_scalars[j] * inv;
            }
        }
        let partial = &verified_partials[i].partial;
        interpolated += partial * lambda;
    }
    let decrypted = agg_c2 - interpolated;
    let count = bsgs_dlog(decrypted, RISTRETTO_BASEPOINT_POINT)?;
    let total = verified_ciphertexts.len();
    Ok((count, total))
}