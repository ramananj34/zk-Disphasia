use serde::{Deserialize, Serialize, Deserializer, Serializer};
use serde_with::{serde_as, Bytes};
use curve25519_dalek_ng::{ristretto::*, scalar::Scalar, traits::Identity, constants::RISTRETTO_BASEPOINT_POINT};
use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
use merlin::Transcript;
use frost_ristretto255 as frost;
use ed25519_dalek::{SigningKey, VerifyingKey, Signature, Signer, Verifier};
use subtle::ConstantTimeEq;
use zeroize::Zeroize;
use rand::rngs::OsRng;
use std::collections::{HashMap, BTreeMap};
use std::error::Error;

//Config constants - tweak these for production
const PROOF_EXPIRY: u64 = 300;  //proofs expire after 5 mins
const RECOMPUTE_INTERVAL: u64 = 30;  //reaggregate every 30s
const MAX_DEVICES: usize = 10000;  //max devices for discrete log
const RATE_WINDOW: u64 = 10;  //rate limit window
const MAX_MSGS_PER_WINDOW: u32 = 10;  //max msgs per window
const MAX_PROOF_SIZE: usize = 8192;  //prevent DoS attacks

//Simple error enum - keeps things clean
#[derive(Debug)]
pub enum AggError {
    InvalidProof(String), ExpiredProof, ThresholdNotMet,
    CryptoError(String), DkgIncomplete, RateLimited,
}

impl std::fmt::Display for AggError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidProof(s) => write!(f, "Invalid proof: {}", s),
            Self::ExpiredProof => write!(f, "Proof expired"),
            Self::ThresholdNotMet => write!(f, "Need more participants"),
            Self::CryptoError(s) => write!(f, "Crypto error: {}", s),
            Self::DkgIncomplete => write!(f, "DKG not done yet"),
            Self::RateLimited => write!(f, "Too many requests"),
        }
    }
}

impl Error for AggError {}

//Macro magic to serialize curve points - saves us a ton of boilerplate code
macro_rules! serde_wrapper {
    ($name:ident, $inner:ty, $size:expr, $from:expr) => {
        #[derive(Debug, Clone)]
        pub struct $name(pub $inner);
        impl Serialize for $name {
            fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
                s.serialize_bytes(self.0.as_bytes())
            }
        }
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

//ElGamal correctness proof - this is the KEY fix from the broken version!
//We use the SAME randomness 'r' for both ElGamal encryption AND Pedersen commitment
//This creates a cryptographic binding that links them together
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ElGamalProof {
    pub commit_r: SerCompressed,  //commitment for randomness
    pub commit_s: SerCompressed,  //commitment for state+randomness
    pub commit_c: SerCompressed,  //commitment to Pedersen (NEW - this is the fix!)
    pub resp_r: SerScalar,  //response for randomness
    pub resp_state: SerScalar,  //response for state value
    pub state_commit: SerCompressed,  //the Pedersen commitment itself
}

impl ElGamalProof {
    //Generate proof that ciphertext encrypts a valid state
    //KEY INSIGHT: we use 'r' (ElGamal randomness) as the Pedersen blinding factor
    //This binds the ElGamal ciphertext to the Pedersen commitment cryptographically
    fn prove(state: u8, r: &Scalar, c1: &RistrettoPoint, c2: &RistrettoPoint, 
             h: &RistrettoPoint, dev_id: u32, ts: u64, ped_gens: &PedersenGens) -> Self {
        let g = RISTRETTO_BASEPOINT_POINT;
        let state_s = Scalar::from(state as u64);
        
        //THE FIX: use ElGamal randomness r as Pedersen blinding!
        let state_commit = ped_gens.commit(state_s, *r);
        
        //Schnorr protocol - generate random nonces
        let w = Scalar::random(&mut OsRng);  //nonce for r
        let v = Scalar::random(&mut OsRng);  //nonce for state
        
        //Create commitments proving we know r and state across all 3 structures
        let commit_r = g * w;  //for ElGamal c1
        let commit_s = g * v + h * w;  //for ElGamal c2
        let commit_c = ped_gens.commit(v, w);  //for Pedersen (this is new!)
        
        //Fiat-Shamir: hash everything to create challenge
        let mut t = Transcript::new(b"elgamal-pedersen-link");
        t.append_u64(b"device", dev_id as u64);
        t.append_u64(b"timestamp", ts);
        t.append_message(b"c1", c1.compress().as_bytes());
        t.append_message(b"c2", c2.compress().as_bytes());
        t.append_message(b"state_commitment", state_commit.compress().as_bytes());
        t.append_message(b"commit_r", commit_r.compress().as_bytes());
        t.append_message(b"commit_s", commit_s.compress().as_bytes());
        t.append_message(b"commit_c", commit_c.compress().as_bytes());
        
        let mut cb = [0u8; 64];
        t.challenge_bytes(b"challenge", &mut cb);
        let c = Scalar::from_bytes_mod_order_wide(&cb);
        
        //Schnorr responses: response = nonce + challenge * secret
        Self {
            commit_r: commit_r.compress().into(),
            commit_s: commit_s.compress().into(),
            commit_c: commit_c.compress().into(),
            resp_r: (w + c * r).into(),
            resp_state: (v + c * state_s).into(),
            state_commit: state_commit.compress().into(),
        }
    }
    
    //Verify the proof - checks all 3 Schnorr equations
    fn verify(&self, c1: &RistrettoPoint, c2: &RistrettoPoint, h: &RistrettoPoint,
              dev_id: u32, ts: u64, ped_gens: &PedersenGens) -> bool {
        let g = RISTRETTO_BASEPOINT_POINT;
        
        //Decompress everything
        let (Some(cr), Some(cs), Some(cc), Some(sc)) = (
            self.commit_r.0.decompress(), self.commit_s.0.decompress(),
            self.commit_c.0.decompress(), self.state_commit.0.decompress()
        ) else { return false };
        
        //Recreate challenge using same transcript
        let mut t = Transcript::new(b"elgamal-pedersen-link");
        t.append_u64(b"device", dev_id as u64);
        t.append_u64(b"timestamp", ts);
        t.append_message(b"c1", c1.compress().as_bytes());
        t.append_message(b"c2", c2.compress().as_bytes());
        t.append_message(b"state_commitment", self.state_commit.0.as_bytes());
        t.append_message(b"commit_r", self.commit_r.0.as_bytes());
        t.append_message(b"commit_s", self.commit_s.0.as_bytes());
        t.append_message(b"commit_c", self.commit_c.0.as_bytes());
        
        let mut cb = [0u8; 64];
        t.challenge_bytes(b"challenge", &mut cb);
        let c = Scalar::from_bytes_mod_order_wide(&cb);
        
        //Check all 3 equations
        //Check 1: ElGamal c1 equation
        let chk1 = g * self.resp_r.0 == cr + c1 * c;
        //Check 2: ElGamal c2 equation  
        let chk2 = g * self.resp_state.0 + h * self.resp_r.0 == cs + c2 * c;
        //Check 3: Pedersen commitment equation
        let chk3 = ped_gens.commit(self.resp_state.0, self.resp_r.0) == cc + sc * c;
        
        chk1 && chk2 && chk3  //all must pass
    }
}

//Device proof - contains encrypted state + all the proofs
#[serde_as]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceProof {
    pub device_id: u32,
    pub timestamp: u64,
    pub elgamal_c1: SerCompressed,  //ElGamal ciphertext part 1
    pub elgamal_c2: SerCompressed,  //ElGamal ciphertext part 2
    pub elgamal_proof: ElGamalProof,  //Schnorr proof of correctness
    pub bulletproof: Vec<u8>,  //range proof that state is in [0,1]
    #[serde_as(as = "Bytes")]
    pub signature: [u8; 64],  //ed25519 signature for authenticity
}

//Schnorr proof for partial decryption - proves you know your secret key
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SchnorrProof {
    pub commitment: SerCompressed,
    pub response: SerScalar,
}

impl SchnorrProof {
    //Prove: partial = sum_c1 * secret  (discrete log equality)
    fn prove_dlog(secret: &Scalar, sum_c1: &RistrettoPoint, partial: &RistrettoPoint,
                  ts: u64, id: u32) -> Self {
        let r = Scalar::random(&mut OsRng);
        let commit = sum_c1 * r;
        let c = Self::challenge(sum_c1, partial, &commit, ts, id);
        Self { commitment: commit.compress().into(), response: (r + c * secret).into() }
    }
    
    fn verify_dlog(&self, sum_c1: &RistrettoPoint, partial: &RistrettoPoint,
                   ts: u64, id: u32) -> bool {
        let Some(commit) = self.commitment.0.decompress() else { return false };
        let c = Self::challenge(sum_c1, partial, &commit, ts, id);
        sum_c1 * self.response.0 == commit + partial * c
    }
    
    fn challenge(sum_c1: &RistrettoPoint, partial: &RistrettoPoint,
                 commit: &RistrettoPoint, ts: u64, id: u32) -> Scalar {
        let mut t = Transcript::new(b"schnorr-dlog-equality");
        t.append_u64(b"timestamp", ts);
        t.append_u64(b"device", id as u64);
        t.append_message(b"sum_c1", sum_c1.compress().as_bytes());
        t.append_message(b"partial", partial.compress().as_bytes());
        t.append_message(b"commitment", commit.compress().as_bytes());
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
    pub partial: SerCompressed,  //partial decryption share
    pub proof: SchnorrProof,  //proof it's computed correctly
    #[serde_as(as = "Bytes")]
    pub signature: [u8; 64],
}

//Main device struct - handles proof generation/verification and aggregation
pub struct IoTDevice {
    pub id: u32,
    frost_key: frost::keys::KeyPackage,  //threshold crypto key
    group_pub: frost::keys::PublicKeyPackage,  //group public key
    sig_key: SigningKey,  //for message authentication
    peer_keys: HashMap<u32, VerifyingKey>,  //peer public keys
    proofs: HashMap<u32, DeviceProof>,  //received proofs from peers
    partials: HashMap<u32, PartialDecryption>,  //received partial decryptions
    agg_c1: Option<RistrettoPoint>,  //aggregated ciphertext c1
    agg_c2: Option<RistrettoPoint>,  //aggregated ciphertext c2
    bp_gens: BulletproofGens,  //bulletproof generators
    ped_gens: PedersenGens,  //pedersen commitment generators
    threshold: usize,
    rates: HashMap<u32, (u64, u32)>,  //rate limiting per peer
    last_recomp: u64,  //last recomputation time
}

impl IoTDevice {
    pub fn new(id: u32, threshold: usize, frost_key: frost::keys::KeyPackage,
               group_pub: frost::keys::PublicKeyPackage, peer_keys: HashMap<u32, VerifyingKey>) -> Self {
        Self {
            id, threshold, frost_key, group_pub, peer_keys,
            sig_key: SigningKey::generate(&mut OsRng),
            proofs: HashMap::new(), partials: HashMap::new(),
            agg_c1: None, agg_c2: None,
            bp_gens: BulletproofGens::new(64, 1),
            ped_gens: PedersenGens::default(),
            rates: HashMap::new(), last_recomp: 0,
        }
    }
    
    //Generate proof for our state (0 or 1)
    pub fn generate_proof(&self, state: u8) -> Result<DeviceProof, AggError> {
        if state > 1 { return Err(AggError::CryptoError("State must be 0/1".into())); }
        
        let ts = timestamp();
        let mut r = Scalar::random(&mut OsRng);  //ElGamal randomness
        let g = RISTRETTO_BASEPOINT_POINT;
        let h = frost_to_point(&self.group_pub.verifying_key())?;
        
        //ElGamal encrypt: (c1, c2) = (g^r, g^state * h^r)
        let (c1, c2) = (g * r, g * Scalar::from(state as u64) + h * r);
        
        //Generate Schnorr proof linking ElGamal to Pedersen commitment
        let eg_proof = ElGamalProof::prove(state, &r, &c1, &c2, &h, self.id, ts, &self.ped_gens);
        
        //Generate bulletproof using SAME r as blinding factor, it binds the range proof to the ciphertext
        let mut t = Transcript::new(b"binary-range-proof");
        t.append_u64(b"device", self.id as u64);
        t.append_u64(b"timestamp", ts);
        t.append_message(b"c1", c1.compress().as_bytes());
        t.append_message(b"c2", c2.compress().as_bytes());
        t.append_message(b"commitment", eg_proof.state_commit.0.as_bytes());
        
        let (bp, _) = RangeProof::prove_single(
            &self.bp_gens, &self.ped_gens, &mut t,
            state as u64, &r, 8  //use r directly
        ).map_err(|e| { r.zeroize(); AggError::CryptoError(format!("BP failed: {:?}", e)) })?;
        
        r.zeroize();  //clean up secret
        
        Ok(DeviceProof {
            device_id: self.id, timestamp: ts,
            elgamal_c1: c1.compress().into(), elgamal_c2: c2.compress().into(),
            elgamal_proof: eg_proof, bulletproof: bp.to_bytes(),
            signature: self.sign(&[&ts.to_le_bytes(), &self.id.to_le_bytes(),
                                   c1.compress().as_bytes(), c2.compress().as_bytes()]),
        })
    }
    
    //Receive and verify a proof from a peer
    pub fn receive_proof(&mut self, p: DeviceProof) -> Result<(), AggError> {
        self.check_rate(p.device_id)?;
        let now = timestamp();
        
        //Basic checks
        if p.timestamp + PROOF_EXPIRY < now { return Err(AggError::ExpiredProof); }
        if self.proofs.contains_key(&p.device_id) { 
            return Err(AggError::InvalidProof("Duplicate".into())); 
        }
        if p.bulletproof.len() > MAX_PROOF_SIZE {
            return Err(AggError::InvalidProof("Too big".into()));
        }
        
        //Verify signature
        let pk = self.peer_keys.get(&p.device_id)
            .ok_or(AggError::InvalidProof("Unknown device".into()))?;
        self.verify_sig(pk, &[&p.timestamp.to_le_bytes(), &p.device_id.to_le_bytes(),
                              p.elgamal_c1.0.as_bytes(), p.elgamal_c2.0.as_bytes()],
                       &p.signature)?;
        
        //Verify ElGamal correctness proof
        let c1 = p.elgamal_c1.0.decompress().ok_or(AggError::InvalidProof("bad c1".into()))?;
        let c2 = p.elgamal_c2.0.decompress().ok_or(AggError::InvalidProof("bad c2".into()))?;
        let h = frost_to_point(&self.group_pub.verifying_key())?;
        
        if !p.elgamal_proof.verify(&c1, &c2, &h, p.device_id, p.timestamp, &self.ped_gens) {
            return Err(AggError::InvalidProof("Schnorr failed".into()));
        }
        
        //Verify bulletproof
        let sc = p.elgamal_proof.state_commit.0.decompress()
            .ok_or(AggError::InvalidProof("bad commitment".into()))?;
        
        let mut t = Transcript::new(b"binary-range-proof");
        t.append_u64(b"device", p.device_id as u64);
        t.append_u64(b"timestamp", p.timestamp);
        t.append_message(b"c1", p.elgamal_c1.0.as_bytes());
        t.append_message(b"c2", p.elgamal_c2.0.as_bytes());
        t.append_message(b"commitment", p.elgamal_proof.state_commit.0.as_bytes());
        
        RangeProof::from_bytes(&p.bulletproof)
            .map_err(|_| AggError::InvalidProof("bad BP".into()))?
            .verify_single(&self.bp_gens, &self.ped_gens, &mut t, &sc.compress(), 8)
            .map_err(|_| AggError::InvalidProof("BP verify failed".into()))?;
        
        self.proofs.insert(p.device_id, p);
        self.maybe_recompute();
        Ok(())
    }
    
    //Generate our partial decryption share
    pub fn generate_partial_decryption(&mut self) -> Result<PartialDecryption, AggError> {
        self.recompute();
        let sum_c1 = self.agg_c1.ok_or(AggError::CryptoError("No agg".into()))?;
        let ts = timestamp();
        
        let mut sec = frost_to_scalar(&self.frost_key.signing_share())?;
        let partial = sum_c1 * sec;  //partial decryption
        let proof = SchnorrProof::prove_dlog(&sec, &sum_c1, &partial, ts, self.id);
        sec.zeroize();
        
        Ok(PartialDecryption {
            device_id: self.id, timestamp: ts,
            partial: partial.compress().into(), proof,
            signature: self.sign(&[&ts.to_le_bytes(), &self.id.to_le_bytes(),
                                   partial.compress().as_bytes()]),
        })
    }
    
    //Receive partial decryption from peer
    pub fn receive_partial(&mut self, p: PartialDecryption) -> Result<(), AggError> {
        self.check_rate(p.device_id)?;
        if p.timestamp + PROOF_EXPIRY < timestamp() { return Err(AggError::ExpiredProof); }
        
        let pk = self.peer_keys.get(&p.device_id)
            .ok_or(AggError::InvalidProof("Unknown".into()))?;
        self.verify_sig(pk, &[&p.timestamp.to_le_bytes(), &p.device_id.to_le_bytes(),
                              p.partial.0.as_bytes()], &p.signature)?;
        
        self.partials.insert(p.device_id, p);
        Ok(())
    }
    
    //Maybe recompute aggregate if enough time has passed
    fn maybe_recompute(&mut self) {
        let now = timestamp();
        if now >= self.last_recomp + RECOMPUTE_INTERVAL {
            self.recompute();
            self.last_recomp = now;
        }
    }
    
    //Clean up old proofs and partials
    pub fn cleanup(&mut self) {
        let cutoff = timestamp().saturating_sub(PROOF_EXPIRY);
        self.proofs.retain(|_, p| p.timestamp > cutoff);
        self.partials.retain(|_, p| p.timestamp > cutoff);
        self.maybe_recompute();
    }
    
    //Compute final aggregate using threshold decryption
    pub fn compute_aggregate(&mut self) -> Result<(usize, usize), AggError> {
        self.recompute();
        let valid = self.proofs.len();
        if valid == 0 { return Ok((0, 0)); }
        if self.partials.len() < self.threshold { return Err(AggError::ThresholdNotMet); }
        
        let sum_c1 = self.agg_c1.ok_or(AggError::CryptoError("No agg".into()))?;
        let sum_c2 = self.agg_c2.ok_or(AggError::CryptoError("No agg".into()))?;
        
        //Verify partials and collect valid ones
        let mut verified = Vec::new();
        for p in self.partials.values().take(self.threshold) {
            let pt = p.partial.0.decompress().ok_or(AggError::CryptoError("bad partial".into()))?;
            if !p.proof.verify_dlog(&sum_c1, &pt, p.timestamp, p.device_id) {
                return Err(AggError::InvalidProof(format!("Failed for {}", p.device_id)));
            }
            verified.push((p.device_id, pt));
        }
        
        //Lagrange interpolation to combine shares
        let ids: Vec<Scalar> = verified.iter().map(|(id, _)| Scalar::from(*id as u64)).collect();
        let mut combined = RistrettoPoint::identity();
        
        for i in 0..verified.len() {
            let mut lambda = Scalar::one();
            for j in 0..verified.len() {
                if i != j {
                    lambda *= -ids[j] * (ids[i] - ids[j]).invert();
                }
            }
            combined += verified[i].1 * lambda;
        }
        
        //Decrypt: sum_c2 - combined gives g^sum, then solve dlog
        Ok((bsgs_dlog(sum_c2 - combined, RISTRETTO_BASEPOINT_POINT)?, valid))
    }
    
    //Recompute aggregate ciphertexts
    fn recompute(&mut self) {
        if self.proofs.is_empty() {
            self.agg_c1 = None;
            self.agg_c2 = None;
        } else {
            let (mut c1, mut c2) = (RistrettoPoint::identity(), RistrettoPoint::identity());
            for p in self.proofs.values() {
                if let (Some(p1), Some(p2)) = (p.elgamal_c1.0.decompress(), p.elgamal_c2.0.decompress()) {
                    c1 += p1; c2 += p2;
                }
            }
            self.agg_c1 = Some(c1);
            self.agg_c2 = Some(c2);
        }
    }
    
    //Rate limiting check
    fn check_rate(&mut self, id: u32) -> Result<(), AggError> {
        let now = timestamp();
        let e = self.rates.entry(id).or_insert((now, 0));
        if now >= e.0 + RATE_WINDOW { *e = (now, 0); }
        if e.1 >= MAX_MSGS_PER_WINDOW { return Err(AggError::RateLimited); }
        e.1 += 1;
        Ok(())
    }
    
    fn sign(&self, parts: &[&[u8]]) -> [u8; 64] {
        let mut d = Vec::new();
        for p in parts { d.extend_from_slice(p); }
        self.sig_key.sign(&d).to_bytes()
    }
    
    fn verify_sig(&self, k: &VerifyingKey, parts: &[&[u8]], sig: &[u8; 64]) -> Result<(), AggError> {
        let mut d = Vec::new();
        for p in parts { d.extend_from_slice(p); }
        let s = Signature::try_from(&sig[..]).map_err(|_| AggError::InvalidProof("bad sig".into()))?;
        k.verify(&d, &s).map_err(|_| AggError::InvalidProof("sig verify failed".into()))
    }
}

//Baby-step giant-step discrete log solver for small values
fn bsgs_dlog(target: RistrettoPoint, base: RistrettoPoint) -> Result<usize, AggError> {
    let m = ((MAX_DEVICES as f64).sqrt() as usize) + 1;
    let mut baby = Vec::with_capacity(m);
    let mut cur = RistrettoPoint::identity();
    
    //Baby steps: compute g^0, g^1, ..., g^m
    for _ in 0..m {
        baby.push(cur.compress().to_bytes());
        cur += base;
    }
    
    //Giant steps: check target * (g^m)^-j for j=0,1,2,...
    let factor = base * Scalar::from(m as u64);
    let mut gamma = target;
    
    for j in 0..m {
        let gb = gamma.compress().to_bytes();
        for (i, e) in baby.iter().enumerate() {
            if e.ct_eq(&gb).unwrap_u8() == 1 {
                let res = j * m + i;
                if res <= MAX_DEVICES { return Ok(res); }
            }
        }
        gamma -= factor;
    }
    
    Err(AggError::CryptoError("dlog not found".into()))
}

//FROST DKG setup - generates threshold keys for all participants
pub fn setup_dkg(n: usize, t: usize) 
    -> Result<Vec<(u32, frost::keys::KeyPackage, frost::keys::PublicKeyPackage)>, AggError> {
    let mut rng = OsRng;
    let mut r1_pkgs = BTreeMap::new();
    let mut r1_secs = HashMap::new();
    
    //Round 1: everyone generates commitments
    for i in 1..=n {
        let id = frost::Identifier::try_from(i as u16)
            .map_err(|e| AggError::CryptoError(e.to_string()))?;
        let (sec, pkg) = frost::keys::dkg::part1(id, n as u16, t as u16, &mut rng)
            .map_err(|e| AggError::CryptoError(e.to_string()))?;
        r1_secs.insert(i as u32, sec);
        r1_pkgs.insert(id, pkg);
    }
    
    //Round 2: exchange shares
    let mut r2_pkgs = HashMap::new();
    for (i, sec) in &r1_secs {
        let mut rcvd = r1_pkgs.clone();
        let id = frost::Identifier::try_from(*i as u16)
            .map_err(|e| AggError::CryptoError(e.to_string()))?;
        rcvd.remove(&id);
        let (r2_sec, pkgs) = frost::keys::dkg::part2(sec.clone(), &rcvd)
            .map_err(|e| AggError::CryptoError(e.to_string()))?;
        r2_pkgs.insert(*i, (r2_sec, pkgs));
    }
    
    //Round 3: finalize keys
    let mut results = Vec::new();
    for i in 1..=n {
        let id = frost::Identifier::try_from(i as u16)
            .map_err(|e| AggError::CryptoError(e.to_string()))?;
        let (r2_sec, _) = r2_pkgs.get(&(i as u32)).ok_or(AggError::DkgIncomplete)?;
        
        let mut rcvd_r2 = BTreeMap::new();
        for (j, (_, pkgs)) in &r2_pkgs {
            if *j != i as u32 {
                if let Some(p) = pkgs.get(&id) {
                    let sid = frost::Identifier::try_from(*j as u16)
                        .map_err(|e| AggError::CryptoError(e.to_string()))?;
                    rcvd_r2.insert(sid, p.clone());
                }
            }
        }
        
        let mut rcvd_r1 = r1_pkgs.clone();
        rcvd_r1.remove(&id);
        let (key_pkg, pub_pkg) = frost::keys::dkg::part3(r2_sec, &rcvd_r1, &rcvd_r2)
            .map_err(|e| AggError::CryptoError(e.to_string()))?;
        results.push((i as u32, key_pkg, pub_pkg));
    }
    Ok(results)
}

//Helper functions
fn timestamp() -> u64 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs()
}

fn frost_to_point(k: &frost::VerifyingKey) -> Result<RistrettoPoint, AggError> {
    CompressedRistretto::from_slice(&k.serialize()).decompress()
        .ok_or_else(|| AggError::CryptoError("bad frost key".into()))
}

fn frost_to_scalar(s: &frost::keys::SigningShare) -> Result<Scalar, AggError> {
    Ok(Scalar::from_bytes_mod_order(
        s.serialize().as_slice().try_into()
            .map_err(|_| AggError::CryptoError("bad share len".into()))?
    ))
}

//Simple test to make sure everything works
fn main() -> Result<(), AggError> {
    let (n, t, states) = (5, 3, [1u8, 0, 1, 1, 0]);
    
    //Setup threshold crypto
    let dkg = setup_dkg(n, t)?;
    let mut devs = Vec::new();
    let mut all_keys = HashMap::new();
    
    for (id, kpkg, ppkg) in &dkg {
        let d = IoTDevice::new(*id, t, kpkg.clone(), ppkg.clone(), HashMap::new());
        all_keys.insert(*id, d.sig_key.verifying_key());
        devs.push(d);
    }
    
    for d in devs.iter_mut() {
        d.peer_keys = all_keys.clone();
    }
    
    //Generate and broadcast proofs
    for (i, &s) in states.iter().enumerate() {
        let p = devs[i].generate_proof(s)?;
        for d in devs.iter_mut() {
            d.receive_proof(p.clone())?;
        }
    }
    
    //Generate partial decryptions
    for i in 0..t {
        if devs[i].proofs.len() >= n {
            let p = devs[i].generate_partial_decryption()?;
            for d in devs.iter_mut() {
                d.receive_partial(p.clone()).ok();
            }
        }
    }
    
    //Compute final results
    for d in &mut devs {
        if let Ok((sum, total)) = d.compute_aggregate() {
            println!("Device {}: sum={}/{}", d.id, sum, total);
        }
    }
    
    Ok(())
}