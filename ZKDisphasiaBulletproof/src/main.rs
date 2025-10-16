//ZK-Disphasia Bulletproof edition

//Libraries
use serde::{Deserialize, Serialize, Deserializer, Serializer}; //Serialization and deserialization
use serde_with::{serde_as, Bytes}; //Serialization and deserialization
use curve25519_dalek_ng::{ristretto::*, scalar::Scalar, traits::Identity, constants::RISTRETTO_BASEPOINT_POINT}; //The Curve
use bulletproofs::{BulletproofGens, PedersenGens, RangeProof}; //Bulletproofs
use merlin::Transcript; //Transcript
use frost_ristretto255 as frost; //FROST
use ed25519_dalek::{SigningKey, VerifyingKey, Signature, Signer, Verifier}; //Digital signatures
use zeroize::Zeroize; //Secure data deletion
use subtle::{Choice, ConditionallySelectable}; //Constant time operations
use rand::rngs::OsRng; //Random
use rand::RngCore; //Random
use std::collections::{HashMap, HashSet, BTreeMap}; //Data Structures
use std::error::Error; //Errors

//Config constants
const PROOF_EXPIRY: u64 = 300; //proofs expire after 5 mins
const RECOMPUTE_INTERVAL: u64 = 30; //reaggregate every 30s
const MAX_DEVICES: usize = 10000; //max devices for discrete log
const RATE_WINDOW: u64 = 10; //rate limit window
const MAX_MSGS_PER_WINDOW: u32 = 10; //max msgs per window
const MAX_TOTAL_RATE: u32 = 50; //global max messages
const MAX_PROOF_SIZE: usize = 8192; //prevent DoS attacks
const MAX_CLOCK_SKEW: u64 = 60; //Allow for a time skew
const MAX_NONCES_PER_DEVICE: usize = 100; //More DoS protection
const MAX_STORED_PROOFS: usize = 10000; //More DoS Protection
const MAX_STORED_PARTIALS: usize = 10000; //more DoS Protection
const PROTOCOL_VERSION: u8 = 1; //Version for transcript

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

//ElGamal correctness proof
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ElGamalProof {
    pub commit_r: SerCompressed, //commitment for randomness
    pub commit_s: SerCompressed, //commitment for state+randomness
    pub commit_c: SerCompressed, //commitment to Pedersen
    pub resp_r: SerScalar, //response for randomness
    pub resp_state: SerScalar, //response for state value
    pub state_commit: SerCompressed, //the Pedersen commitment itself
}
impl ElGamalProof {
    //Generate proof that ciphertext encrypts a valid state
    fn prove(state: u8, r: &Scalar, c1: &RistrettoPoint, c2: &RistrettoPoint, h: &RistrettoPoint, dev_id: u32, ts: u64, nonce: &[u8; 32], ped_gens: &PedersenGens) -> Self {
        //Setup
        let g = RISTRETTO_BASEPOINT_POINT;
        let state_s = Scalar::from(state as u64);
        let state_commit = ped_gens.commit(state_s, *r);
        //Random nonces
        let mut w = Scalar::random(&mut OsRng); //nonce for r
        let mut v = Scalar::random(&mut OsRng); //nonce for state
        //Create commitments
        let commit_r = g * w; //for ElGamal c1
        let commit_s = g * v + h * w; //for ElGamal c2
        let commit_c = ped_gens.commit(v, w);
        //Build a transcript (Fiat-Shamir)
        let mut t = Transcript::new(b"elgamal-pedersen-link");
        t.append_message(b"protocol_version", &[PROTOCOL_VERSION]);
        t.append_u64(b"device", dev_id as u64);
        t.append_u64(b"timestamp", ts);
        t.append_message(b"nonce", nonce);
        t.append_message(b"c1", c1.compress().as_bytes());
        t.append_message(b"c2", c2.compress().as_bytes());
        t.append_message(b"state_commitment", state_commit.compress().as_bytes());
        t.append_message(b"commit_r", commit_r.compress().as_bytes());
        t.append_message(b"commit_s", commit_s.compress().as_bytes());
        t.append_message(b"commit_c", commit_c.compress().as_bytes());
        //Derive a challange
        let mut cb = [0u8; 64];
        t.challenge_bytes(b"challenge", &mut cb);
        let c = Scalar::from_bytes_mod_order_wide(&cb);
        //Compute Schnorr responses
        let result = Self {
            commit_r: commit_r.compress().into(),
            commit_s: commit_s.compress().into(),
            commit_c: commit_c.compress().into(),
            resp_r: (w + c * r).into(),
            resp_state: (v + c * state_s).into(),
            state_commit: state_commit.compress().into(),
        };
        //Clean up secrets
        w.zeroize();
        v.zeroize();
        result
    }
    
    //Verify the proof - checks all 3 Schnorr equations
    fn verify(&self, c1: &RistrettoPoint, c2: &RistrettoPoint, h: &RistrettoPoint, dev_id: u32, ts: u64, nonce: &[u8; 32], ped_gens: &PedersenGens) -> bool {
        let g = RISTRETTO_BASEPOINT_POINT;
        //Decompress everything, construct points
        let (Some(cr), Some(cs), Some(cc), Some(sc)) = ( self.commit_r.0.decompress(), self.commit_s.0.decompress(), self.commit_c.0.decompress(), self.state_commit.0.decompress() ) else { return false };
        //Recreate challenge using same transcript
        let mut t = Transcript::new(b"elgamal-pedersen-link");
        t.append_message(b"protocol_version", &[PROTOCOL_VERSION]);
        t.append_u64(b"device", dev_id as u64);
        t.append_u64(b"timestamp", ts);
        t.append_message(b"nonce", nonce);
        t.append_message(b"c1", c1.compress().as_bytes());
        t.append_message(b"c2", c2.compress().as_bytes());
        t.append_message(b"state_commitment", self.state_commit.0.as_bytes());
        t.append_message(b"commit_r", self.commit_r.0.as_bytes());
        t.append_message(b"commit_s", self.commit_s.0.as_bytes());
        t.append_message(b"commit_c", self.commit_c.0.as_bytes());
        //Derive the challange
        let mut cb = [0u8; 64];
        t.challenge_bytes(b"challenge", &mut cb);
        let c = Scalar::from_bytes_mod_order_wide(&cb);
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
    pub device_id: u32, //Device ID
    pub timestamp: u64, //Timestamp
    pub nonce: [u8; 32], //Random nonce
    pub elgamal_c1: SerCompressed, //ElGamal ciphertext part 1
    pub elgamal_c2: SerCompressed, //ElGamal ciphertext part 2
    pub elgamal_proof: ElGamalProof, //Schnorr proof of correctness
    pub bulletproof: Vec<u8>, //range proof that state is in [0,1]
    #[serde_as(as = "Bytes")]
    pub signature: [u8; 64], //ed25519 signature for authenticity
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
    fn prove_dlog(secret: &Scalar, sum_c1: &RistrettoPoint, partial: &RistrettoPoint, public_key_share: &RistrettoPoint, ts: u64, id: u32) -> Self {
        let g = RISTRETTO_BASEPOINT_POINT;
        let mut r = Scalar::random(&mut OsRng);
        let commit_g = g * r;
        let commit_c = sum_c1 * r;
        let c = Self::challenge(sum_c1, partial, public_key_share, &commit_g, &commit_c, ts, id);
        let result = Self { commitment_g: commit_g.compress().into(),commitment_c: commit_c.compress().into(),response: (r + c * secret).into() };
        r.zeroize();
        result
    }
    fn verify_dlog(&self, sum_c1: &RistrettoPoint, partial: &RistrettoPoint, public_key_share: &RistrettoPoint, ts: u64, id: u32) -> bool {
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
    pub device_id: u32, //Device ID
    pub timestamp: u64, //Timestamp
    pub partial: SerCompressed, //partial decryption share
    pub proof: SchnorrProof, //proof it's computed correctly
    #[serde_as(as = "Bytes")]
    pub signature: [u8; 64], //ECC signature
}

//Main device struct - handles proof generation/verification and aggregation
pub struct IoTDevice {
    pub id: u32, //Device ID
    frost_key: frost::keys::KeyPackage, //threshold crypto key
    group_pub: frost::keys::PublicKeyPackage, //group public key
    sig_key: SigningKey, //for message authentication
    peer_keys: HashMap<u32, VerifyingKey>, //peer public keys
    valid_participant_ids: HashSet<u32>, //Valid peers
    proofs: HashMap<u32, DeviceProof>, //received proofs from peers
    partials: HashMap<u32, PartialDecryption>,  //received partial decryptions
    agg_c1: Option<RistrettoPoint>, //aggregated ciphertext c1
    agg_c2: Option<RistrettoPoint>, //aggregated ciphertext c2
    bp_gens: BulletproofGens, //bulletproof generators
    ped_gens: PedersenGens, //pedersen commitment generators
    threshold: usize, //How many devices to decrypt
    rates: HashMap<u32, (u64, u32)>, //rate limiting per peer
    last_recomp: u64, //last recomputation time
    seen_nonces: HashMap<u32, std::collections::HashSet<[u8; 32]>> //Replay protection
}
impl IoTDevice {
    pub fn new(id: u32, threshold: usize, frost_key: frost::keys::KeyPackage, group_pub: frost::keys::PublicKeyPackage, peer_keys: HashMap<u32, VerifyingKey>) -> Result<Self, AggError> {
        //Basic checks
        if id == 0 { return Err(AggError::CryptoError("Device ID cannot be zero (Lagrange requirement)".into())); }
        if threshold == 0 { return Err(AggError::CryptoError("Threshold must be at least 1".into())); }
        if !peer_keys.is_empty() {
            let total_devices = peer_keys.len() + 1; //+1 for self
            if threshold > total_devices { return Err(AggError::CryptoError( format!("Threshold {} exceeds total devices {}", threshold, total_devices) )); }
            if total_devices > MAX_DEVICES { return Err(AggError::CryptoError( format!("Too many devices: {} > {}", total_devices, MAX_DEVICES) )); }
        }
        let mut valid_participant_ids = HashSet::new();
        valid_participant_ids.insert(id);
        for peer_id in peer_keys.keys() { valid_participant_ids.insert(*peer_id); }
        //Simple initialization
        Ok(Self {
            id, threshold, frost_key, group_pub, peer_keys,
            sig_key: SigningKey::generate(&mut OsRng), valid_participant_ids,
            proofs: HashMap::new(), partials: HashMap::new(),
            agg_c1: None, agg_c2: None,
            bp_gens: BulletproofGens::new(8, 1),
            ped_gens: PedersenGens::default(),
            rates: HashMap::new(), last_recomp: 0,
            seen_nonces: HashMap::new(),
        })
    }
    
    //Generate proof for our state (0 or 1)
    pub fn generate_proof(&self, state: u8) -> Result<DeviceProof, AggError> {
        //Validate input
        if state > 1 { return Err(AggError::CryptoError("State must be 0/1".into())); }
        //Get randomness
        let ts = timestamp();
        let mut nonce = [0u8; 32];
        OsRng.fill_bytes(&mut nonce);
        let mut r = Scalar::random(&mut OsRng); //ElGamal randomness
        let g = RISTRETTO_BASEPOINT_POINT;
        let h = frost_to_point(&self.group_pub.verifying_key())?;
        //ElGamal encrypt: (c1, c2) = (g^r, g^state * h^r)
        let (c1, c2) = (g * r, g * Scalar::from(state as u64) + h * r);
        //Generate Schnorr proof linking ElGamal to Pedersen commitment
        let eg_proof = ElGamalProof::prove(state, &r, &c1, &c2, &h, self.id, ts, &nonce, &self.ped_gens);
        //Create binding factor from ElGamal ciphertext
        let mut binding_transcript = Transcript::new(b"elgamal-bulletproof-binding");
        binding_transcript.append_message(b"protocol_version", &[PROTOCOL_VERSION]);
        binding_transcript.append_message(b"c1", c1.compress().as_bytes());
        binding_transcript.append_message(b"c2", c2.compress().as_bytes());
        binding_transcript.append_message(b"device", &self.id.to_le_bytes());
        binding_transcript.append_message(b"timestamp", &ts.to_le_bytes());
        binding_transcript.append_message(b"nonce", &nonce);
        let mut binding_bytes = [0u8; 64];
        binding_transcript.challenge_bytes(b"binding_factor", &mut binding_bytes);
        let binding_factor = Scalar::from_bytes_mod_order_wide(&binding_bytes);
        //Bind bulletproof to ElGamal ciphertext
        let r_bound = r + binding_factor;
        //Generate bulletproof using bound r as blinding factor
        let mut t = Transcript::new(b"binary-range-proof");
        t.append_message(b"protocol_version", &[PROTOCOL_VERSION]);
        t.append_u64(b"device", self.id as u64);
        t.append_u64(b"timestamp", ts);
        t.append_message(b"nonce", &nonce);
        t.append_message(b"c1", c1.compress().as_bytes());
        t.append_message(b"c2", c2.compress().as_bytes());
        t.append_message(b"commitment", eg_proof.state_commit.0.as_bytes());
        //Generate bulletproof
        let (bp, _) = RangeProof::prove_single(&self.bp_gens, &self.ped_gens, &mut t, state as u64, &r_bound, 8).map_err(|e| { r.zeroize(); AggError::CryptoError(format!("BP failed: {:?}", e)) })?;
        r.zeroize(); //clean up secret
        //Return proof
        Ok(DeviceProof {
            device_id: self.id, timestamp: ts, nonce,
            elgamal_c1: c1.compress().into(), elgamal_c2: c2.compress().into(),
            elgamal_proof: eg_proof.clone(), bulletproof: bp.to_bytes(),
            signature: { let mut sig_data = Vec::new();sig_data.extend_from_slice(&ts.to_le_bytes());sig_data.extend_from_slice(&self.id.to_le_bytes());sig_data.extend_from_slice(&nonce);sig_data.extend_from_slice(c1.compress().as_bytes());sig_data.extend_from_slice(c2.compress().as_bytes());sig_data.extend_from_slice(eg_proof.state_commit.0.as_bytes());sig_data.extend_from_slice(eg_proof.commit_r.0.as_bytes());sig_data.extend_from_slice(eg_proof.commit_s.0.as_bytes());sig_data.extend_from_slice(eg_proof.commit_c.0.as_bytes());sig_data.extend_from_slice(&eg_proof.resp_r.0.to_bytes());sig_data.extend_from_slice(&eg_proof.resp_state.0.to_bytes());sig_data.extend_from_slice(&bp.to_bytes()); self.sig_key.sign(&sig_data).to_bytes() },
        })
    }

    //Receive and verify a proof from a peer
    pub fn receive_proof(&mut self, p: DeviceProof) -> Result<(), AggError> {
        //Start with basic checks
        if self.proofs.len() >= MAX_STORED_PROOFS {
            self.cleanup();
            if self.proofs.len() >= MAX_STORED_PROOFS { return Err(AggError::RateLimited); }
        }
        self.check_rate(p.device_id)?;
        let now = timestamp();
        let adjusted_now = now + MAX_CLOCK_SKEW;
        if p.timestamp > adjusted_now { return Err(AggError::InvalidProof("Timestamp too far in future".into())); }
        if p.timestamp + PROOF_EXPIRY < now.saturating_sub(MAX_CLOCK_SKEW) { return Err(AggError::ExpiredProof); }
        let device_nonces = self.seen_nonces.entry(p.device_id).or_insert_with(HashSet::new);
        if device_nonces.len() >= MAX_NONCES_PER_DEVICE { return Err(AggError::RateLimited); }
        if !device_nonces.insert(p.nonce) { return Err(AggError::InvalidProof("Nonce already used".into())); }
        if self.proofs.contains_key(&p.device_id) { return Err(AggError::InvalidProof("Duplicate".into())); }
        if p.bulletproof.len() > MAX_PROOF_SIZE { return Err(AggError::InvalidProof("Too big".into())); }
        //Verify signature
        let pk = self.peer_keys.get(&p.device_id).ok_or(AggError::InvalidProof("Unknown device".into()))?;
        {
            let mut sig_data = Vec::new();sig_data.extend_from_slice(&p.timestamp.to_le_bytes());sig_data.extend_from_slice(&p.device_id.to_le_bytes());sig_data.extend_from_slice(&p.nonce);sig_data.extend_from_slice(p.elgamal_c1.0.as_bytes());sig_data.extend_from_slice(p.elgamal_c2.0.as_bytes());sig_data.extend_from_slice(p.elgamal_proof.state_commit.0.as_bytes());sig_data.extend_from_slice(p.elgamal_proof.commit_r.0.as_bytes());sig_data.extend_from_slice(p.elgamal_proof.commit_s.0.as_bytes());sig_data.extend_from_slice(p.elgamal_proof.commit_c.0.as_bytes());sig_data.extend_from_slice(&p.elgamal_proof.resp_r.0.to_bytes());sig_data.extend_from_slice(&p.elgamal_proof.resp_state.0.to_bytes());sig_data.extend_from_slice(&p.bulletproof);
            let sig = Signature::try_from(&p.signature[..]).map_err(|_| AggError::InvalidProof("bad sig".into()))?;
            pk.verify(&sig_data, &sig).map_err(|_| AggError::InvalidProof("sig verify failed".into()))?;
        }
        //Verify ElGamal correctness proof
        let c1 = p.elgamal_c1.0.decompress().ok_or(AggError::InvalidProof("bad c1".into()))?;
        let c2 = p.elgamal_c2.0.decompress().ok_or(AggError::InvalidProof("bad c2".into()))?;
        let h = frost_to_point(&self.group_pub.verifying_key())?;
        if !p.elgamal_proof.verify(&c1, &c2, &h, p.device_id, p.timestamp, &p.nonce, &self.ped_gens) { return Err(AggError::InvalidProof("Schnorr failed".into())); }
        //Verify bulletproof with binding
        let sc = p.elgamal_proof.state_commit.0.decompress().ok_or(AggError::InvalidProof("bad commitment".into()))?;
        //Reconstruct binding factor (same as in generate_proof)
        let mut binding_transcript = Transcript::new(b"elgamal-bulletproof-binding");
        binding_transcript.append_message(b"protocol_version", &[PROTOCOL_VERSION]);
        binding_transcript.append_message(b"c1", p.elgamal_c1.0.as_bytes());
        binding_transcript.append_message(b"c2", p.elgamal_c2.0.as_bytes());
        binding_transcript.append_message(b"device", &p.device_id.to_le_bytes());
        binding_transcript.append_message(b"timestamp", &p.timestamp.to_le_bytes());
        binding_transcript.append_message(b"nonce", &p.nonce);
        let mut binding_bytes = [0u8; 64];
        binding_transcript.challenge_bytes(b"binding_factor", &mut binding_bytes);
        let binding_factor = Scalar::from_bytes_mod_order_wide(&binding_bytes);
        //Compute expected commitment with binding
        let binding_commit = self.ped_gens.commit(Scalar::zero(), binding_factor);
        let expected_commit = sc + binding_commit;
        let mut t = Transcript::new(b"binary-range-proof");
        t.append_message(b"protocol_version", &[PROTOCOL_VERSION]);
        t.append_u64(b"device", p.device_id as u64);
        t.append_u64(b"timestamp", p.timestamp);
        t.append_message(b"nonce", &p.nonce);
        t.append_message(b"c1", p.elgamal_c1.0.as_bytes());
        t.append_message(b"c2", p.elgamal_c2.0.as_bytes());
        t.append_message(b"commitment", p.elgamal_proof.state_commit.0.as_bytes());
        //Verify bulletproof
        RangeProof::from_bytes(&p.bulletproof).map_err(|_| AggError::InvalidProof("bad BP".into()))?.verify_single(&self.bp_gens, &self.ped_gens, &mut t, &expected_commit.compress(), 8).map_err(|_| AggError::InvalidProof("BP verify failed".into()))?;
        //Insert proof and maybe recompute aggregate
        self.proofs.insert(p.device_id, p);
        self.maybe_recompute();
        Ok(())
    }
    
    //Generate our partial decryption share
    pub fn generate_partial_decryption(&mut self) -> Result<PartialDecryption, AggError> {
        self.recompute(); //Force recompute
        let sum_c1 = self.agg_c1.ok_or(AggError::CryptoError("No agg".into()))?; //Get sum of c1
        let ts = timestamp(); //Get timestamp
        let mut sec = frost_to_scalar(&self.frost_key.signing_share())?; //Convert secret key to scalar
        let partial = sum_c1 * sec;  //partial decryption
        let frost_id = frost::Identifier::try_from(self.id as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
        let public_key_share = self.group_pub.verifying_shares().get(&frost_id).ok_or(AggError::CryptoError("Unknown participant".into()))?;
        let public_key_share_point = frost_share_to_point(public_key_share)?;
        let proof = SchnorrProof::prove_dlog(&sec, &sum_c1, &partial, &public_key_share_point, ts, self.id);
        sec.zeroize();
        //Return partial decryption
        Ok(PartialDecryption {
            device_id: self.id, timestamp: ts,
            partial: partial.compress().into(), proof,
            signature: self.sign(&[&ts.to_le_bytes(), &self.id.to_le_bytes(), partial.compress().as_bytes()]),
        })
    }
    
    //Receive partial decryption from peer
    pub fn receive_partial(&mut self, p: PartialDecryption) -> Result<(), AggError> {
        //Basic checks
        if self.partials.len() >= MAX_STORED_PARTIALS {
            self.cleanup();
            if self.partials.len() >= MAX_STORED_PARTIALS { return Err(AggError::RateLimited); }
        }
        self.check_rate(p.device_id)?;
        let now = timestamp();
        let adjusted_now = now + MAX_CLOCK_SKEW;
        if p.timestamp > adjusted_now { return Err(AggError::InvalidProof("Timestamp too far in future".into())); }
        if p.timestamp + PROOF_EXPIRY < now.saturating_sub(MAX_CLOCK_SKEW) { return Err(AggError::ExpiredProof); }
        let pk = self.peer_keys.get(&p.device_id).ok_or(AggError::InvalidProof("Unknown".into()))?;
        //Verify signature and recompute
        self.verify_sig(pk, &[&p.timestamp.to_le_bytes(), &p.device_id.to_le_bytes(), p.partial.0.as_bytes()], &p.signature)?;
        self.recompute();
        //Verify Schnorr
        let sum_c1 = self.agg_c1.ok_or(AggError::CryptoError("No aggregation computed yet".into()))?;
        let pt = p.partial.0.decompress().ok_or(AggError::CryptoError("Invalid partial point".into()))?;
        let frost_id = frost::Identifier::try_from(p.device_id as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
        let public_key_share = self.group_pub.verifying_shares().get(&frost_id).ok_or(AggError::CryptoError("Unknown participant".into()))?;
        let public_key_share_point = frost_share_to_point(public_key_share)?;
        if !p.proof.verify_dlog(&sum_c1, &pt, &public_key_share_point, p.timestamp, p.device_id) { return Err(AggError::InvalidProof("Schnorr proof verification failed".into())); }
        self.partials.insert(p.device_id, p); //Add to aggregate
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
        let expired_devices: HashSet<u32> = self.proofs.iter().filter(|(_, p)| p.timestamp <= cutoff).map(|(id, _)| *id).collect();
        self.proofs.retain(|_, p| p.timestamp > cutoff);
        self.partials.retain(|_, p| p.timestamp > cutoff);
        for device_id in expired_devices { self.seen_nonces.remove(&device_id); }
        self.maybe_recompute();
    }
    
    //Compute final aggregate using threshold decryption
    pub fn compute_aggregate(&mut self) -> Result<(usize, usize), AggError> {
        self.recompute();
        //Make sure threshold is met and we are up to date
        let valid = self.proofs.len();
        if valid == 0 { return Ok((0, 0)); }
        if self.partials.len() < self.threshold { return Err(AggError::ThresholdNotMet); }
        //Start sums
        let sum_c1 = self.agg_c1.ok_or(AggError::CryptoError("No agg".into()))?;
        let sum_c2 = self.agg_c2.ok_or(AggError::CryptoError("No agg".into()))?;
        //Verify partials and collect valid ones
        let mut verified = Vec::new();
        for p in self.partials.values().take(self.threshold) {
            let pt = p.partial.0.decompress().ok_or(AggError::CryptoError("bad partial".into()))?;
            let frost_id = frost::Identifier::try_from(p.device_id as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
            let public_key_share = self.group_pub.verifying_shares().get(&frost_id).ok_or(AggError::CryptoError("Unknown participant".into()))?;
            let public_key_share_point = frost_share_to_point(public_key_share)?;
            if !p.proof.verify_dlog(&sum_c1, &pt, &public_key_share_point, p.timestamp, p.device_id) { return Err(AggError::InvalidProof(format!("Failed for {}", p.device_id))); }
            verified.push((p.device_id, pt));
        }
        //Check valid DKG participants
        for (id, _) in &verified { if !self.valid_participant_ids.contains(id) { return Err(AggError::InvalidProof( format!("Device {} is not a valid DKG participant", id) )); } }
        //Ensure no zero IDs
        if verified.iter().any(|(id, _)| *id == 0) { return Err(AggError::CryptoError("Device ID cannot be zero".into())); }
        //Check all IDs are unique
        let mut seen = std::collections::HashSet::new();
        for (id, _) in &verified { if !seen.insert(id) { return Err(AggError::CryptoError("Duplicate device ID in partials".into())); } }
        //Check we have exactly threshold participants
        if verified.len() != self.threshold { return Err(AggError::CryptoError( format!("Expected {} partials, got {}", self.threshold, verified.len()) )); }
        //Lagrange interpolation to combine shares
        let ids: Vec<Scalar> = verified.iter().map(|(id, _)| Scalar::from(*id as u64)).collect();
        let mut combined = RistrettoPoint::identity();
        for i in 0..verified.len() {
            let mut lambda = Scalar::one();
            for j in 0..verified.len() {
                if i != j {
                    let diff = ids[i] - ids[j];
                    if diff == Scalar::zero() { return Err(AggError::CryptoError("Cannot compute Lagrange with duplicate IDs".into())); }
                    let inv = diff.invert();
                    lambda *= -ids[j] * inv;
                }
            }
            combined += verified[i].1 * lambda;
        }
        //Decrypt: sum_c2 - combined gives g^sum, then solve dlog
        Ok((bsgs_dlog(sum_c2 - combined, RISTRETTO_BASEPOINT_POINT)?, valid))
    }
    
    //Recompute aggregate ciphertexts
    fn recompute(&mut self) {
        if self.proofs.is_empty() { self.agg_c1 = None; self.agg_c2 = None;
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
        //Global rate limit
        let total_msgs: u32 = self.rates.values().filter(|(ts, _)| now < ts.saturating_add(RATE_WINDOW)).map(|(_, count)| count).sum(); //DDoS
        if total_msgs >= MAX_TOTAL_RATE { return Err(AggError::RateLimited); }
        //Per-device rate limit
        let e = self.rates.entry(id).or_insert((now, 0));
        //Reset window if expired
        if now >= e.0.saturating_add(RATE_WINDOW) { *e = (now, 0); }
        if e.1 >= MAX_MSGS_PER_WINDOW { return Err(AggError::RateLimited); }
        e.1 = e.1.saturating_add(1);
        //Cleanup
        if self.rates.len() > 1000 {
            let cutoff = now.saturating_sub(RATE_WINDOW * 2);
            self.rates.retain(|_, (ts, _)| *ts > cutoff);
        }
        Ok(())
    }
    
    //Sign with signature
    fn sign(&self, parts: &[&[u8]]) -> [u8; 64] {
        let mut d = Vec::new();
        for p in parts { d.extend_from_slice(p); }
        self.sig_key.sign(&d).to_bytes()
    }
    
    //Verify signature
    fn verify_sig(&self, k: &VerifyingKey, parts: &[&[u8]], sig: &[u8; 64]) -> Result<(), AggError> {
        let mut d = Vec::new();
        for p in parts { d.extend_from_slice(p); }
        let s = Signature::try_from(&sig[..]).map_err(|_| AggError::InvalidProof("bad sig".into()))?;
        k.verify(&d, &s).map_err(|_| AggError::InvalidProof("sig verify failed".into()))
    }
}

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
    } else { Err(AggError::CryptoError("dlog not found".into())) }
}

//FROST DKG setup - generates threshold keys for all participants
pub fn setup_dkg(n: usize, t: usize) -> Result<Vec<(u32, frost::keys::KeyPackage, frost::keys::PublicKeyPackage)>, AggError> {
    let mut rng = OsRng;
    let mut r1_pkgs = BTreeMap::new();
    let mut r1_secs = HashMap::new();
    //Round 1: everyone generates commitments
    for i in 1..=n {
        let id = frost::Identifier::try_from(i as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
        let (sec, pkg) = frost::keys::dkg::part1(id, n as u16, t as u16, &mut rng).map_err(|e| AggError::CryptoError(e.to_string()))?;
        r1_secs.insert(i as u32, sec);
        r1_pkgs.insert(id, pkg);
    }
    //Round 2: exchange shares
    let mut r2_pkgs = HashMap::new();
    for (i, sec) in &r1_secs {
        let mut rcvd = r1_pkgs.clone();
        let id = frost::Identifier::try_from(*i as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
        rcvd.remove(&id);
        let (r2_sec, pkgs) = frost::keys::dkg::part2(sec.clone(), &rcvd).map_err(|e| AggError::CryptoError(e.to_string()))?;
        r2_pkgs.insert(*i, (r2_sec, pkgs));
    }
    //Round 3: finalize keys
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

//Helper functions
fn timestamp() -> u64 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).expect("System clock is before Unix epoch") .as_secs()
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

//Main test
fn main() -> Result<(), AggError> {
    let (n, t, states) = (5, 3, [1u8, 0, 1, 1, 0]);
    let dkg = setup_dkg(n, t)?;
    let mut devs = Vec::new();
    let mut all_keys = HashMap::new();
    for (id, kpkg, ppkg) in &dkg {
        let d = IoTDevice::new(*id, t, kpkg.clone(), ppkg.clone(), HashMap::new())?;
        all_keys.insert(*id, d.sig_key.verifying_key());
        devs.push(d);
    }
    for d in devs.iter_mut() {
        d.peer_keys = all_keys.clone();
        d.valid_participant_ids.clear();
        d.valid_participant_ids.insert(d.id);
        for peer_id in d.peer_keys.keys() {
            d.valid_participant_ids.insert(*peer_id);
        }
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