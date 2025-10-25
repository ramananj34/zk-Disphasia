use serde::{Deserialize, Serialize};
use serde_with::{serde_as, Bytes};
use curve25519_dalek_ng::{ristretto::*, scalar::Scalar, traits::Identity, constants::RISTRETTO_BASEPOINT_POINT};
use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
use merlin::Transcript;
use frost_ristretto255 as frost;
use ed25519_dalek::{SigningKey, VerifyingKey, Signature, Signer, Verifier};
use zeroize::Zeroize;
use rand::rngs::OsRng;
use rand::RngCore;
use std::collections::{HashMap, HashSet};

use crate::common::{SerCompressed, SerScalar, AggError, VerifiedCiphertext, VerifiedPartial, PartialDecryption, PROTOCOL_VERSION, MAX_DEVICES, MAX_STORED_PROOFS, MAX_CLOCK_SKEW,MAX_NONCES_PER_DEVICE, PROOF_EXPIRY, timestamp, frost_to_point, check_rate};

pub const MAX_PROOF_SIZE: usize = 8192;

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

//Main device struct - handles proof generation/verification and aggregation
pub struct IoTDevice {
    pub id: u32, //Device ID
    pub frost_key: frost::keys::KeyPackage, //threshold crypto key
    pub group_pub: frost::keys::PublicKeyPackage, //group public key
    pub sig_key: SigningKey, //for message authentication
    pub peer_keys: HashMap<u32, VerifyingKey>, //peer public keys
    pub valid_participant_ids: HashSet<u32>, //Valid peers
    pub verified_ciphertexts: HashMap<u32, VerifiedCiphertext>, //received proofs from peers
    partials: HashMap<u32, VerifiedPartial>,  //received partial decryptions
    agg_c1: Option<RistrettoPoint>, //aggregated ciphertext c1
    agg_c2: Option<RistrettoPoint>, //aggregated ciphertext c2
    bp_gens: BulletproofGens, //bulletproof generators
    ped_gens: PedersenGens, //pedersen commitment generators
    threshold: usize, //How many devices to decrypt
    rates: HashMap<u32, (u64, u32)>, //rate limiting per peer
    seen_nonces: HashMap<u32, std::collections::HashSet<[u8; 32]>> //Replay protection
}
impl IoTDevice {
    pub fn new(id: u32, threshold: usize, frost_key: frost::keys::KeyPackage, group_pub: frost::keys::PublicKeyPackage, peer_keys: HashMap<u32, VerifyingKey>, signing_key: Option<SigningKey>) -> Result<Self, AggError> {
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
        let sig_key = signing_key.unwrap_or_else(|| SigningKey::generate(&mut OsRng));
        //Simple initialization
        Ok(Self {
            id, threshold, frost_key, group_pub, peer_keys,
            sig_key, valid_participant_ids,
            verified_ciphertexts: HashMap::new(), partials: HashMap::new(),
            agg_c1: None, agg_c2: None,
            bp_gens: BulletproofGens::new(8, 1),
            ped_gens: PedersenGens::default(),
            rates: HashMap::new(),
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
        if self.verified_ciphertexts.len() >= MAX_STORED_PROOFS {
            self.cleanup();
            if self.verified_ciphertexts.len() >= MAX_STORED_PROOFS { return Err(AggError::RateLimited); }
        }
        check_rate(p.device_id, &mut self.rates)?;
        let now = timestamp();
        let adjusted_now = now + MAX_CLOCK_SKEW;
        if p.timestamp > adjusted_now { return Err(AggError::InvalidProof("Timestamp too far in future".into())); }
        if p.timestamp + PROOF_EXPIRY < now.saturating_sub(MAX_CLOCK_SKEW) { return Err(AggError::ExpiredProof); }
        let device_nonces = self.seen_nonces.entry(p.device_id).or_insert_with(HashSet::new);
        if device_nonces.len() >= MAX_NONCES_PER_DEVICE { return Err(AggError::RateLimited); }
        if !device_nonces.insert(p.nonce) { return Err(AggError::InvalidProof("Nonce already used".into())); }
        if self.verified_ciphertexts.contains_key(&p.device_id) { return Err(AggError::InvalidProof("Duplicate".into())); }
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
        self.verified_ciphertexts.insert(p.device_id, VerifiedCiphertext {timestamp: p.timestamp,c1,c2,});
        Ok(())
    }

    fn cleanup(&mut self) {
        let now = timestamp();
        let cutoff = now.saturating_sub(PROOF_EXPIRY * 2);
        self.verified_ciphertexts.retain(|_, vc| vc.timestamp > cutoff);
        self.seen_nonces.retain(|_, nonces| !nonces.is_empty());
    }

    fn recompute(&mut self) {
        if self.verified_ciphertexts.is_empty() {
            self.agg_c1 = None;
            self.agg_c2 = None;
        } else {
            let (mut c1, mut c2) = (RistrettoPoint::identity(), RistrettoPoint::identity());
            for vc in self.verified_ciphertexts.values() {
                c1 += vc.c1;
                c2 += vc.c2;
            }
            self.agg_c1 = Some(c1);
            self.agg_c2 = Some(c2);
        }
    }

    pub fn generate_partial_decryption(&mut self) -> Result<PartialDecryption, AggError> {
        self.recompute();
        let verified_vec: Vec<VerifiedCiphertext> = self.verified_ciphertexts.values().cloned().collect();
        let partial = crate::common::generate_partial_decryption(self.id,&self.frost_key,&self.group_pub,&self.sig_key,&verified_vec)?;
        Ok(partial)
    }
    pub fn receive_partial(&mut self, partial: PartialDecryption) -> Result<(), AggError> {
        let verified_vec: Vec<VerifiedCiphertext> = self.verified_ciphertexts.values().cloned().collect();
        let mut verified_partials_vec: Vec<VerifiedPartial> = self.partials.values().cloned().collect();
        let verified = crate::common::receive_partial(partial,&self.peer_keys,&self.group_pub,&verified_vec,&mut verified_partials_vec,&mut self.rates,)?;
        self.partials.insert(verified.device_id, verified);
        Ok(())
    }
    pub fn compute_aggregate(&mut self) -> Result<(usize, usize), AggError> {
        self.recompute();
        if self.partials.len() < self.threshold { return Err(AggError::ThresholdNotMet); }
        let verified_vec: Vec<VerifiedCiphertext> = self.verified_ciphertexts.values().cloned().collect();
        let verified_partials_vec: Vec<VerifiedPartial> = self.partials.values().cloned().collect();
        crate::common::compute_aggregate(self.threshold,&verified_vec,&verified_partials_vec)
    }
}