use serde::{Deserialize, Serialize}; //Serialize/deserialize
use serde_with::{serde_as, Bytes};//Serialize/deserialize
use curve25519_dalek_ng::{ristretto::*, scalar::Scalar, traits::Identity, constants::RISTRETTO_BASEPOINT_POINT}; //My curve
use winterfell::{Air, AirContext, Assertion, EvaluationFrame, ProofOptions, Prover, Proof,TraceInfo, TransitionConstraintDegree,crypto::{hashers::Blake3_256, DefaultRandomCoin, MerkleTree},math::{fields::f128::BaseElement, FieldElement, ToElements, StarkField},matrix::ColMatrix, TraceTable, verify, AcceptableOptions,ConstraintCompositionCoefficients, DefaultConstraintEvaluator, DefaultTraceLde,PartitionOptions, StarkDomain, TracePolyTable, AuxRandElements}; //Winterfell
use winter_utils::Serializable; //Winterfell
use merlin::Transcript; //Transcript
use frost_ristretto255 as frost; //FROST
use ed25519_dalek::{SigningKey, VerifyingKey, Signature, Signer, Verifier}; //Digital signatures
use zeroize::Zeroize; //Safe data deletion
use rand::rngs::OsRng; //Random
use rand::RngCore; //Random
use std::collections::{HashMap, HashSet}; //Data structures

use crate::common::{SerCompressed, SerScalar, AggError, VerifiedCiphertext, VerifiedPartial, PartialDecryption, PROTOCOL_VERSION, MAX_DEVICES, MAX_STORED_PROOFS, MAX_CLOCK_SKEW,MAX_NONCES_PER_DEVICE, PROOF_EXPIRY, timestamp, frost_to_point, check_rate};

const MAX_PROOF_SIZE: usize = 65536; //prevent DoS attacks


//STARK AIR definition - enforces binary constraint
#[derive(Clone, Debug)]
pub struct BinaryPublicInputs {
    state_commitment: BaseElement, //Public state
    nonce_public: BaseElement, //Public nonce
    pedersen_public: BaseElement, //Public pedersen
}
//Convert to linear array for STARK framework
impl ToElements<BaseElement> for BinaryPublicInputs { fn to_elements(&self) -> Vec<BaseElement> { vec![self.state_commitment, self.nonce_public, self.pedersen_public] } }
//AIR Algebraic Intermediate Representation. This defines the constraint that state * (state - 1) = 0
#[allow(dead_code)]
#[derive(Clone)]
pub struct BinaryAir {
    context: AirContext<BaseElement>,
    state_commitment: BaseElement,
    nonce_public: BaseElement,
    pedersen_public: BaseElement,
}
impl Air for BinaryAir {
    type BaseField = BaseElement;
    type PublicInputs = BinaryPublicInputs;
    type GkrProof = ();
    type GkrVerifier = ();
    fn new(trace_info: TraceInfo, pub_inputs: Self::PublicInputs, opts: ProofOptions) -> Self {
        assert_eq!(4, trace_info.width());
        //Binary and Hash Constraint
        let degrees = vec![ TransitionConstraintDegree::new(2), TransitionConstraintDegree::new(5)];
        Self {
            context: AirContext::new(trace_info, degrees, 3, opts),
            state_commitment: pub_inputs.state_commitment,
            nonce_public: pub_inputs.nonce_public,
            pedersen_public: pub_inputs.pedersen_public,
        }
    }
    fn context(&self) -> &AirContext<Self::BaseField> { &self.context }
    fn evaluate_transition<E: FieldElement + From<Self::BaseField>>( &self, frame: &EvaluationFrame<E>, _: &[E], result: &mut [E] ) {
        let current = frame.current();
        let state = current[0];
        let nonce = current[1];
        let pedersen = current[2];
        let hash_val = current[3];
        //Constraint 1: Binary constraint
        result[0] = state * (state - E::ONE);
        //Constraint 2: Hash constraint
        let state_sq = state * state;
        let state_5 = state_sq * state_sq * state;
        let nonce_sq = nonce * nonce;
        let nonce_5 = nonce_sq * nonce_sq * nonce;
        let pedersen_sq = pedersen * pedersen;
        let pedersen_5 = pedersen_sq * pedersen_sq * pedersen;
        let expected_hash = state_5 + nonce_5 + pedersen_5 + (state * nonce) + (state * pedersen);
        result[1] = hash_val - expected_hash;
    }
    fn get_assertions(&self) -> Vec<Assertion<Self::BaseField>> {
        vec![Assertion::single(3, 63, self.state_commitment),Assertion::single(1, 63, self.nonce_public),Assertion::single(2, 63, self.pedersen_public)]
    }
}
//STARK prover implementation
#[derive(Clone)]
pub struct BinaryProver {
    pub options: ProofOptions,
    last_state: std::cell::Cell<Option<BaseElement>>,
    last_nonce: std::cell::Cell<Option<BaseElement>>,
    last_pedersen: std::cell::Cell<Option<BaseElement>>,
    last_commitment: std::cell::Cell<Option<BaseElement>>,
}
impl BinaryProver {
    pub fn new() -> Self {
        Self {
            options: ProofOptions::new(40,16,20,winterfell::FieldExtension::None,8,63),
            last_state: std::cell::Cell::new(None),
            last_nonce: std::cell::Cell::new(None),
            last_pedersen: std::cell::Cell::new(None),
            last_commitment: std::cell::Cell::new(None),
        }
    }
    pub fn build_trace(&self, state: u8, nonce: BaseElement, pedersen: BaseElement) -> TraceTable<BaseElement> {
        let state_elem = BaseElement::new(state as u128);
        //Compute hash
        let state_sq = state_elem * state_elem;
        let state_5 = state_sq * state_sq * state_elem;
        let nonce_sq = nonce * nonce;
        let nonce_5 = nonce_sq * nonce_sq * nonce;
        let pedersen_sq = pedersen * pedersen;
        let pedersen_5 = pedersen_sq * pedersen_sq * pedersen;
        let hash = state_5 + nonce_5 + pedersen_5 + (state_elem * nonce) + (state_elem * pedersen);
        //Store result
        self.last_state.set(Some(state_elem));
        self.last_nonce.set(Some(nonce));
        self.last_pedersen.set(Some(pedersen));
        self.last_commitment.set(Some(hash));
        //Trace length
        let len = 64;
        let mut trace = TraceTable::new(4, len);
        //Trace
        trace.fill(
            |s| {s[0] = BaseElement::ZERO;s[1] = BaseElement::ZERO;s[2] = BaseElement::ZERO;s[3] = BaseElement::ZERO;},
            |step, s| {if step == 0 {s[0] = state_elem;s[1] = nonce;s[2] = pedersen;s[3] = hash;} else {s[0] = state_elem;s[1] = nonce;s[2] = pedersen;s[3] = hash;}}
        );
        trace
    }
}
//Prover biolerplate
impl Prover for BinaryProver {
    type BaseField = BaseElement;
    type Air = BinaryAir;
    type Trace = TraceTable<BaseElement>;
    type HashFn = Blake3_256<BaseElement>;
    type RandomCoin = DefaultRandomCoin<Self::HashFn>;
    type VC = MerkleTree<Self::HashFn>;
    type TraceLde<E: FieldElement<BaseField = Self::BaseField>> = DefaultTraceLde<E, Self::HashFn, Self::VC>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = Self::BaseField>> = DefaultConstraintEvaluator<'a, Self::Air, E>;
    fn get_pub_inputs(&self, _: &Self::Trace) -> BinaryPublicInputs {
        BinaryPublicInputs {
            state_commitment: self.last_commitment.get().unwrap(),
            nonce_public: self.last_nonce.get().unwrap(),
            pedersen_public: self.last_pedersen.get().unwrap(),
        }
    }
    fn options(&self) -> &ProofOptions { &self.options }
    fn new_trace_lde<E: FieldElement<BaseField = Self::BaseField>>(&self, info: &TraceInfo, main: &ColMatrix<Self::BaseField>, domain: &StarkDomain<Self::BaseField>, part: PartitionOptions) -> (Self::TraceLde<E>, TracePolyTable<E>) {
        DefaultTraceLde::new(info, main, domain, part)
    }
    fn new_evaluator<'a, E: FieldElement<BaseField = Self::BaseField>>(&self, air: &'a Self::Air, aux: Option<AuxRandElements<E>>,coeffs: ConstraintCompositionCoefficients<E>) -> Self::ConstraintEvaluator<'a, E> {
        DefaultConstraintEvaluator::new(air, aux, coeffs)
    }
}

//ElGamal correctness proof
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ElGamalProof {
    pub commit_r: SerCompressed, //Random witness var
    pub commit_s: SerCompressed, //Random witness var
    pub commit_p: SerCompressed, //Random witness var
    pub resp_r: SerScalar, //Fiat Shamir Response
    pub resp_state: SerScalar, //Fiat Shamir Response
    pub pedersen_commit: SerCompressed, //Fiat Shamir Response
    pub nonce_bytes: [u8; 32], //Replay salt
}
impl ElGamalProof {
    pub fn prove(state: u8, r: &Scalar, c1: &RistrettoPoint, c2: &RistrettoPoint, h: &RistrettoPoint, dev_id: u32, ts: u64) -> Self {
        //Setup
        let g = RISTRETTO_BASEPOINT_POINT;
        let state_scalar = Scalar::from(state as u64);
        let pedersen_commit = g * state_scalar + h * r;
        //Get randomness
        let mut nonce_bytes = [0u8; 32];
        OsRng.fill_bytes(&mut nonce_bytes);
        let mut w = Scalar::random(&mut OsRng);
        let mut v = Scalar::random(&mut OsRng);
        //Compute commitments
        let cr = g * w;
        let cs = g * v + h * w;
        let cp = g * v + h * w;
        //Build transcript
        let mut t = Transcript::new(b"elgamal-pedersen");
        t.append_message(b"protocol_version", &[PROTOCOL_VERSION]);
        t.append_u64(b"device", dev_id as u64);
        t.append_u64(b"timestamp", ts);
        t.append_message(b"nonce", &nonce_bytes);
        t.append_message(b"c1", c1.compress().as_bytes());
        t.append_message(b"c2", c2.compress().as_bytes());
        t.append_message(b"pedersen", pedersen_commit.compress().as_bytes());
        t.append_message(b"R", cr.compress().as_bytes());
        t.append_message(b"S", cs.compress().as_bytes());
        t.append_message(b"P", cp.compress().as_bytes());
        //Derive challange
        let mut cb = [0u8; 64];
        t.challenge_bytes(b"challenge", &mut cb);
        let c = Scalar::from_bytes_mod_order_wide(&cb);
        //Compute response
        let result = Self {
            commit_r: cr.compress().into(),
            commit_s: cs.compress().into(),
            commit_p: cp.compress().into(),
            resp_r: (w + c * r).into(),
            resp_state: (v + c * state_scalar).into(),
            pedersen_commit: pedersen_commit.compress().into(),
            nonce_bytes,
        };
        //Zeroize secrets
        w.zeroize();
        v.zeroize();
        result
    }

    pub fn verify(&self, c1: &RistrettoPoint, c2: &RistrettoPoint, h: &RistrettoPoint, dev_id: u32, ts: u64) -> bool {
        //Decompress
        let g = RISTRETTO_BASEPOINT_POINT;
        let (Some(cr), Some(cs), Some(cp), Some(pc)) = (self.commit_r.0.decompress(), self.commit_s.0.decompress(),self.commit_p.0.decompress(),self.pedersen_commit.0.decompress()) else { return false };
        //Rebuild transcript
        let mut t = Transcript::new(b"elgamal-pedersen");
        t.append_message(b"protocol_version", &[PROTOCOL_VERSION]);
        t.append_u64(b"device", dev_id as u64);
        t.append_u64(b"timestamp", ts);
        t.append_message(b"nonce", &self.nonce_bytes);
        t.append_message(b"c1", c1.compress().as_bytes());
        t.append_message(b"c2", c2.compress().as_bytes());
        t.append_message(b"pedersen", self.pedersen_commit.0.as_bytes());
        t.append_message(b"R", self.commit_r.0.as_bytes());
        t.append_message(b"S", self.commit_s.0.as_bytes());
        t.append_message(b"P", self.commit_p.0.as_bytes());
        //Derive challange
        let mut cb = [0u8; 64];
        t.challenge_bytes(b"challenge", &mut cb);
        let c = Scalar::from_bytes_mod_order_wide(&cb);
        //Perform checks
        let chk1 = g * self.resp_r.0 == cr + c1 * c;
        let chk2 = g * self.resp_state.0 + h * self.resp_r.0 == cs + c2 * c;
        let chk3 = g * self.resp_state.0 + h * self.resp_r.0 == cp + pc * c;
        chk1 && chk2 && chk3
    }

    pub fn compute_stark_commitment(state: u8, nonce: &[u8; 32], pedersen: &CompressedRistretto) -> BaseElement {
        //Inputs to field elements
        let state_elem = BaseElement::new(state as u128);
        let nonce_elem = bytes_to_base_element(nonce);
        let pedersen_elem = bytes_to_base_element(pedersen.as_bytes());
        //Compute non-linear hashes, then raises to the fifth power for entropy, a pseudo-hash in the finite field
        let s_sq = state_elem * state_elem;
        let s_5 = s_sq * s_sq * state_elem;
        let n_sq = nonce_elem * nonce_elem;
        let n_5 = n_sq * n_sq * nonce_elem;
        let p_sq = pedersen_elem * pedersen_elem;
        let p_5 = p_sq * p_sq * pedersen_elem;
        //Mix everything together
        s_5 + n_5 + p_5 + (state_elem * nonce_elem) + (state_elem * pedersen_elem)
    }
}

//Device proof with STARK
#[serde_as]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceProof {
    pub device_id: u32, //Device ID
    pub timestamp: u64, //Timestamp
    pub elgamal_c1: SerCompressed, //ElGamal
    pub elgamal_c2: SerCompressed, //ElGamal
    pub elgamal_proof: ElGamalProof, //ElGamal
    pub stark_commitment: Vec<u8>, //Stark
    pub stark_proof: Vec<u8>, //Stark
    #[serde_as(as = "Bytes")]
    pub signature: [u8; 64], //Signature
}

//Main device struct - handles proof generation/verification and aggregation
pub struct IoTDevice {
    pub id: u32,
    pub frost_key: frost::keys::KeyPackage,
    pub group_pub: frost::keys::PublicKeyPackage,
    pub sig_key: SigningKey,
    pub peer_keys: HashMap<u32, VerifyingKey>,
    pub valid_participant_ids: HashSet<u32>,
    pub verified_ciphertexts: HashMap<u32, VerifiedCiphertext>,
    partials: HashMap<u32, VerifiedPartial>,
    agg_c1: Option<RistrettoPoint>,
    agg_c2: Option<RistrettoPoint>,
    stark_prover: BinaryProver,
    threshold: usize,
    rates: HashMap<u32, (u64, u32)>,
    seen_nonces: HashMap<u32, HashSet<[u8; 32]>>,
}

impl IoTDevice {
    pub fn new(id: u32, threshold: usize, frost_key: frost::keys::KeyPackage, group_pub: frost::keys::PublicKeyPackage, peer_keys: HashMap<u32, VerifyingKey>) -> Result<Self, AggError> {
        //Basic checks
        if id == 0 { return Err(AggError::CryptoError("Device ID cannot be zero (Lagrange requirement)".into())); }
        if threshold == 0 { return Err(AggError::CryptoError("Threshold must be at least 1".into())); }
        if !peer_keys.is_empty() {
            let total_devices = peer_keys.len() + 1;
            if threshold > total_devices { return Err(AggError::CryptoError( format!("Threshold {} exceeds total devices {}", threshold, total_devices) )); }
            if total_devices > MAX_DEVICES { return Err(AggError::CryptoError( format!("Too many devices: {} > {}", total_devices, MAX_DEVICES) )); }
        }
        //Initialization
        let mut valid_participant_ids = HashSet::new();
        valid_participant_ids.insert(id);
        for peer_id in peer_keys.keys() { valid_participant_ids.insert(*peer_id); }
        Ok(Self {
            id, threshold, frost_key, group_pub, peer_keys,
            sig_key: SigningKey::generate(&mut OsRng), valid_participant_ids,
            verified_ciphertexts: HashMap::new(), partials: HashMap::new(),
            agg_c1: None, agg_c2: None,
            stark_prover: BinaryProver::new(),
            rates: HashMap::new(),
            seen_nonces: HashMap::new(),
        })
    }
    //Generate proof for our state (0 or 1)
    pub fn generate_proof(&self, state: u8) -> Result<DeviceProof, AggError> {
        if state > 1 { return Err(AggError::CryptoError("State must be 0/1".into())); }
        //Setup
        let ts = timestamp();
        let mut r = Scalar::random(&mut OsRng);
        let g = RISTRETTO_BASEPOINT_POINT;
        let h = frost_to_point(&self.group_pub.verifying_key())?;
        //ElGamal encrypt
        let (c1, c2) = (g * r, g * Scalar::from(state as u64) + h * r);
        //Generate ElGamal proof
        let eg_proof = ElGamalProof::prove(state, &r, &c1, &c2, &h, self.id, ts);
        //Compute STARK commitment
        let commitment = ElGamalProof::compute_stark_commitment(state, &eg_proof.nonce_bytes, &eg_proof.pedersen_commit.0);
        let commitment_bytes = commitment.as_int().to_le_bytes().to_vec();
        //Build STARK trace
        let nonce_elem = bytes_to_base_element(&eg_proof.nonce_bytes);
        let pedersen_elem = bytes_to_base_element(eg_proof.pedersen_commit.0.as_bytes());
        let trace = self.stark_prover.build_trace(state, nonce_elem, pedersen_elem);
        //Stark Proof
        let stark_proof = self.stark_prover.prove(trace).map_err(|e| { r.zeroize(); AggError::CryptoError(format!("STARK failed: {:?}", e)) })?;
        let mut bytes = Vec::new();
        stark_proof.write_into(&mut bytes);
        r.zeroize();
        Ok(DeviceProof {
            device_id: self.id, timestamp: ts,
            elgamal_c1: c1.compress().into(), elgamal_c2: c2.compress().into(),
            elgamal_proof: eg_proof.clone(), stark_commitment: commitment_bytes,
            stark_proof: bytes,
            signature: {let mut sig_data = Vec::new();sig_data.extend_from_slice(&ts.to_le_bytes());sig_data.extend_from_slice(&self.id.to_le_bytes());sig_data.extend_from_slice(&eg_proof.nonce_bytes);sig_data.extend_from_slice(c1.compress().as_bytes());sig_data.extend_from_slice(c2.compress().as_bytes());sig_data.extend_from_slice(eg_proof.pedersen_commit.0.as_bytes());sig_data.extend_from_slice(eg_proof.commit_r.0.as_bytes());sig_data.extend_from_slice(eg_proof.commit_s.0.as_bytes());sig_data.extend_from_slice(eg_proof.commit_p.0.as_bytes());sig_data.extend_from_slice(&eg_proof.resp_r.0.to_bytes());sig_data.extend_from_slice(&eg_proof.resp_state.0.to_bytes());sig_data.extend_from_slice(&commitment.as_int().to_le_bytes());self.sig_key.sign(&sig_data).to_bytes()},
        })
    }

    //Receive and verify a proof from a peer
    pub fn receive_proof(&mut self, p: DeviceProof) -> Result<(), AggError> {
        //Auto-cleanup if storage limits exceeded
        if self.verified_ciphertexts.len() >= MAX_STORED_PROOFS {
            self.cleanup();
            if self.verified_ciphertexts.len() >= MAX_STORED_PROOFS {return Err(AggError::RateLimited);}
        }
        //DoS Checks
        check_rate(p.device_id, &mut self.rates)?;
        let now = timestamp();
        let adjusted_now = now + MAX_CLOCK_SKEW;
        if p.timestamp > adjusted_now { return Err(AggError::InvalidProof("Timestamp too far in future".into())); }
        if p.timestamp + PROOF_EXPIRY < now.saturating_sub(MAX_CLOCK_SKEW) { return Err(AggError::ExpiredProof); }
        let device_nonces = self.seen_nonces.entry(p.device_id).or_insert_with(HashSet::new);
        if device_nonces.len() >= MAX_NONCES_PER_DEVICE { return Err(AggError::RateLimited); }
        if !device_nonces.insert(p.elgamal_proof.nonce_bytes) { return Err(AggError::InvalidProof("Nonce already used".into())); }
        if self.verified_ciphertexts.contains_key(&p.device_id) { return Err(AggError::InvalidProof("Duplicate".into())); }
        if p.stark_proof.len() > MAX_PROOF_SIZE { return Err(AggError::InvalidProof("Too big".into())); }
        //Verify signature
        let pk = self.peer_keys.get(&p.device_id).ok_or(AggError::InvalidProof("Unknown device".into()))?; {if p.stark_commitment.len() != 16 { return Err(AggError::InvalidProof("Bad commitment size".into()));}let mut commitment_bytes = [0u8; 16];commitment_bytes.copy_from_slice(&p.stark_commitment);let mut sig_data = Vec::new();sig_data.extend_from_slice(&p.timestamp.to_le_bytes());sig_data.extend_from_slice(&p.device_id.to_le_bytes());sig_data.extend_from_slice(&p.elgamal_proof.nonce_bytes);sig_data.extend_from_slice(p.elgamal_c1.0.as_bytes());sig_data.extend_from_slice(p.elgamal_c2.0.as_bytes());sig_data.extend_from_slice(p.elgamal_proof.pedersen_commit.0.as_bytes());sig_data.extend_from_slice(p.elgamal_proof.commit_r.0.as_bytes());sig_data.extend_from_slice(p.elgamal_proof.commit_s.0.as_bytes());sig_data.extend_from_slice(p.elgamal_proof.commit_p.0.as_bytes());sig_data.extend_from_slice(&p.elgamal_proof.resp_r.0.to_bytes());sig_data.extend_from_slice(&p.elgamal_proof.resp_state.0.to_bytes());sig_data.extend_from_slice(&commitment_bytes);let sig = Signature::try_from(&p.signature[..]).map_err(|_| AggError::InvalidProof("bad sig".into()))?;pk.verify(&sig_data, &sig).map_err(|_| AggError::InvalidProof("sig verify failed".into()))?;}
        //Verify ElGamal correctness proof
        let c1 = p.elgamal_c1.0.decompress().ok_or(AggError::InvalidProof("bad c1".into()))?;
        let c2 = p.elgamal_c2.0.decompress().ok_or(AggError::InvalidProof("bad c2".into()))?;
        let h = frost_to_point(&self.group_pub.verifying_key())?;
        if !p.elgamal_proof.verify(&c1, &c2, &h, p.device_id, p.timestamp) { return Err(AggError::InvalidProof("Schnorr failed".into())); }
        //Verify STARK proof
        let mut commitment_bytes = [0u8; 16];
        commitment_bytes.copy_from_slice(&p.stark_commitment);
        let mut commitment_val: u128 = 0;
        for i in 0..16 { commitment_val |= (commitment_bytes[i] as u128) << (i * 8); }
        let commitment_elem = BaseElement::new(commitment_val);
        let nonce_elem = bytes_to_base_element(&p.elgamal_proof.nonce_bytes);
        let pedersen_elem = bytes_to_base_element(p.elgamal_proof.pedersen_commit.0.as_bytes());
        let stark_proof = Proof::from_bytes(&p.stark_proof[..]).map_err(|_| AggError::InvalidProof("bad STARK format".into()))?;
        let pub_inputs = BinaryPublicInputs {state_commitment: commitment_elem,nonce_public: nonce_elem,pedersen_public: pedersen_elem};
        let min_opts = AcceptableOptions::MinConjecturedSecurity(95);
        verify::<BinaryAir, Blake3_256<BaseElement>, DefaultRandomCoin<Blake3_256<BaseElement>>, MerkleTree<Blake3_256<BaseElement>>>(stark_proof, pub_inputs, &min_opts).map_err(|_| AggError::InvalidProof("STARK verify failed".into()))?;
        self.verified_ciphertexts.insert(p.device_id, VerifiedCiphertext {timestamp: p.timestamp,c1,c2,});
        Ok(())
    }
    //Clean up old proofs and partials
    pub fn cleanup(&mut self) {
        let cutoff = timestamp().saturating_sub(PROOF_EXPIRY);
        let expired_devices: HashSet<u32> = self.verified_ciphertexts.iter().filter(|(_, vc)| vc.timestamp <= cutoff).map(|(id, _)| *id).collect();
        self.verified_ciphertexts.retain(|_, vc| vc.timestamp > cutoff);
        self.partials.retain(|_, p| p.timestamp > cutoff);
        for device_id in expired_devices { self.seen_nonces.remove(&device_id); }
    }
    //Recompute aggregate ciphertexts
    fn recompute(&mut self) {
        if self.verified_ciphertexts.is_empty() { self.agg_c1 = None; self.agg_c2 = None; } else {
            let (mut c1, mut c2) = (RistrettoPoint::identity(), RistrettoPoint::identity());
            for vc in self.verified_ciphertexts.values() {
                c1+=vc.c1;
                c2+=vc.c2;
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

//Convert 32 bytes to field element using XOR of both halves
pub fn bytes_to_base_element(bytes: &[u8; 32]) -> BaseElement {
    let mut val: u128 = 0;
    for i in 0..16 {
        val |= ((bytes[i] ^ bytes[i+16]) as u128) << (i * 8);
    }
    BaseElement::new(val)
}