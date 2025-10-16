//ZK-Disphasia STARK edition

use serde::{Deserialize, Serialize, Deserializer, Serializer}; //Serialize/deserialize
use serde_with::{serde_as, Bytes};//Serialize/deserialize
use curve25519_dalek_ng::{ristretto::*, scalar::Scalar, traits::Identity, constants::RISTRETTO_BASEPOINT_POINT}; //My curve
use winterfell::{Air, AirContext, Assertion, EvaluationFrame, ProofOptions, Prover, Proof,TraceInfo, TransitionConstraintDegree,crypto::{hashers::Blake3_256, DefaultRandomCoin, MerkleTree},math::{fields::f128::BaseElement, FieldElement, ToElements, StarkField},matrix::ColMatrix, TraceTable, verify, AcceptableOptions,ConstraintCompositionCoefficients, DefaultConstraintEvaluator, DefaultTraceLde,PartitionOptions, StarkDomain, TracePolyTable, AuxRandElements}; //Winterfell
use winter_utils::Serializable; //Winterfell
use merlin::Transcript; //Transcript
use frost_ristretto255 as frost; //FROST
use ed25519_dalek::{SigningKey, VerifyingKey, Signature, Signer, Verifier}; //Digital signatures
use zeroize::Zeroize; //Safe data deletion
use subtle::{Choice, ConditionallySelectable}; //Constant time operations
use rand::rngs::OsRng; //Random
use rand::RngCore; //Random
use std::collections::{HashMap, HashSet, BTreeMap}; //Data structures
use std::error::Error; //Errors

//Config constants
const PROOF_EXPIRY: u64 = 300; //proofs expire after 5 mins
const RECOMPUTE_INTERVAL: u64 = 30; //reaggregate every 30s
const MAX_DEVICES: usize = 10000; //max devices for discrete log
const RATE_WINDOW: u64 = 10; //rate limit window
const MAX_MSGS_PER_WINDOW: u32 = 10; //max msgs per window
const MAX_TOTAL_RATE: u32 = 50; //global max messages
const MAX_PROOF_SIZE: usize = 65536; //prevent DoS attacks
const MAX_CLOCK_SKEW: u64 = 60; //Allow for a time skew
const MAX_NONCES_PER_DEVICE: usize = 100; //More DoS protection
const MAX_STORED_PROOFS: usize = 10000; //More DoS Protection
const MAX_STORED_PARTIALS: usize = 10000; //more DoS Protection
const PROTOCOL_VERSION: u8 = 1; //Version for transcript

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
pub struct BinaryProver {
    options: ProofOptions,
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
    fn prove(state: u8, r: &Scalar, c1: &RistrettoPoint, c2: &RistrettoPoint, h: &RistrettoPoint, dev_id: u32, ts: u64) -> Self {
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

    fn verify(&self, c1: &RistrettoPoint, c2: &RistrettoPoint, h: &RistrettoPoint, dev_id: u32, ts: u64) -> bool {
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

    fn compute_stark_commitment(state: u8, nonce: &[u8; 32], pedersen: &CompressedRistretto) -> BaseElement {
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
    pub device_id: u32,
    pub timestamp: u64,
    pub partial: SerCompressed,
    pub proof: SchnorrProof,
    #[serde_as(as = "Bytes")]
    pub signature: [u8; 64],
}

//Main device struct - handles proof generation/verification and aggregation
pub struct IoTDevice {
    pub id: u32,
    frost_key: frost::keys::KeyPackage,
    group_pub: frost::keys::PublicKeyPackage,
    sig_key: SigningKey,
    peer_keys: HashMap<u32, VerifyingKey>,
    valid_participant_ids: HashSet<u32>,
    proofs: HashMap<u32, DeviceProof>,
    partials: HashMap<u32, PartialDecryption>,
    agg_c1: Option<RistrettoPoint>,
    agg_c2: Option<RistrettoPoint>,
    stark_prover: BinaryProver,
    threshold: usize,
    rates: HashMap<u32, (u64, u32)>,
    last_recomp: u64,
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
            proofs: HashMap::new(), partials: HashMap::new(),
            agg_c1: None, agg_c2: None,
            stark_prover: BinaryProver::new(),
            rates: HashMap::new(), last_recomp: 0,
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
        if self.proofs.len() >= MAX_STORED_PROOFS {
            self.cleanup();
            if self.proofs.len() >= MAX_STORED_PROOFS {return Err(AggError::RateLimited);}
        }
        //DoS Checks
        self.check_rate(p.device_id)?;
        let now = timestamp();
        let adjusted_now = now + MAX_CLOCK_SKEW;
        if p.timestamp > adjusted_now { return Err(AggError::InvalidProof("Timestamp too far in future".into())); }
        if p.timestamp + PROOF_EXPIRY < now.saturating_sub(MAX_CLOCK_SKEW) { return Err(AggError::ExpiredProof); }
        let device_nonces = self.seen_nonces.entry(p.device_id).or_insert_with(HashSet::new);
        if device_nonces.len() >= MAX_NONCES_PER_DEVICE { return Err(AggError::RateLimited); }
        if !device_nonces.insert(p.elgamal_proof.nonce_bytes) { return Err(AggError::InvalidProof("Nonce already used".into())); }
        if self.proofs.contains_key(&p.device_id) { return Err(AggError::InvalidProof("Duplicate".into())); }
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
        //Auto-cleanup if storage limits exceeded
        if self.partials.len() >= MAX_STORED_PARTIALS {
            self.cleanup();
            if self.partials.len() >= MAX_STORED_PARTIALS { return Err(AggError::RateLimited); }
        }
        //DoS Checks
        self.check_rate(p.device_id)?;
        let now = timestamp();
        let adjusted_now = now + MAX_CLOCK_SKEW;
        if p.timestamp > adjusted_now { return Err(AggError::InvalidProof("Timestamp too far in future".into())); }
        if p.timestamp + PROOF_EXPIRY < now.saturating_sub(MAX_CLOCK_SKEW) { return Err(AggError::ExpiredProof); }
        let pk = self.peer_keys.get(&p.device_id).ok_or(AggError::InvalidProof("Unknown".into()))?;
        //Verify signature
        self.verify_sig(pk, &[&p.timestamp.to_le_bytes(), &p.device_id.to_le_bytes(), p.partial.0.as_bytes()], &p.signature)?;
        self.recompute();
        //Verify Schnorr
        let sum_c1 = self.agg_c1.ok_or(AggError::CryptoError("No aggregation computed yet".into()))?;
        let pt = p.partial.0.decompress().ok_or(AggError::CryptoError("Invalid partial point".into()))?;
        let frost_id = frost::Identifier::try_from(p.device_id as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
        let public_key_share = self.group_pub.verifying_shares().get(&frost_id).ok_or(AggError::CryptoError("Unknown participant".into()))?;
        let public_key_share_point = frost_share_to_point(public_key_share)?;
        if !p.proof.verify_dlog(&sum_c1, &pt, &public_key_share_point, p.timestamp, p.device_id) { return Err(AggError::InvalidProof("Schnorr proof verification failed".into())); }
        //Add to results
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
        let expired_devices: HashSet<u32> = self.proofs.iter().filter(|(_, p)| p.timestamp <= cutoff).map(|(id, _)| *id).collect();
        self.proofs.retain(|_, p| p.timestamp > cutoff);
        self.partials.retain(|_, p| p.timestamp > cutoff);
        for device_id in expired_devices { self.seen_nonces.remove(&device_id); }
        self.maybe_recompute();
    }
    //Compute final aggregate using threshold decryption
    pub fn compute_aggregate(&mut self) -> Result<(usize, usize), AggError> {
        self.recompute();
        //Get valid proofs
        let valid = self.proofs.len();
        if valid == 0 { return Ok((0, 0)); }
        if self.partials.len() < self.threshold { return Err(AggError::ThresholdNotMet); }
        //Start aggregate
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
        for (id, _) in &verified {
            if !self.valid_participant_ids.contains(id) { return Err(AggError::InvalidProof( format!("Device {} is not a valid DKG participant", id) )); }
        }
        //Ensure no zero IDs
        if verified.iter().any(|(id, _)| *id == 0) { return Err(AggError::CryptoError("Device ID cannot be zero".into())); }
        //Check all IDs are unique
        let mut seen = HashSet::new();
        for (id, _) in &verified {
            if !seen.insert(id) { return Err(AggError::CryptoError("Duplicate device ID in partials".into())); }
        }
        //Check we have exactly threshold participants
        if verified.len() != self.threshold {
            return Err(AggError::CryptoError( format!("Expected {} partials, got {}", self.threshold, verified.len()) ));
        }
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
        Ok((bsgs_dlog(sum_c2 - combined, RISTRETTO_BASEPOINT_POINT)?, valid))
    }
    //Recompute aggregate ciphertexts
    fn recompute(&mut self) {
        if self.proofs.is_empty() { self.agg_c1 = None; self.agg_c2 = None; } else {
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
        let total_msgs: u32 = self.rates.values().filter(|(ts, _)| now < ts.saturating_add(RATE_WINDOW)).map(|(_, count)| count).sum();
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

//Helper functions
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

//Convert 32 bytes to field element using XOR of both halves
fn bytes_to_base_element(bytes: &[u8; 32]) -> BaseElement {
    let mut val: u128 = 0;
    for i in 0..16 {
        val |= ((bytes[i] ^ bytes[i+16]) as u128) << (i * 8);
    }
    BaseElement::new(val)
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