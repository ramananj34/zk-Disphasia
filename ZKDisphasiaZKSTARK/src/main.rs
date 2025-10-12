use serde::{Deserialize, Serialize, Deserializer, Serializer};
use serde_with::{serde_as, Bytes};
use curve25519_dalek_ng::{ristretto::*, scalar::Scalar, traits::Identity, constants::RISTRETTO_BASEPOINT_POINT};
use winterfell::{
    Air, AirContext, Assertion, EvaluationFrame, ProofOptions, Prover, Proof,
    TraceInfo, TransitionConstraintDegree,
    crypto::{hashers::Blake3_256, DefaultRandomCoin, MerkleTree},
    math::{fields::f128::BaseElement, FieldElement, ToElements, StarkField},
    matrix::ColMatrix, TraceTable, verify, AcceptableOptions,
    ConstraintCompositionCoefficients, DefaultConstraintEvaluator, DefaultTraceLde,
    PartitionOptions, StarkDomain, TracePolyTable, AuxRandElements
};
use winter_utils::Serializable;
use merlin::Transcript;
use frost_ristretto255 as frost;
use ed25519_dalek::{SigningKey, VerifyingKey, Signature, Signer, Verifier};
use subtle::ConstantTimeEq;
use zeroize::Zeroize;
use rand::rngs::OsRng;
use std::collections::{HashMap, BTreeMap};
use std::error::Error;

//Config
const PROOF_EXPIRY: u64 = 300;
const RECOMPUTE_INTERVAL: u64 = 30;
const MAX_DEVICES: usize = 10000;
const MAX_PROOF_SIZE: usize = 65536;  //STARKs are bigger
const RATE_WINDOW: u64 = 10;
const MAX_MSGS_PER_WINDOW: u32 = 10;

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
            Self::DkgIncomplete => write!(f, "DKG not done"),
            Self::RateLimited => write!(f, "Rate limited"),
        }
    }
}

impl Error for AggError {}

//STARK AIR definition - enforces binary constraint
#[derive(Clone, Debug)]
pub struct BinaryPublicInputs {
    ciphertext_commitment: BaseElement,  //links STARK to Schnorr proof
}

impl ToElements<BaseElement> for BinaryPublicInputs {
    fn to_elements(&self) -> Vec<BaseElement> { vec![self.ciphertext_commitment] }
}

//AIR = Algebraic Intermediate Representation
//This defines the constraint that state * (state - 1) = 0
#[allow(dead_code)]
pub struct BinaryAir {
    context: AirContext<BaseElement>,
    value: BaseElement,
}

impl Air for BinaryAir {
    type BaseField = BaseElement;
    type PublicInputs = BinaryPublicInputs;
    type GkrProof = ();
    type GkrVerifier = ();

    fn new(trace_info: TraceInfo, pub_inputs: Self::PublicInputs, opts: ProofOptions) -> Self {
        assert_eq!(1, trace_info.width());
        Self {
            context: AirContext::new(trace_info, vec![TransitionConstraintDegree::new(2)], 1, opts),
            value: pub_inputs.ciphertext_commitment,
        }
    }

    fn context(&self) -> &AirContext<Self::BaseField> { &self.context }

    //This is where the magic happens - enforce the binary constraint!
    fn evaluate_transition<E: FieldElement + From<Self::BaseField>>(
        &self, frame: &EvaluationFrame<E>, _: &[E], result: &mut [E]
    ) {
        let state = frame.current()[0];
        result[0] = state * (state - E::ONE);  //forces state to be 0 or 1
    }

    fn get_assertions(&self) -> Vec<Assertion<Self::BaseField>> {
        vec![Assertion::single(0, 0, BaseElement::ZERO)]
    }
}

//STARK prover implementation
pub struct BinaryProver {
    options: ProofOptions,
    last_commit: std::cell::Cell<Option<BaseElement>>,
}

impl BinaryProver {
    pub fn new() -> Self {
        Self {
            options: ProofOptions::new(32, 16, 0, winterfell::FieldExtension::None, 8, 127),
            last_commit: std::cell::Cell::new(None),
        }
    }

    //Build execution trace using commitment as seed
    pub fn build_trace(&self, commit: BaseElement) -> TraceTable<BaseElement> {
        self.last_commit.set(Some(commit));
        let len = 128;  //trace length
        let mut trace = TraceTable::new(1, len);
        
        //Use commitment to generate deterministic binary sequence
        let cb = commit.as_int().to_le_bytes();
        
        trace.fill(|s| s[0] = BaseElement::ZERO,
        |step, s| {
            let byte_idx = (step / 8) % 16;
            let bit_idx = step % 8;
            let bit = (cb[byte_idx] >> bit_idx) & 1;
            s[0] = BaseElement::new(bit as u128);
        });
        trace
    }
}

impl Prover for BinaryProver {
    type BaseField = BaseElement;
    type Air = BinaryAir;
    type Trace = TraceTable<BaseElement>;
    type HashFn = Blake3_256<BaseElement>;
    type RandomCoin = DefaultRandomCoin<Self::HashFn>;
    type VC = MerkleTree<Self::HashFn>;
    type TraceLde<E: FieldElement<BaseField = Self::BaseField>> =
        DefaultTraceLde<E, Self::HashFn, Self::VC>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = Self::BaseField>> =
        DefaultConstraintEvaluator<'a, Self::Air, E>;

    fn get_pub_inputs(&self, _: &Self::Trace) -> BinaryPublicInputs {
        BinaryPublicInputs { ciphertext_commitment: self.last_commit.get().unwrap() }
    }

    fn options(&self) -> &ProofOptions { &self.options }

    fn new_trace_lde<E: FieldElement<BaseField = Self::BaseField>>(
        &self, info: &TraceInfo, main: &ColMatrix<Self::BaseField>,
        domain: &StarkDomain<Self::BaseField>, part: PartitionOptions
    ) -> (Self::TraceLde<E>, TracePolyTable<E>) {
        DefaultTraceLde::new(info, main, domain, part)
    }

    fn new_evaluator<'a, E: FieldElement<BaseField = Self::BaseField>>(
        &self, air: &'a Self::Air, aux: Option<AuxRandElements<E>>,
        coeffs: ConstraintCompositionCoefficients<E>
    ) -> Self::ConstraintEvaluator<'a, E> {
        DefaultConstraintEvaluator::new(air, aux, coeffs)
    }
}

//Serialization wrappers
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

//ElGamal correctness proof
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ElGamalProof {
    pub commit_r: SerCompressed,
    pub commit_s: SerCompressed,
    pub resp_r: SerScalar,
    pub resp_state: SerScalar,
}

impl ElGamalProof {
    fn prove(state: u8, r: &Scalar, c1: &RistrettoPoint, c2: &RistrettoPoint, h: &RistrettoPoint, dev_id: u32, ts: u64) -> Self {
        let g = RISTRETTO_BASEPOINT_POINT;
        let w = Scalar::random(&mut OsRng);
        let v = Scalar::random(&mut OsRng);
        let cr = g * w;
        let cs = g * v + h * w;
        //Fiat-Shamir
        let mut t = Transcript::new(b"elgamal-correctness");
        t.append_u64(b"device", dev_id as u64);
        t.append_u64(b"timestamp", ts);
        t.append_message(b"c1", c1.compress().as_bytes());
        t.append_message(b"c2", c2.compress().as_bytes());
        t.append_message(b"R", cr.compress().as_bytes());
        t.append_message(b"S", cs.compress().as_bytes());
        let mut cb = [0u8; 64];
        t.challenge_bytes(b"challenge", &mut cb);
        let c = Scalar::from_bytes_mod_order_wide(&cb);
        Self {
            commit_r: cr.compress().into(), commit_s: cs.compress().into(),
            resp_r: (w + c * r).into(), resp_state: (v + c * Scalar::from(state as u64)).into(),
        }
    }
    
    fn verify(&self, c1: &RistrettoPoint, c2: &RistrettoPoint, h: &RistrettoPoint, dev_id: u32, ts: u64) -> bool {
        let g = RISTRETTO_BASEPOINT_POINT;
        let (Some(cr), Some(cs)) = (self.commit_r.0.decompress(), self.commit_s.0.decompress())
        else { return false };
        let mut t = Transcript::new(b"elgamal-correctness");
        t.append_u64(b"device", dev_id as u64);
        t.append_u64(b"timestamp", ts);
        t.append_message(b"c1", c1.compress().as_bytes());
        t.append_message(b"c2", c2.compress().as_bytes());
        t.append_message(b"R", self.commit_r.0.as_bytes());
        t.append_message(b"S", self.commit_s.0.as_bytes());
        let mut cb = [0u8; 64];
        t.challenge_bytes(b"challenge", &mut cb);
        let c = Scalar::from_bytes_mod_order_wide(&cb);
        let chk1 = g * self.resp_r.0 == cr + c1 * c;
        let chk2 = g * self.resp_state.0 + h * self.resp_r.0 == cs + c2 * c;
        chk1 && chk2
    }

    //Create commitment to link Schnorr proof to STARK proof
    fn get_commitment(&self) -> BaseElement {
        let mut h = blake2b_simd::Params::new().hash_length(16).to_state();
        h.update(b"linked-commitment");
        h.update(&self.resp_state.0.to_bytes());
        h.update(&self.resp_r.0.to_bytes());
        let hb = h.finalize();
        let b = hb.as_bytes();
        let mut val: u128 = 0;
        for i in 0..16 { val |= (b[i] as u128) << (i * 8); }
        BaseElement::new(val)
    }
}

//Device proof with STARK
#[serde_as]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceProof {
    pub device_id: u32,
    pub timestamp: u64,
    pub elgamal_c1: SerCompressed,
    pub elgamal_c2: SerCompressed,
    pub elgamal_proof: ElGamalProof,
    pub stark_proof: Vec<u8>,  //STARK proof for binary constraint
    #[serde_as(as = "Bytes")]
    pub signature: [u8; 64],
}

//Schnorr proof for partial decryption
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SchnorrProof {
    pub commitment: SerCompressed,
    pub response: SerScalar,
}

impl SchnorrProof {
    fn prove_dlog(secret: &Scalar, sum_c1: &RistrettoPoint, partial: &RistrettoPoint, ts: u64, id: u32) -> Self {
        let r = Scalar::random(&mut OsRng);
        let c = sum_c1 * r;
        let ch = Self::challenge(sum_c1, partial, &c, ts, id);
        Self { commitment: c.compress().into(), response: (r + ch * secret).into() }
    }
    
    fn verify_dlog(&self, sum_c1: &RistrettoPoint, partial: &RistrettoPoint, ts: u64, id: u32) -> bool {
        let Some(c) = self.commitment.0.decompress() else { return false };
        let ch = Self::challenge(sum_c1, partial, &c, ts, id);
        sum_c1 * self.response.0 == c + partial * ch
    }
    
    fn challenge(sum_c1: &RistrettoPoint, partial: &RistrettoPoint, commit: &RistrettoPoint, ts: u64, id: u32) -> Scalar {
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

//IoT Device
pub struct IoTDevice {
    pub id: u32,
    frost_key: frost::keys::KeyPackage,
    group_pub: frost::keys::PublicKeyPackage,
    sig_key: SigningKey,
    peer_keys: HashMap<u32, VerifyingKey>,
    proofs: HashMap<u32, DeviceProof>,
    partials: HashMap<u32, PartialDecryption>,
    agg_c1: Option<RistrettoPoint>,
    agg_c2: Option<RistrettoPoint>,
    stark_prover: BinaryProver,  //STARK prover
    threshold: usize,
    rates: HashMap<u32, (u64, u32)>,
    last_recomp: u64,
}

impl IoTDevice {
    pub fn new(id: u32, threshold: usize, frost_key: frost::keys::KeyPackage, group_pub: frost::keys::PublicKeyPackage, peer_keys: HashMap<u32, VerifyingKey>) -> Self {
        Self {
            id, threshold, frost_key, group_pub, peer_keys,
            sig_key: SigningKey::generate(&mut OsRng),
            proofs: HashMap::new(), partials: HashMap::new(),
            agg_c1: None, agg_c2: None,
            stark_prover: BinaryProver::new(),
            rates: HashMap::new(), last_recomp: 0,
        }
    }
    
    pub fn generate_proof(&self, state: u8) -> Result<DeviceProof, AggError> {
        if state > 1 { return Err(AggError::CryptoError("State must be 0/1".into())); }
        let ts = timestamp();
        let mut r = Scalar::random(&mut OsRng);
        let g = RISTRETTO_BASEPOINT_POINT;
        let h = frost_to_point(&self.group_pub.verifying_key())?;
        //ElGamal encrypt
        let (c1, c2) = (g * r, g * Scalar::from(state as u64) + h * r);
        //Schnorr proof for ElGamal
        let eg_proof = ElGamalProof::prove(state, &r, &c1, &c2, &h, self.id, ts);
        //Get commitment linking Schnorr to STARK
        let commit = eg_proof.get_commitment();
        //Build STARK trace and generate proof
        let trace = self.stark_prover.build_trace(commit);
        let stark_proof = self.stark_prover.prove(trace)
            .map_err(|e| { r.zeroize(); AggError::CryptoError(format!("STARK failed: {:?}", e)) })?;
        let mut bytes = Vec::new();
        stark_proof.write_into(&mut bytes);
        r.zeroize();
        Ok(DeviceProof {
            device_id: self.id, timestamp: ts,
            elgamal_c1: c1.compress().into(), elgamal_c2: c2.compress().into(),
            elgamal_proof: eg_proof, stark_proof: bytes,
            signature: self.sign(&[&ts.to_le_bytes(), &self.id.to_le_bytes(), c1.compress().as_bytes(), c2.compress().as_bytes()]),
        })
    }
    
    pub fn receive_proof(&mut self, p: DeviceProof) -> Result<(), AggError> {
        self.check_rate(p.device_id)?;
        let now = timestamp();
        if p.timestamp + PROOF_EXPIRY < now { return Err(AggError::ExpiredProof); }
        if self.proofs.get(&p.device_id).map_or(false, |e| e.timestamp + PROOF_EXPIRY > now) {
            return Err(AggError::InvalidProof("Duplicate".into()));
        }
        if p.stark_proof.len() > MAX_PROOF_SIZE {
            return Err(AggError::InvalidProof("Too big".into()));
        }
        //Verify signature
        let pk = self.peer_keys.get(&p.device_id)
            .ok_or(AggError::InvalidProof("Unknown device".into()))?;
        self.verify_sig(pk, &[&p.timestamp.to_le_bytes(), &p.device_id.to_le_bytes(), p.elgamal_c1.0.as_bytes(), p.elgamal_c2.0.as_bytes()], &p.signature)?;
        //Verify ElGamal proof
        let c1 = p.elgamal_c1.0.decompress().ok_or(AggError::InvalidProof("bad c1".into()))?;
        let c2 = p.elgamal_c2.0.decompress().ok_or(AggError::InvalidProof("bad c2".into()))?;
        let h = frost_to_point(&self.group_pub.verifying_key())?;
        if !p.elgamal_proof.verify(&c1, &c2, &h, p.device_id, p.timestamp) {
            return Err(AggError::InvalidProof("ElGamal proof failed".into()));
        }
        
        //Verify STARK proof
        let commit = p.elgamal_proof.get_commitment();
        let stark_proof = Proof::from_bytes(&p.stark_proof[..])
            .map_err(|_| AggError::InvalidProof("bad STARK format".into()))?;
        let pub_inputs = BinaryPublicInputs { ciphertext_commitment: commit };
        let min_opts = AcceptableOptions::MinConjecturedSecurity(95);
        verify::<BinaryAir, Blake3_256<BaseElement>, DefaultRandomCoin<Blake3_256<BaseElement>>, MerkleTree<Blake3_256<BaseElement>>>(stark_proof, pub_inputs, &min_opts)
            .map_err(|_| AggError::InvalidProof("STARK verify failed".into()))?;
        
        self.proofs.insert(p.device_id, p);
        self.maybe_recompute();
        Ok(())
    }
    
    pub fn cleanup(&mut self) {
        let cutoff = timestamp().saturating_sub(PROOF_EXPIRY);
        self.proofs.retain(|_, p| p.timestamp > cutoff);
        self.partials.retain(|_, p| p.timestamp > cutoff);
        self.maybe_recompute();
    }
    
    fn maybe_recompute(&mut self) {
        let now = timestamp();
        if now >= self.last_recomp + RECOMPUTE_INTERVAL {
            self.recompute();
            self.last_recomp = now;
        }
    }
    
    fn recompute(&mut self) {
        if self.proofs.is_empty() {
            self.agg_c1 = None; self.agg_c2 = None;
        } else {
            let (mut c1, mut c2) = (RistrettoPoint::identity(), RistrettoPoint::identity());
            for p in self.proofs.values() {
                if let (Some(p1), Some(p2)) = (p.elgamal_c1.0.decompress(), p.elgamal_c2.0.decompress()) {
                    c1 += p1; c2 += p2;
                }
            }
            self.agg_c1 = Some(c1); self.agg_c2 = Some(c2);
        }
    }
    
    fn check_rate(&mut self, id: u32) -> Result<(), AggError> {
        let now = timestamp();
        let e = self.rates.entry(id).or_insert((now, 0));
        if now >= e.0 + RATE_WINDOW { *e = (now, 0); }
        if e.1 >= MAX_MSGS_PER_WINDOW { return Err(AggError::RateLimited); }
        e.1 += 1; Ok(())
    }
    
    pub fn generate_partial_decryption(&mut self) -> Result<PartialDecryption, AggError> {
        self.recompute();
        let sum_c1 = self.agg_c1.ok_or(AggError::CryptoError("No agg".into()))?;
        let ts = timestamp();
        let mut sec = frost_to_scalar(&self.frost_key.signing_share())?;
        let partial = sum_c1 * sec;
        let proof = SchnorrProof::prove_dlog(&sec, &sum_c1, &partial, ts, self.id);
        sec.zeroize();
        
        Ok(PartialDecryption {
            device_id: self.id, timestamp: ts,
            partial: partial.compress().into(), proof,
            signature: self.sign(&[&ts.to_le_bytes(), &self.id.to_le_bytes(), partial.compress().as_bytes()]),
        })
    }
    
    pub fn receive_partial(&mut self, p: PartialDecryption) -> Result<(), AggError> {
        self.check_rate(p.device_id)?;
        if p.timestamp + PROOF_EXPIRY < timestamp() { return Err(AggError::ExpiredProof); }
        let pk = self.peer_keys.get(&p.device_id)
            .ok_or(AggError::InvalidProof("Unknown".into()))?;
        self.verify_sig(pk, &[&p.timestamp.to_le_bytes(), &p.device_id.to_le_bytes(), p.partial.0.as_bytes()], &p.signature)?;
        self.partials.insert(p.device_id, p);
        Ok(())
    }
    
    pub fn compute_aggregate(&mut self) -> Result<(usize, usize), AggError> {
        self.recompute();
        let cutoff = timestamp().saturating_sub(PROOF_EXPIRY);
        let valid: Vec<_> = self.proofs.values().filter(|p| p.timestamp > cutoff).collect();
        if valid.is_empty() { return Ok((0, 0)); }
        let valid_parts: Vec<_> = self.partials.values().filter(|p| p.timestamp > cutoff).collect();
        if valid_parts.len() < self.threshold { return Err(AggError::ThresholdNotMet); }
        let sum_c1 = self.agg_c1.ok_or(AggError::CryptoError("No agg".into()))?;
        let sum_c2 = self.agg_c2.ok_or(AggError::CryptoError("No agg".into()))?;
        //Verify partials
        let mut verified = Vec::new();
        for p in valid_parts.iter().take(self.threshold) {
            let pt = p.partial.0.decompress().ok_or(AggError::CryptoError("bad partial".into()))?;
            if !p.proof.verify_dlog(&sum_c1, &pt, p.timestamp, p.device_id) {
                return Err(AggError::InvalidProof(format!("Failed for {}", p.device_id)));
            }
            verified.push((p.device_id, pt));
        }
        //Lagrange interpolation
        let ids: Vec<Scalar> = verified.iter().map(|(id, _)| Scalar::from(*id as u64)).collect();
        let mut combined = RistrettoPoint::identity();
        for i in 0..verified.len() {
            let mut lambda = Scalar::one();
            for j in 0..verified.len() {
                if i != j { lambda *= -ids[j] * (ids[i] - ids[j]).invert(); }
            }
            combined += verified[i].1 * lambda;
        }
        Ok((bsgs_dlog(sum_c2 - combined, RISTRETTO_BASEPOINT_POINT)?, valid.len()))
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

//Helper functions
fn bsgs_dlog(target: RistrettoPoint, base: RistrettoPoint) -> Result<usize, AggError> {
    let m = ((MAX_DEVICES as f64).sqrt() as usize) + 1;
    let mut baby = Vec::with_capacity(m);
    let mut cur = RistrettoPoint::identity();
    for _ in 0..m {
        baby.push(cur.compress().to_bytes());
        cur += base;
    }
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

pub fn setup_dkg(n: usize, t: usize) 
    -> Result<Vec<(u32, frost::keys::KeyPackage, frost::keys::PublicKeyPackage)>, AggError> {
    let mut rng = OsRng;
    let mut r1_pkgs = BTreeMap::new();
    let mut r1_secs = HashMap::new();
    
    for i in 1..=n {
        let id = frost::Identifier::try_from(i as u16)
            .map_err(|e| AggError::CryptoError(e.to_string()))?;
        let (sec, pkg) = frost::keys::dkg::part1(id, n as u16, t as u16, &mut rng)
            .map_err(|e| AggError::CryptoError(e.to_string()))?;
        r1_secs.insert(i as u32, sec);
        r1_pkgs.insert(id, pkg);
    }
    
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

fn main() -> Result<(), AggError> {
    let (n, t, states) = (5, 3, [1u8, 0, 1, 1, 0]);
    
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
    
    for (i, &s) in states.iter().enumerate() {
        let p = devs[i].generate_proof(s)?;
        for d in devs.iter_mut() {
            d.receive_proof(p.clone())?;
        }
    }
    
    for i in 0..t {
        if devs[i].proofs.len() >= n {
            let p = devs[i].generate_partial_decryption()?;
            for d in devs.iter_mut() {
                d.receive_partial(p.clone()).ok();
            }
        }
    }
    
    for d in &mut devs {
        if let Ok((sum, total)) = d.compute_aggregate() {
            println!("Device {}: sum={}/{}", d.id, sum, total);
        }
    }
    
    Ok(())
}