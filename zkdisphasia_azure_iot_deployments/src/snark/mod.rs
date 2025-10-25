use serde::{Deserialize, Serialize}; //Serialization/deserialization
use serde_with::{serde_as, Bytes}; //Serialization/deserialization
use curve25519_dalek_ng::{ristretto::*, scalar::Scalar, traits::Identity, constants::RISTRETTO_BASEPOINT_POINT}; //Curve
use halo2_proofs::{arithmetic::Field, halo2curves::{bn256::{Bn256, Fr as Halo2Fr, G1Affine}, ff::PrimeField}, circuit::{Layouter, SimpleFloorPlanner, Value}, plonk::{Advice, Circuit, Column, ConstraintSystem, Error as Halo2Error, Selector, create_proof, keygen_pk, keygen_vk, verify_proof, ProvingKey, VerifyingKey, Instance}, poly::{Rotation, commitment::Params, kzg::{commitment::{KZGCommitmentScheme, ParamsKZG}, multiopen::{ProverSHPLONK, VerifierSHPLONK}, strategy::SingleStrategy}}, transcript::{Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer}}; //Halo2
use merlin::Transcript; //Transcript
use frost_ristretto255 as frost; //Frost
use ed25519_dalek::{SigningKey, VerifyingKey as ed_vf, Signature, Signer, Verifier}; //ECDS
use zeroize::Zeroize; //Safe deletion
use rand::rngs::OsRng; //Random
use rand::RngCore; //Random
use std::collections::{HashMap, HashSet}; //Data structures
use std::fs::File; //File operations
use std::io::BufReader; //File operations
use std::path::Path; //File operations

use crate::common::{SerCompressed, SerScalar, AggError, VerifiedCiphertext, VerifiedPartial, PartialDecryption, PROTOCOL_VERSION, MAX_DEVICES, MAX_STORED_PROOFS, MAX_CLOCK_SKEW,MAX_NONCES_PER_DEVICE, PROOF_EXPIRY, timestamp, frost_to_point, check_rate};

const MAX_PROOF_SIZE: usize = 8192; //prevent DoS attacks
const _HALO2_K: u32 = 5;
const PARAMS_PATH: &str = "./trusted_setup/kzg_bn254_5.params";

//Load KZG parameters
pub fn load_kzg_params() -> Result<ParamsKZG<Bn256>, AggError> {
    let path = Path::new(PARAMS_PATH);
    if !path.exists() { return Err(AggError::CryptoError(format!("KZG params not found at: {}\nRun setup first!", PARAMS_PATH))); }
    let file = File::open(path).map_err(|e| AggError::CryptoError(format!("Failed to open params: {}", e)))?;
    let mut reader = BufReader::new(file);
    ParamsKZG::<Bn256>::read(&mut reader).map_err(|e| AggError::CryptoError(format!("Failed to read params: {}", e)))
}

//Halo2 circuit configuration
#[derive(Clone, Debug)]
struct BinaryConfig {
    advice: [Column<Advice>; 4],
    selector: Selector,
    instance: [Column<Instance>; 3],
}
//Circuit proving state is binary
#[warn(dead_code)]
#[derive(Clone, Debug)]
struct BinaryCircuit {
    state: Value<Halo2Fr>,
    nonce: Value<Halo2Fr>,
    pedersen: Value<Halo2Fr>,
}
impl Circuit<Halo2Fr> for BinaryCircuit {
    type Config = BinaryConfig;
    type FloorPlanner = SimpleFloorPlanner;
    fn without_witnesses(&self) -> Self {
        Self {
            state: Value::unknown(),
            nonce: Value::unknown(),
            pedersen: Value::unknown()
        }
    }
    fn configure(meta: &mut ConstraintSystem<Halo2Fr>) -> Self::Config {
        let advice = [meta.advice_column(),meta.advice_column(),meta.advice_column(),meta.advice_column()];
        let selector = meta.selector();
        let instance = [meta.instance_column(),meta.instance_column(),meta.instance_column()];
        for col in &advice {meta.enable_equality(*col);}
        for col in &instance {meta.enable_equality(*col);}
        //Binary constraint: state * (state - 1) = 0
        meta.create_gate("binary", |meta| {let s = meta.query_selector(selector);let state = meta.query_advice(advice[0], Rotation::cur());let one = halo2_proofs::plonk::Expression::Constant(Halo2Fr::ONE);vec![s * state.clone() * (state - one)]});
        //Hash constraint
        meta.create_gate("hash_with_pedersen", |meta| {let s = meta.query_selector(selector);let state = meta.query_advice(advice[0], Rotation::cur());let nonce = meta.query_advice(advice[1], Rotation::cur());let pedersen = meta.query_advice(advice[2], Rotation::cur());let commit = meta.query_advice(advice[3], Rotation::cur());let state_sq = state.clone() * state.clone();let state_5 = state_sq.clone() * state_sq.clone() * state.clone();let nonce_sq = nonce.clone() * nonce.clone();let nonce_5 = nonce_sq.clone() * nonce_sq.clone() * nonce.clone();let pedersen_sq = pedersen.clone() * pedersen.clone();let pedersen_5 = pedersen_sq.clone() * pedersen_sq.clone() * pedersen.clone();let mixed = state.clone() * nonce.clone() + state.clone() * pedersen.clone();let hash_result = state_5 + nonce_5 + pedersen_5 + mixed;vec![s * (hash_result - commit)] });
        BinaryConfig { advice, selector, instance }
    }
    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<Halo2Fr>) -> Result<(), Halo2Error> {
        let (hash_cell, nonce_cell, pedersen_cell) = layouter.assign_region(|| "main", |mut region| {
            config.selector.enable(&mut region, 0)?;
            region.assign_advice(|| "state", config.advice[0], 0, || self.state)?;
            let nonce_cell = region.assign_advice(|| "nonce", config.advice[1], 0, || self.nonce)?;
            let pedersen_cell = region.assign_advice(|| "pedersen", config.advice[2], 0, || self.pedersen)?;
            let hash_value = self.state.zip(self.nonce).zip(self.pedersen).map(|((s, n), p)| {let s_sq = s * s;let s_5 = s_sq * s_sq * s;let n_sq = n * n;let n_5 = n_sq * n_sq * n;let p_sq = p * p;let p_5 = p_sq * p_sq * p;s_5 + n_5 + p_5 + (s * n) + (s * p)});
            let hash_cell = region.assign_advice(|| "hash", config.advice[3], 0, || hash_value)?;
            Ok((hash_cell, nonce_cell, pedersen_cell))
        })?;
        layouter.constrain_instance(hash_cell.cell(), config.instance[0], 0)?;
        layouter.constrain_instance(nonce_cell.cell(), config.instance[1], 0)?;
        layouter.constrain_instance(pedersen_cell.cell(), config.instance[2], 0)?;
        Ok(())
    }
}
//Halo2 setup
#[derive(Clone)]
pub struct Halo2Setup {
    params: ParamsKZG<Bn256>,
    pk: ProvingKey<G1Affine>,
    vk: VerifyingKey<G1Affine>
}

//Setup Halo2
pub fn setup_halo2() -> Result<Halo2Setup, AggError> {
    let params = load_kzg_params()?;
    let empty_circuit = BinaryCircuit {state: Value::unknown(),nonce: Value::unknown(),pedersen: Value::unknown()};
    let vk = keygen_vk(&params, &empty_circuit).map_err(|e| AggError::CryptoError(format!("VK gen failed: {:?}", e)))?;
    let pk = keygen_pk(&params, vk.clone(), &empty_circuit).map_err(|e| AggError::CryptoError(format!("PK gen failed: {:?}", e)))?;
    Ok(Halo2Setup { params, pk, vk })
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
        //Define bases
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
        let mut cb = [0u8; 64];
        //Derive challenge
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
        //Reconstruct transcript
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
    fn compute_halo2_commitment(state: u8, nonce_bytes: &[u8; 32], pedersen: &CompressedRistretto) -> Halo2Fr {
        //Inputs to field elements
        let state_fr = Halo2Fr::from(state as u64);
        let nonce_fr = Halo2Fr::from_repr(*nonce_bytes).unwrap_or(Halo2Fr::ZERO);
        let pedersen_fr = Halo2Fr::from_repr(*pedersen.as_bytes()).unwrap_or(Halo2Fr::ZERO);
        //Compute non-linear hashes, then raises to the fifth power for entropy, a pseudo-hash in the finite field
        let s_sq = state_fr * state_fr;
        let s_5 = s_sq * s_sq * state_fr;
        let n_sq = nonce_fr * nonce_fr;
        let n_5 = n_sq * n_sq * nonce_fr;
        let p_sq = pedersen_fr * pedersen_fr;
        let p_5 = p_sq * p_sq * pedersen_fr;
        //Mix components together
        s_5 + n_5 + p_5 + (state_fr * nonce_fr) + (state_fr * pedersen_fr)
    }
}

//Device proof with Halo2
#[serde_as]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceProof {
    pub device_id: u32,
    pub timestamp: u64,
    pub elgamal_c1: SerCompressed, //ElGamal
    pub elgamal_c2: SerCompressed, //ElGamal
    pub elgamal_proof: ElGamalProof, //ElGamal
    pub halo2_commitment: [u8; 32], //Halo2 Commitment
    pub halo2_proof: Vec<u8>, //Halo2 Proof
    #[serde_as(as = "Bytes")]
    pub signature: [u8; 64], //Signature
}

//Main device struct - handles proof generation/verification and aggregation
pub struct IoTDevice {
    pub id: u32,
    pub frost_key: frost::keys::KeyPackage,
    pub group_pub: frost::keys::PublicKeyPackage,
    pub sig_key: SigningKey,
    pub peer_keys: HashMap<u32, ed_vf>,
    pub valid_participant_ids: HashSet<u32>,
    pub verified_ciphertexts: HashMap<u32, VerifiedCiphertext>,
    partials: HashMap<u32, VerifiedPartial>,
    agg_c1: Option<RistrettoPoint>,
    agg_c2: Option<RistrettoPoint>,
    halo2_setup: Halo2Setup,
    threshold: usize,
    rates: HashMap<u32, (u64, u32)>,
    seen_nonces: HashMap<u32, HashSet<[u8; 32]>>,
}
impl IoTDevice {
    pub fn new(id: u32, threshold: usize, frost_key: frost::keys::KeyPackage, group_pub: frost::keys::PublicKeyPackage, peer_keys: HashMap<u32, ed_vf>, halo2_setup: Halo2Setup) -> Result<Self, AggError> {
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
            sig_key: SigningKey::generate(&mut OsRng), valid_participant_ids, halo2_setup,
            verified_ciphertexts: HashMap::new(), partials: HashMap::new(),
            agg_c1: None, agg_c2: None,
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
        //Compute Halo2 commitment
        let pedersen_compressed = eg_proof.pedersen_commit.0;
        let sc = ElGamalProof::compute_halo2_commitment(state, &eg_proof.nonce_bytes, &pedersen_compressed);
        let sc_bytes: [u8; 32] = sc.to_repr().as_ref().try_into().unwrap();
        //Create Halo2 circuit
        let nonce_fr = Halo2Fr::from_repr(eg_proof.nonce_bytes).unwrap_or(Halo2Fr::ZERO);
        let pedersen_fr = Halo2Fr::from_repr(*pedersen_compressed.as_bytes()).unwrap_or(Halo2Fr::ZERO);
        let circuit = BinaryCircuit { state: Value::known(Halo2Fr::from(state as u64)), nonce: Value::known(nonce_fr), pedersen: Value::known(pedersen_fr) };
        //Generate Halo2 proof
        let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);
        let instance_col_0 = vec![sc];
        let instance_col_1 = vec![nonce_fr];
        let instance_col_2 = vec![pedersen_fr];
        create_proof::<KZGCommitmentScheme<Bn256>, ProverSHPLONK<'_, Bn256>, _, _, _, _>( &self.halo2_setup.params, &self.halo2_setup.pk, &[circuit], &[&[&instance_col_0[..], &instance_col_1[..], &instance_col_2[..]]], OsRng, &mut transcript ).map_err(|e| { r.zeroize(); AggError::CryptoError(format!("Halo2 failed: {:?}", e)) })?;
        //Return
        r.zeroize();
        Ok(DeviceProof {
            device_id: self.id, timestamp: ts,
            elgamal_c1: c1.compress().into(), elgamal_c2: c2.compress().into(),
            elgamal_proof: eg_proof.clone(), halo2_commitment: sc_bytes,
            halo2_proof: transcript.finalize(),
            signature: { let mut sig_data = Vec::new(); sig_data.extend_from_slice(&ts.to_le_bytes()); sig_data.extend_from_slice(&self.id.to_le_bytes()); sig_data.extend_from_slice(&eg_proof.nonce_bytes); sig_data.extend_from_slice(c1.compress().as_bytes()); sig_data.extend_from_slice(c2.compress().as_bytes()); sig_data.extend_from_slice(eg_proof.pedersen_commit.0.as_bytes()); sig_data.extend_from_slice(eg_proof.commit_r.0.as_bytes()); sig_data.extend_from_slice(eg_proof.commit_s.0.as_bytes()); sig_data.extend_from_slice(eg_proof.commit_p.0.as_bytes()); sig_data.extend_from_slice(&eg_proof.resp_r.0.to_bytes()); sig_data.extend_from_slice(&eg_proof.resp_state.0.to_bytes()); sig_data.extend_from_slice(&sc_bytes); self.sig_key.sign(&sig_data).to_bytes() },
        })
    }
    //Receive and verify a proof from a peer
    pub fn receive_proof(&mut self, p: DeviceProof) -> Result<(), AggError> {
        //Auto-cleanup if storage limits exceeded
        if self.verified_ciphertexts.len() >= MAX_STORED_PROOFS {
            self.cleanup();
            if self.verified_ciphertexts.len() >= MAX_STORED_PROOFS { return Err(AggError::RateLimited); }
        }
        //Perform DoS checks
        check_rate(p.device_id, &mut self.rates)?;
        let now = timestamp();
        let adjusted_now = now + MAX_CLOCK_SKEW;
        if p.timestamp > adjusted_now { return Err(AggError::InvalidProof("Timestamp too far in future".into())); }
        if p.timestamp + PROOF_EXPIRY < now.saturating_sub(MAX_CLOCK_SKEW) { return Err(AggError::ExpiredProof); }
        let device_nonces = self.seen_nonces.entry(p.device_id).or_insert_with(HashSet::new);
        if device_nonces.len() >= MAX_NONCES_PER_DEVICE { return Err(AggError::RateLimited); }
        if !device_nonces.insert(p.elgamal_proof.nonce_bytes) { return Err(AggError::InvalidProof("Nonce already used".into())); }
        if p.halo2_proof.len() > MAX_PROOF_SIZE { return Err(AggError::InvalidProof("Too big".into())); }
        if self.verified_ciphertexts.contains_key(&p.device_id) { return Err(AggError::InvalidProof("Duplicate".into())); }
        //Verify signature
        let pk = self.peer_keys.get(&p.device_id).ok_or(AggError::InvalidProof("Unknown device".into()))?;{let mut sig_data = Vec::new();sig_data.extend_from_slice(&p.timestamp.to_le_bytes());sig_data.extend_from_slice(&p.device_id.to_le_bytes());sig_data.extend_from_slice(&p.elgamal_proof.nonce_bytes);sig_data.extend_from_slice(p.elgamal_c1.0.as_bytes());sig_data.extend_from_slice(p.elgamal_c2.0.as_bytes());sig_data.extend_from_slice(p.elgamal_proof.pedersen_commit.0.as_bytes());sig_data.extend_from_slice(p.elgamal_proof.commit_r.0.as_bytes());sig_data.extend_from_slice(p.elgamal_proof.commit_s.0.as_bytes());sig_data.extend_from_slice(p.elgamal_proof.commit_p.0.as_bytes());sig_data.extend_from_slice(&p.elgamal_proof.resp_r.0.to_bytes());sig_data.extend_from_slice(&p.elgamal_proof.resp_state.0.to_bytes());sig_data.extend_from_slice(&p.halo2_commitment);let sig = Signature::try_from(&p.signature[..]).map_err(|_| AggError::InvalidProof("bad sig".into()))?;pk.verify(&sig_data, &sig).map_err(|_| AggError::InvalidProof("sig verify failed".into()))?;}
        //Verify ElGamal correctness proof
        let c1 = p.elgamal_c1.0.decompress().ok_or(AggError::InvalidProof("bad c1".into()))?;
        let c2 = p.elgamal_c2.0.decompress().ok_or(AggError::InvalidProof("bad c2".into()))?;
        let h = frost_to_point(&self.group_pub.verifying_key())?;
        if !p.elgamal_proof.verify(&c1, &c2, &h, p.device_id, p.timestamp) { return Err(AggError::InvalidProof("Schnorr failed".into())); }
        //Verify Halo2 proof
        let sc = Halo2Fr::from_repr(p.halo2_commitment).unwrap_or(Halo2Fr::ZERO);
        let nonce_fr = Halo2Fr::from_repr(p.elgamal_proof.nonce_bytes).unwrap_or(Halo2Fr::ZERO);
        let pedersen_fr = Halo2Fr::from_repr(*p.elgamal_proof.pedersen_commit.0.as_bytes()).unwrap_or(Halo2Fr::ZERO);
        let instance_col_0 = vec![sc];
        let instance_col_1 = vec![nonce_fr];
        let instance_col_2 = vec![pedersen_fr];
        let strategy = SingleStrategy::new(&self.halo2_setup.params);
        let mut transcript = Blake2bRead::<_, G1Affine, Challenge255<_>>::init(&p.halo2_proof[..]);
        verify_proof::<KZGCommitmentScheme<Bn256>, VerifierSHPLONK<'_, Bn256>, _, _, _>(&self.halo2_setup.params, &self.halo2_setup.vk, strategy,&[&[&instance_col_0[..], &instance_col_1[..], &instance_col_2[..]]], &mut transcript).map_err(|_| AggError::InvalidProof("Halo2 verify failed".into()))?;
        //Add to proofs
        self.verified_ciphertexts.insert(p.device_id, VerifiedCiphertext {timestamp: p.timestamp,c1,c2,});
        Ok(())
    }
    pub fn cleanup(&mut self) {
        let cutoff = timestamp().saturating_sub(PROOF_EXPIRY);
        let expired_devices: HashSet<u32> = self.verified_ciphertexts.iter().filter(|(_, vc)| vc.timestamp <= cutoff).map(|(id, _)| *id).collect();
        self.verified_ciphertexts.retain(|_, vc| vc.timestamp > cutoff);
        self.partials.retain(|_, p| p.timestamp > cutoff);
        for device_id in expired_devices { self.seen_nonces.remove(&device_id); }
    }
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