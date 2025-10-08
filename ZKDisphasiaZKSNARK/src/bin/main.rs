////////////////////////////////////////////////////////////////////////////
/// Libraries

use serde::{Deserialize, Serialize, Deserializer, Serializer};
use serde_with::{serde_as, Bytes};
use curve25519_dalek_ng::{ristretto::{CompressedRistretto, RistrettoPoint}, scalar::Scalar, traits::Identity, constants::RISTRETTO_BASEPOINT_POINT};
use halo2_proofs::{arithmetic::Field, circuit::{Layouter, SimpleFloorPlanner, Value}, plonk::{Advice, Circuit, Column, ConstraintSystem, Error as Halo2Error, Selector, create_proof, keygen_pk, keygen_vk, verify_proof, ProvingKey, VerifyingKey, Instance}, poly::{Rotation, commitment::Params, kzg::{commitment::{KZGCommitmentScheme, ParamsKZG}, multiopen::{ProverSHPLONK, VerifierSHPLONK}, strategy::SingleStrategy}}, transcript::{Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer}};
use halo2_proofs::halo2curves::bn256::{Bn256, Fr as Halo2Fr, G1Affine};
use merlin::Transcript;
use frost_ristretto255 as frost;
use ed25519_dalek::{SigningKey, VerifyingKey as SigSignKey, Signature, Signer, Verifier};
use subtle::ConstantTimeEq;
use zeroize::Zeroize;
use rand::rngs::OsRng;
use std::collections::{HashMap, BTreeMap};
use std::error::Error;
use std::fs::File;
use std::io::BufReader;
use std::path::Path;

////////////////////////////////////////////////////////////////////////////
/// Configuration

const PROOF_EXPIRATION_SECS: u64 = 300; //Proof validity window
const RECOMPUTE_INTERVAL_SECS: u64 = 30; //Aggregate recomputation frequency
const MAX_DEVICES: usize = 10000; //Network size limit
const MAX_HALO2_BYTES: usize = 4096; //DoS protection for proofs
const RATE_WINDOW_SECS: u64 = 10; //Rate limit reset interval
const MAX_MESSAGES_PER_WINDOW: u32 = 10; //Max messages per rate window
const HALO2_K: u32 = 8; //Circuit size parameter
const PARAMS_PATH: &str = "./trusted_setup/kzg_bn254_8.params"; //KZG parameters location

////////////////////////////////////////////////////////////////////////////
/// Error Types

#[derive(Debug)]
pub enum AggError {
    InvalidProof(String), //Proof validation failed
    ExpiredProof, //Timestamp too old
    ThresholdNotMet, //Insufficient partial decryptions
    CryptoError(String), //Cryptographic operation failed
    DkgIncomplete, //DKG not finished
    RateLimited, //Peer exceeded message limit
}
impl std::fmt::Display for AggError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AggError::InvalidProof(s) => write!(f, "Invalid proof: {}", s),
            AggError::ExpiredProof => write!(f, "Proof expired"),
            AggError::ThresholdNotMet => write!(f, "Insufficient participants"),
            AggError::CryptoError(s) => write!(f, "Cryptographic error: {}", s),
            AggError::DkgIncomplete => write!(f, "DKG not complete"),
            AggError::RateLimited => write!(f, "Rate limited"),
        }
    }
}
impl Error for AggError {}

////////////////////////////////////////////////////////////////////////////
/// Halo2 Circuit

//Circuit configuration for binary state constraint
#[derive(Clone, Debug)]
struct BinaryStateConfig { advice: Column<Advice>, selector: Selector, instance: Column<Instance>}

//Circuit proving state is 0 or 1
#[derive(Clone, Debug)]
struct BinaryStateCircuit { state: Value<Halo2Fr>, c1_bytes: Value<[u8; 32]>, c2_bytes: Value<[u8; 32]>}
impl Circuit<Halo2Fr> for BinaryStateCircuit {
    type Config = BinaryStateConfig;
    type FloorPlanner = SimpleFloorPlanner;
    fn without_witnesses(&self) -> Self { Self { state: Value::unknown(), c1_bytes: Value::unknown(), c2_bytes: Value::unknown()} }
    fn configure(meta: &mut ConstraintSystem<Halo2Fr>) -> Self::Config {
        let advice = meta.advice_column();
        let selector = meta.selector();
        meta.enable_equality(advice);
        //Gate enforces: state * (state - 1) = 0, so state ∈ {0,1}
        let instance = meta.instance_column();
        meta.enable_equality(instance);
        meta.create_gate("binary constraint", |meta| {
            let s = meta.query_selector(selector);
            let state = meta.query_advice(advice, Rotation::cur());
            let one = halo2_proofs::plonk::Expression::Constant(Halo2Fr::ONE);
            vec![s * state.clone() * (state - one)]
        });
        BinaryStateConfig { advice, selector, instance }
    }
    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<Halo2Fr>) -> Result<(), Halo2Error> {
        let (c1_cell, c2_cell) = layouter.assign_region(|| "binary state proof", |mut region| {
            config.selector.enable(&mut region, 0)?;
            region.assign_advice(|| "state", config.advice, 0, || self.state)?;
            
            // Hash c1/c2 to field elements
            let c1_scalar = self.c1_bytes.map(|bytes| {
                let mut hasher = blake2b_simd::Params::new().hash_length(64).to_state();
                hasher.update(b"c1");
                hasher.update(&bytes);
                hash_to_fr(hasher.finalize().as_array())
            });

            let c2_scalar = self.c2_bytes.map(|bytes| {
                let mut hasher = blake2b_simd::Params::new().hash_length(64).to_state();
                hasher.update(b"c2");
                hasher.update(&bytes);
                hash_to_fr(hasher.finalize().as_array())
            });

            let c1_cell = region.assign_advice(|| "c1", config.advice, 1, || c1_scalar)?;
            let c2_cell = region.assign_advice(|| "c2", config.advice, 2, || c2_scalar)?;
            
            Ok((c1_cell, c2_cell))
        })?;
        
        // Constrain to instance column
        layouter.constrain_instance(c1_cell.cell(), config.instance, 0)?;
        layouter.constrain_instance(c2_cell.cell(), config.instance, 1)?;
        
        Ok(())
    }
}

////////////////////////////////////////////////////////////////////////////
/// Cryptographic Structures

//Halo2 setup parameters (KZG commitments, proving/verifying keys)
#[derive(Clone)]
pub struct Halo2Setup { params: ParamsKZG<Bn256>, pk: ProvingKey<G1Affine>, vk: VerifyingKey<G1Affine> }

//Serialization wrapper macro for Ristretto types
macro_rules! impl_serde_wrapper {
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
                let bytes = Vec::<u8>::deserialize(d)?;
                if bytes.len() != $size { return Err(serde::de::Error::custom(concat!("Invalid ", stringify!($name), " length"))); }
                let mut arr = [0u8; $size];
                arr.copy_from_slice(&bytes);
                Ok($name($from(arr)))
            }
        }
        impl From<$inner> for $name { fn from(v: $inner) -> Self { $name(v) } }
        impl From<$name> for $inner { fn from(v: $name) -> Self { v.0 } }
    };
}
impl_serde_wrapper!(SerializableCompressedRistretto, CompressedRistretto, 32, CompressedRistretto);
impl_serde_wrapper!(SerializableScalar, Scalar, 32, Scalar::from_bytes_mod_order);

//Device proof with Halo2 ZK proof and ElGamal encryption
#[serde_as]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceProof {
    pub device_id: u32, //Device identifier
    pub timestamp: u64, //Creation time
    pub elgamal_c1: SerializableCompressedRistretto, //ElGamal c1
    pub elgamal_c2: SerializableCompressedRistretto, //ElGamal c2
    pub halo2_proof: Vec<u8>, //Halo2 binary state proof
    #[serde_as(as = "Bytes")]
    pub signature: [u8; 64], //ECDSA signature
}

//Partial decryption with Schnorr proof
#[serde_as]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PartialDecryption {
    pub device_id: u32, //Device identifier
    pub timestamp: u64, //Creation time
    pub partial: SerializableCompressedRistretto, //Partial decryption point
    pub proof: SchnorrProof, //Discrete log equality proof
    #[serde_as(as = "Bytes")]
    pub signature: [u8; 64], //ECDSA signature
}

//Schnorr proof for discrete log equality (Fiat-Shamir)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SchnorrProof { pub commitment: SerializableCompressedRistretto, pub response: SerializableScalar }
impl SchnorrProof {
    fn prove_dlog_equality(secret: &Scalar, sum_c1: &RistrettoPoint, partial: &RistrettoPoint, ts: u64, id: u32) -> Self {
        let r = Scalar::random(&mut OsRng); //Random nonce
        let commitment = sum_c1 * r; //Commitment = r*sum_c1
        let challenge = Self::challenge(&sum_c1, &partial, &commitment, ts, id); //Fiat-Shamir challenge
        let response = r + challenge * secret; //Response = r + c*x
        Self { commitment: commitment.compress().into(), response: response.into() }
    }
    fn verify_dlog_equality(&self, sum_c1: &RistrettoPoint, partial: &RistrettoPoint, ts: u64, id: u32) -> bool {
        let commitment = match self.commitment.0.decompress() { Some(c) => c, _none => return false };
        let challenge = Self::challenge(&sum_c1, &partial, &commitment, ts, id);
        sum_c1 * self.response.0 == commitment + partial * challenge //Verify equation
    }
    fn challenge(sum_c1: &RistrettoPoint, partial: &RistrettoPoint, commitment: &RistrettoPoint, ts: u64, id: u32) -> Scalar {
        let mut t = Transcript::new(b"schnorr-dlog-equality"); //Merlin transcript for domain separation
        t.append_u64(b"timestamp", ts); //Bind timestamp (replay protection)
        t.append_u64(b"device", id as u64); //Bind device ID (replay protection)
        t.append_message(b"sum_c1", sum_c1.compress().as_bytes()); //Bind state
        t.append_message(b"partial", partial.compress().as_bytes()); //Bind state
        t.append_message(b"commitment", commitment.compress().as_bytes()); //Bind state
        let mut bytes = [0u8; 64];
        t.challenge_bytes(b"challenge", &mut bytes); //Deterministic challenge derivation
        Scalar::from_bytes_mod_order_wide(&bytes)
    }
}

////////////////////////////////////////////////////////////////////////////
/// IoT Device

pub struct IoTDevice {
    pub id: u32, //Device ID
    pub frost_key_package: frost::keys::KeyPackage, //FROST private key share
    pub group_public: frost::keys::PublicKeyPackage, //FROST group public key
    pub signing_key: SigningKey, //ECDSA signing key
    pub peer_keys: HashMap<u32, SigSignKey>, //Peer public keys
    pub received_proofs: HashMap<u32, DeviceProof>, //Received device proofs
    pub received_partials: HashMap<u32, PartialDecryption>, //Received partial decryptions
    pub current_aggregate_c1: Option<RistrettoPoint>, //Sum of ElGamal c1
    pub current_aggregate_c2: Option<RistrettoPoint>, //Sum of ElGamal c2
    halo2_setup: Halo2Setup, //Halo2 proving/verifying setup
    pub threshold: usize, //Threshold for decryption
    peer_rates: HashMap<u32, (u64, u32)>, //Rate limiting per peer
    last_recompute: u64, //Last aggregate recomputation time
}
impl IoTDevice {
    //Constructor
    pub fn new(id: u32, threshold: usize, key_package: frost::keys::KeyPackage, public_package: frost::keys::PublicKeyPackage, peer_keys: HashMap<u32, SigSignKey>, halo2_setup: Halo2Setup) -> Self {
        Self {
            id, frost_key_package: key_package, group_public: public_package, //FROST keys
            signing_key: SigningKey::generate(&mut OsRng), peer_keys, //Random signing key
            received_proofs: HashMap::new(), received_partials: HashMap::new(), //Empty maps
            current_aggregate_c1: None, current_aggregate_c2: None, //No aggregate yet
            halo2_setup, threshold, //Halo2 setup and threshold
            peer_rates: HashMap::new(), last_recompute: 0, //Empty rate limits
        }
    }
    //Generate proof for binary state (0 or 1)
    pub fn generate_proof(&self, state: u8) -> Result<DeviceProof, AggError> {
        if state > 1 { return Err(AggError::CryptoError("State must be 0 or 1".into())); }
        let (ts, mut r, g) = (current_timestamp(), Scalar::random(&mut OsRng), RISTRETTO_BASEPOINT_POINT);
        let h = frost_pubkey_to_point(&self.group_public.verifying_key())?; //Get public key
        let (c1, c2) = (g * r, g * Scalar::from(state as u64) + h * r); //ElGamal encryption
        //Build Halo2 circuit with state
        let circuit = BinaryStateCircuit { state: Value::known(Halo2Fr::from(state as u64)), c1_bytes: Value::known(*c1.compress().as_bytes()), c2_bytes: Value::known(*c2.compress().as_bytes())};
        //Generate Halo2 proof
        let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);
        let mut hasher = blake2b_simd::Params::new().hash_length(64).to_state();
        hasher.update(b"c1");
        hasher.update(c1.compress().as_bytes());
        let c1_instance = hash_to_fr(hasher.finalize().as_array());

        hasher = blake2b_simd::Params::new().hash_length(64).to_state();
        hasher.update(b"c2");
        hasher.update(c2.compress().as_bytes());
        let c2_instance = hash_to_fr(hasher.finalize().as_array());

        let instances = vec![c1_instance, c2_instance];
        create_proof::<KZGCommitmentScheme<Bn256>, ProverSHPLONK<'_, Bn256>, _, _, _, _>(
            &self.halo2_setup.params, 
            &self.halo2_setup.pk, 
            &[circuit], 
            &[&[&instances[..]]], 
            OsRng, 
            &mut transcript
            ).map_err(|e| { 
                r.zeroize(); 
                AggError::CryptoError(format!("Halo2 prove failed: {:?}", e)) 
        })?;
        r.zeroize(); //Securely delete nonce
        //Construct and return proof
        Ok(DeviceProof {
            device_id: self.id, timestamp: ts,
            elgamal_c1: c1.compress().into(), elgamal_c2: c2.compress().into(),
            halo2_proof: transcript.finalize(),
            signature: self.sign_data(&[&ts.to_le_bytes(), &self.id.to_le_bytes(), c1.compress().as_bytes(), c2.compress().as_bytes()]),
        })
    }
    //Remove expired proofs and partials
    pub fn cleanup_expired_proofs(&mut self) {
        let thresh = current_timestamp().saturating_sub(PROOF_EXPIRATION_SECS);
        self.received_proofs.retain(|_, p| p.timestamp > thresh);
        self.received_partials.retain(|_, p| p.timestamp > thresh);
        self.maybe_recompute();
    }
    //Conditionally recompute aggregate
    fn maybe_recompute(&mut self) {
        let now = current_timestamp();
        if now >= self.last_recompute + RECOMPUTE_INTERVAL_SECS { self.recompute_aggregate(); self.last_recompute = now; }
    }
    //Recompute ElGamal aggregate
    fn recompute_aggregate(&mut self) {
        if self.received_proofs.is_empty() { self.current_aggregate_c1 = None; self.current_aggregate_c2 = None; }
        else {
            let (mut c1, mut c2) = (RistrettoPoint::identity(), RistrettoPoint::identity());
            for p in self.received_proofs.values() {
                if let (Some(p1), Some(p2)) = (p.elgamal_c1.0.decompress(), p.elgamal_c2.0.decompress()) { c1 += p1; c2 += p2; }
            }
            self.current_aggregate_c1 = Some(c1); self.current_aggregate_c2 = Some(c2);
        }
    }
    //Rate limiting check
    fn check_rate(&mut self, id: u32) -> Result<(), AggError> {
        let now = current_timestamp();
        let entry = self.peer_rates.entry(id).or_insert((now, 0));
        if now >= entry.0 + RATE_WINDOW_SECS { *entry = (now, 0); }
        if entry.1 >= MAX_MESSAGES_PER_WINDOW { return Err(AggError::RateLimited); }
        entry.1 += 1;
        Ok(())
    }
    //Receive and verify device proof
    pub fn receive_proof(&mut self, proof: DeviceProof) -> Result<(), AggError> {
        self.check_rate(proof.device_id)?; // Rate limit check
        let now = current_timestamp();
        if proof.timestamp + PROOF_EXPIRATION_SECS < now { return Err(AggError::ExpiredProof); }
        if self.received_proofs.get(&proof.device_id).map_or(false, |e| e.timestamp + PROOF_EXPIRATION_SECS > now) { 
            return Err(AggError::InvalidProof("Duplicate proof".into())); 
        }
        if proof.halo2_proof.len() > MAX_HALO2_BYTES { return Err(AggError::InvalidProof("Halo2 proof too large".into())); }
        
        // Verify signature
        let pubkey = self.peer_keys.get(&proof.device_id).ok_or(AggError::InvalidProof("Unknown device".into()))?;
        self.verify_sig(pubkey, &[&proof.timestamp.to_le_bytes(), &proof.device_id.to_le_bytes(), proof.elgamal_c1.0.as_bytes(), proof.elgamal_c2.0.as_bytes()], &proof.signature)?;
        
        // Reconstruct instance values from ElGamal ciphertext
        let mut hasher = blake2b_simd::Params::new().hash_length(64).to_state();
        hasher.update(b"c1");
        hasher.update(proof.elgamal_c1.0.as_bytes());
        let c1_instance = hash_to_fr(hasher.finalize().as_array());
        
        let mut hasher = blake2b_simd::Params::new().hash_length(64).to_state();
        hasher.update(b"c2");
        hasher.update(proof.elgamal_c2.0.as_bytes());
        let c2_instance = hash_to_fr(hasher.finalize().as_array());
        
        let instances = vec![c1_instance, c2_instance];
        
        // Verify Halo2 proof
        let strategy = SingleStrategy::new(&self.halo2_setup.params);
        let mut transcript = Blake2bRead::<_, G1Affine, Challenge255<_>>::init(&proof.halo2_proof[..]);
        verify_proof::<KZGCommitmentScheme<Bn256>, VerifierSHPLONK<'_, Bn256>, _, _, _>(
            &self.halo2_setup.params, 
            &self.halo2_setup.vk, 
            strategy, 
            &[&[&instances[..]]],
            &mut transcript
        ).map_err(|_| AggError::InvalidProof("Halo2 verification failed".into()))?;
        
        self.received_proofs.insert(proof.device_id, proof); // Store proof
        self.maybe_recompute();
        Ok(())
    }
    //Generate partial decryption
    pub fn generate_partial_decryption(&mut self) -> Result<PartialDecryption, AggError> {
        self.recompute_aggregate();
        let sum_c1 = self.current_aggregate_c1.ok_or(AggError::CryptoError("No aggregate".into()))?;
        let ts = current_timestamp();
        let mut secret = scalar_from_frost_signing(&self.frost_key_package.signing_share())?; //Get FROST secret
        let partial = sum_c1 * secret; //Compute partial = c1 * secret
        let proof = SchnorrProof::prove_dlog_equality(&secret, &sum_c1, &partial, ts, self.id); //Schnorr proof
        secret.zeroize(); //Securely delete secret
        Ok(PartialDecryption {
            device_id: self.id, timestamp: ts, partial: partial.compress().into(), proof,
            signature: self.sign_data(&[&ts.to_le_bytes(), &self.id.to_le_bytes(), partial.compress().as_bytes()]),
        })
    }
    //Receive and verify partial decryption
    pub fn receive_partial(&mut self, partial: PartialDecryption) -> Result<(), AggError> {
        self.check_rate(partial.device_id)?; //Rate limit
        if partial.timestamp + PROOF_EXPIRATION_SECS < current_timestamp() { return Err(AggError::ExpiredProof); } //Expiration
        let pubkey = self.peer_keys.get(&partial.device_id).ok_or(AggError::InvalidProof("Unknown device".into()))?;
        self.verify_sig(pubkey, &[&partial.timestamp.to_le_bytes(), &partial.device_id.to_le_bytes(), partial.partial.0.as_bytes()], &partial.signature)?; //Signature
        self.received_partials.insert(partial.device_id, partial);
        Ok(())
    }
    //Compute final aggregate using Lagrange interpolation
    pub fn compute_aggregate(&mut self) -> Result<(usize, usize), AggError> {
        self.recompute_aggregate();
        let thresh = current_timestamp().saturating_sub(PROOF_EXPIRATION_SECS);
        let valid_proofs: Vec<_> = self.received_proofs.values().filter(|p| p.timestamp > thresh).collect();
        if valid_proofs.is_empty() { return Ok((0, 0)); }
        let valid_partials: Vec<_> = self.received_partials.values().filter(|p| p.timestamp > thresh).collect();
        if valid_partials.len() < self.threshold { return Err(AggError::ThresholdNotMet); } //Check threshold
        let sum_c1 = self.current_aggregate_c1.ok_or(AggError::CryptoError("No aggregate".into()))?;
        let sum_c2 = self.current_aggregate_c2.ok_or(AggError::CryptoError("No aggregate".into()))?;
        //Verify Schnorr proofs and collect valid partials
        let mut verified = Vec::new();
        for p in valid_partials.iter().take(self.threshold) {
            let point = p.partial.0.decompress().ok_or(AggError::CryptoError("Invalid partial".into()))?;
            if !p.proof.verify_dlog_equality(&sum_c1, &point, p.timestamp, p.device_id) { return Err(AggError::InvalidProof(format!("Schnorr failed for device {}", p.device_id))); }
            verified.push((p.device_id, point));
        }
        //Lagrange interpolation
        let participants: Vec<Scalar> = verified.iter().map(|(id, _)| Scalar::from(*id as u64)).collect();
        let mut combined = RistrettoPoint::identity();
        for i in 0..verified.len() {
            let mut lambda = Scalar::one();
            for j in 0..verified.len() { if i != j { lambda *= -participants[j] * (participants[i] - participants[j]).invert(); } }
            combined += verified[i].1 * lambda;
        }
        //Extract discrete log
        Ok((bsgs_discrete_log(sum_c2 - combined, RISTRETTO_BASEPOINT_POINT)?, valid_proofs.len()))
    }
    //Sign data with ECDSA
    fn sign_data(&self, parts: &[&[u8]]) -> [u8; 64] {
        let mut data = Vec::new();
        for p in parts { data.extend_from_slice(p); }
        self.signing_key.sign(&data).to_bytes()
    }
    //Verify ECDSA signature
    fn verify_sig(&self, key: &SigSignKey, parts: &[&[u8]], sig: &[u8; 64]) -> Result<(), AggError> {
        let mut data = Vec::new();
        for p in parts { data.extend_from_slice(p); }
        let sig = Signature::try_from(&sig[..]).map_err(|_| AggError::InvalidProof("Invalid sig".into()))?;
        key.verify(&data, &sig).map_err(|_| AggError::InvalidProof("Sig failed".into()))
    }
}

////////////////////////////////////////////////////////////////////////////
/// Helper Functions

//Baby-step giant-step discrete log extraction
fn bsgs_discrete_log(target: RistrettoPoint, base: RistrettoPoint) -> Result<usize, AggError> {
    let m = ((MAX_DEVICES as f64).sqrt() as usize) + 1; //Step size
    let mut baby = Vec::with_capacity(m);
    let mut current = RistrettoPoint::identity();
    for _ in 0..m { baby.push(current.compress().to_bytes()); current += base; } //Baby steps
    let factor = base * Scalar::from(m as u64);
    let mut gamma = target;
    for j in 0..m { //Giant steps
        let gamma_bytes = gamma.compress().to_bytes();
        for (i, entry) in baby.iter().enumerate() {
            if entry.ct_eq(&gamma_bytes).unwrap_u8() == 1 {
                let result = j * m + i;
                if result <= MAX_DEVICES { return Ok(result); }
            }
        }
        gamma -= factor;
    }
    Err(AggError::CryptoError("Discrete log not found".into()))
}

//DKG setup for FROST threshold keys
pub fn setup_dkg(num: usize, threshold: usize) -> Result<Vec<(u32, frost::keys::KeyPackage, frost::keys::PublicKeyPackage)>, AggError> {
    let mut rng = OsRng;
    let mut r1_packages = BTreeMap::new();
    let mut r1_secrets = HashMap::new();
    //Round 1: Generate commitments
    for i in 1..=num {
        let id = frost::Identifier::try_from(i as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
        let (secret, package) = frost::keys::dkg::part1(id, num as u16, threshold as u16, &mut rng).map_err(|e| AggError::CryptoError(e.to_string()))?;
        r1_secrets.insert(i as u32, secret);
        r1_packages.insert(id, package);
    }
    //Round 2: Compute shares
    let mut r2_packages = HashMap::new();
    for (i, secret) in &r1_secrets {
        let mut received = r1_packages.clone();
        let id = frost::Identifier::try_from(*i as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
        received.remove(&id);
        let (r2_secret, packages) = frost::keys::dkg::part2(secret.clone(), &received).map_err(|e| AggError::CryptoError(e.to_string()))?;
        r2_packages.insert(*i, (r2_secret, packages));
    }
    //Round 3: Finalize keys
    let mut results = Vec::new();
    for i in 1..=num {
        let id = frost::Identifier::try_from(i as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
        let (r2_secret, _) = r2_packages.get(&(i as u32)).ok_or(AggError::DkgIncomplete)?;
        let mut received_r2 = BTreeMap::new();
        for (j, (_, packages)) in &r2_packages {
            if *j != i as u32 {
                if let Some(p) = packages.get(&id) {
                    let sender_id = frost::Identifier::try_from(*j as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
                    received_r2.insert(sender_id, p.clone());
                }
            }
        }
        let mut received_r1 = r1_packages.clone();
        received_r1.remove(&id);
        let (key_package, pubkey_package) = frost::keys::dkg::part3(r2_secret, &received_r1, &received_r2).map_err(|e| AggError::CryptoError(e.to_string()))?;
        results.push((i as u32, key_package, pubkey_package));
    }
    Ok(results)
}

//Load KZG parameters from trusted setup file
pub fn load_kzg_params() -> Result<ParamsKZG<Bn256>, AggError> {
    let params_path = Path::new(PARAMS_PATH);
    if !params_path.exists() { return Err(AggError::CryptoError(format!("KZG parameters not found at: {}\nPlease run 'cargo run --bin setup_params' first to download/generate parameters.", PARAMS_PATH))); }
    println!("Loading KZG parameters from: {}", PARAMS_PATH);
    let file = File::open(params_path).map_err(|e| AggError::CryptoError(format!("Failed to open params file: {}", e)))?;
    let mut reader = BufReader::new(file);
    let params = ParamsKZG::<Bn256>::read(&mut reader).map_err(|e| AggError::CryptoError(format!("Failed to read params: {}", e)))?;
    Ok(params)
}

//Setup Halo2 with KZG commitments
pub fn setup_halo2() -> Result<Halo2Setup, AggError> {
    let params = load_kzg_params()?; //Load pre-generated KZG parameters
    let empty_circuit = BinaryStateCircuit { state: Value::unknown(), c1_bytes: Value::unknown(), c2_bytes: Value::unknown()}; //Empty circuit for keygen
    let vk = keygen_vk(&params, &empty_circuit).map_err(|e| AggError::CryptoError(format!("VK generation failed: {:?}", e)))?; //Generate verifying key
    let pk = keygen_pk(&params, vk.clone(), &empty_circuit).map_err(|e| AggError::CryptoError(format!("PK generation failed: {:?}", e)))?; //Generate proving key
    println!("Halo2 KZG Setup Success (k={}, using trusted setup)", HALO2_K);
    Ok(Halo2Setup { params, pk, vk })
}

//Get the current time helper method
fn current_timestamp() -> u64 { std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs() }

//Turn public key to RistrettoPoint (convert to byte array, decompress)
fn frost_pubkey_to_point(key: &frost::VerifyingKey) -> Result<RistrettoPoint, AggError> {
    CompressedRistretto::from_slice(&key.serialize()).decompress()
        .ok_or_else(|| AggError::CryptoError("Invalid frost key".into()))
}

//Turn the FROST signing key into a Scalar for Risteretto Operations (convert to byte array, then into Scalar)
fn scalar_from_frost_signing(share: &frost::keys::SigningShare) -> Result<Scalar, AggError> {
    Ok(Scalar::from_bytes_mod_order(share.serialize().as_slice().try_into()
        .map_err(|_| AggError::CryptoError("Invalid share length".into()))?))
}

//Hash value to a field element
fn hash_to_fr(hash_64_bytes: &[u8; 64]) -> Halo2Fr {
    // Take first 32 bytes and reduce modulo the field order
    let mut bytes_32 = [0u8; 32];
    bytes_32.copy_from_slice(&hash_64_bytes[0..32]);
    
    // from_bytes expects little-endian, returns None if >= modulus
    // If None, XOR with second half and try again (simple reduction)
    match Halo2Fr::from_bytes(&bytes_32).into() {
        Some(fr) => fr,
        None => {
            // Simple reduction: XOR first 32 with last 32 bytes
            for i in 0..32 {
                bytes_32[i] ^= hash_64_bytes[32 + i];
            }
            Halo2Fr::from_bytes(&bytes_32).unwrap_or(Halo2Fr::zero())
        }
    }
}

////////////////////////////////////////////////////////////////////////////
/// Main Testing Method

fn main() -> Result<(), AggError> {
    println!("\n\nZK-DISPHASIA with Halo2 KZG ZK-SNARK\n");
    println!("Configuration:\nProof expiration: every {} seconds\n", PROOF_EXPIRATION_SECS);
    
    //DKG Setup
    let (num_devices, threshold, states) = (5, 3, [1u8, 0, 1, 1, 0]);
    println!("Setting up DKG for {} devices (threshold: {})...", num_devices, threshold);
    let dkg_results = setup_dkg(num_devices, threshold)?;
    println!("DKG Setup Success");
    
    //Halo2 Setup
    let halo2_setup = setup_halo2()?;

    //Create the Devices
    println!("Creating the Devices");
    let mut devices = Vec::new();
    let mut all_keys = HashMap::new();
    
    //Giving them Keys
    for (id, key_pkg, pub_pkg) in &dkg_results {
        let d = IoTDevice::new(*id, threshold, key_pkg.clone(), pub_pkg.clone(), 
                              HashMap::new(), halo2_setup.clone());
        all_keys.insert(*id, d.signing_key.verifying_key());
        devices.push(d);
    }
    //Sharing the Keys
    for d in devices.iter_mut() { 
        d.peer_keys = all_keys.clone(); 
    }
    println!("System initialized\n\nSimulating device states: {:?}", states);

    //Generating Proofs
    for (i, state) in states.iter().enumerate() {
        let proof = devices[i].generate_proof(*state)?;
        println!("  Device {} generated proof for state {}", 
                 i + 1, state);
        for (j, device) in devices.iter_mut().enumerate() {
            if let Err(e) = device.receive_proof(proof.clone()) {
                if i != j { 
                    println!("    Device {} rejected proof from {}: {}", j + 1, i + 1, e); 
                }
            }
        }
    }

    //Generating Partial Decryptions
    println!("\nGenerating partial decryptions:");
    for i in 0..threshold {
        if devices[i].received_proofs.len() >= num_devices {
            let partial = devices[i].generate_partial_decryption()?;
            println!("  Device {} generated partial", i + 1);
            for d in devices.iter_mut() { 
                d.receive_partial(partial.clone()).ok(); 
            }
        }
    }

    //Calculating Results
    println!("\nResults:");
    for d in &mut devices {
        match d.compute_aggregate() {
            Ok((sum, total)) => println!("  Device {}: sum = {}/{} devices", d.id, sum, total),
            Err(e) => println!("  Device {}: Error - {}", d.id, e),
        }
    }
    
    println!("\nSimulation Complete");
    Ok(())
}