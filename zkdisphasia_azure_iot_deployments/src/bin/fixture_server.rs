//This was made with AI Assistance

use serde::{Deserialize, Serialize}; //Serialize/deserialize
use std::collections::{HashMap, BTreeMap}; //Data structures
use std::sync::Arc; //Thread-safe reference counting
use actix_web::{web, App, HttpResponse, HttpServer, get, middleware}; //Web framework
use frost_ristretto255 as frost; //FROST threshold signatures
use ed25519_dalek::{SigningKey}; //Digital signatures
use rand::SeedableRng; //Random number generation
use rand_chacha::ChaCha20Rng; //ChaCha RNG
use curve25519_dalek_ng::{ristretto::{RistrettoPoint}, scalar::Scalar, traits::Identity, constants::RISTRETTO_BASEPOINT_POINT}; //Elliptic curve
use base64::{Engine as _, engine::general_purpose}; //Base64 encoding

//Import from the main library (assumed to be in the same crate)
use zk_disphasia_azure_test::common::{self, AggError, VerifiedCiphertext};
use zk_disphasia_azure_test::bulletproof;
use zk_disphasia_azure_test::snark;
use zk_disphasia_azure_test::stark;

//Network configurations to test
//const NETWORK_SIZES: &[usize] = &[5, 10, 20, 50, 100, 500, 1000, 2500, 5000, 10000]; //Test network sizes
const NETWORK_SIZES: &[usize] = &[5, 10, 20, 50]; //Test network sizes
const THRESHOLD_RATIOS: &[f64] = &[0.5, 0.67, 0.75]; //Threshold ratios

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ZKPType { Bulletproof, SNARK, STARK }

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifiedPartialData { pub device_id: u32, pub partial_bytes: Vec<u8>, pub aggregate_c1_bytes: [u8; 32], pub aggregate_c2_bytes: [u8; 32] }

impl std::fmt::Display for ZKPType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self { ZKPType::Bulletproof => write!(f, "bulletproof"), ZKPType::SNARK => write!(f, "snark"), ZKPType::STARK => write!(f, "stark") }
    }
}
impl std::str::FromStr for ZKPType {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() { "bulletproof" => Ok(ZKPType::Bulletproof), "snark" => Ok(ZKPType::SNARK), "stark" => Ok(ZKPType::STARK), _ => Err(format!("Unknown ZKP type: {}", s)) }
    }
}

//DKG CEREMONY STRUCTURES
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceOutput { pub device_id: u32, pub key_package: Vec<u8>, pub public_package: Vec<u8>, pub signing_pubkey: [u8; 32] } //Output from a completed DKG ceremony for one device

#[derive(Debug, Clone)]
pub struct DKGCeremony {
    pub n: usize, //Number of participants
    pub t: usize, //Threshold
    pub round1_packages: HashMap<u32, Vec<Vec<u8>>>, //For DKG Phase 2: (n-1) round1 packages per device
    pub round2_packages: HashMap<u32, Vec<Vec<u8>>>, //For DKG Phase 3: (n-1) round2 packages per device
    pub all_round1: Vec<Vec<u8>>, //All round1 packages (for DKG Phase 3)
    pub completed_dkg: Vec<DeviceOutput> //Final completed DKG outputs for each device
}

//ZKP-SPECIFIC ARTIFACTS
#[derive(Debug, Clone)]
pub struct ZKPArtifacts {
    pub zkp_type: ZKPType,
    pub n: usize,
    pub t: usize,
    pub sample_proof: Vec<u8>, //For Proof Verify: Sample proof from a peer (state=1)
    pub verified_ciphertexts: Vec<Vec<u8>>, //For Partial Gen: Mock aggregate from all n devices
    pub sample_partial: VerifiedPartialData, //For Partial Verify: Sample partial from a peer
    pub threshold_partials: Vec<Vec<u8>> //For Aggregate Compute: t partials for threshold decryption
}

//MAIN CACHE STRUCTURE
pub struct FixtureCache {
    dkg_ceremonies: HashMap<(usize, usize), DKGCeremony>, //DKG ceremonies: (n, t) -> DKGCeremony
    zkp_artifacts: HashMap<(ZKPType, usize, usize), ZKPArtifacts>, //ZKP artifacts: (zkp_type, n, t) -> ZKPArtifacts
    halo2_setup: Option<snark::Halo2Setup> //Halo2 setup (shared across all SNARK tests)
}

impl FixtureCache {
    pub fn new() -> Self { Self { dkg_ceremonies: HashMap::new(), zkp_artifacts: HashMap::new(), halo2_setup: None } } //Initialize empty cache
    pub fn initialize() -> Result<Self, AggError> { //Main initialization - pre-compute all fixtures
        println!("=== Fixture Server Initialization ===");
        println!("Pre-computing all fixtures (this takes ~30 minutes)...\n");
        let start_time = std::time::Instant::now();
        let mut cache = Self::new();
        //Step 1: Load Halo2 setup for SNARK tests
        println!("Loading Halo2 trusted setup...");
        cache.halo2_setup = Some(snark::setup_halo2()?);
        println!("✓ Halo2 setup loaded\n");
        //Step 2: Pre-compute DKG ceremonies for all (n, t) combinations
        let total_configs = NETWORK_SIZES.len() * THRESHOLD_RATIOS.len();
        let mut config_num = 0;
        for &n in NETWORK_SIZES {
            for &t_ratio in THRESHOLD_RATIOS {
                let t = (n as f64 * t_ratio).ceil() as usize;
                config_num += 1;
                println!("[{}/{}] Computing DKG ceremony for n={}, t={}...", config_num, total_configs, n, t);
                let ceremony = Self::run_complete_dkg_ceremony(n, t)?;
                cache.dkg_ceremonies.insert((n, t), ceremony.clone());
                //Step 3: For each ZKP type, generate artifacts
                for zkp_type in [ZKPType::Bulletproof, ZKPType::SNARK, ZKPType::STARK] {
                    println!("  Generating {} artifacts...", zkp_type);
                    let artifacts = Self::generate_zkp_artifacts(zkp_type, &ceremony, cache.halo2_setup.as_ref())?;
                    cache.zkp_artifacts.insert((zkp_type, n, t), artifacts);
                }
                println!("  ✓ Completed n={}, t={}\n", n, t);
            }
        }
        let elapsed = start_time.elapsed();
        let size_mb = cache.estimate_size_mb();
        println!("=== Initialization Complete ===");
        println!("Total time: {:.2} minutes", elapsed.as_secs_f64() / 60.0);
        println!("Total cache size: {:.2} GB", size_mb / 1024.0);
        println!("Ready to serve requests!\n");
        Ok(cache)
    }
    fn run_complete_dkg_ceremony(n: usize, t: usize) -> Result<DKGCeremony, AggError> {
        let mut completed_dkg = Vec::new();
        let mut round1_for_devices = HashMap::new();
        let mut round2_for_devices = HashMap::new();
        let mut r1_secrets = Vec::new();
        let mut r1_packages = BTreeMap::new();
        for i in 1..=n {
            let device_id = i as u32;
            let (secret, package) = common::dkg_phase1(device_id, n, t)?;
            let id = frost::Identifier::try_from(i as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
            r1_secrets.push((device_id, secret));
            r1_packages.insert(id, package);
        }
        let mut r2_secrets = Vec::new();
        let mut r2_packages_map = BTreeMap::new();
        for (device_id, r1_secret) in &r1_secrets {
            let my_id = frost::Identifier::try_from(*device_id as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
            let mut received_r1 = r1_packages.clone();
            received_r1.remove(&my_id);
            let (r2_secret, r2_packages) = common::dkg_phase2(r1_secret.clone(), &received_r1)?;
            r2_secrets.push((*device_id, r2_secret));
            r2_packages_map.insert(*device_id, r2_packages);
        }
        for (device_id, r2_secret) in &r2_secrets {
            let my_id = frost::Identifier::try_from(*device_id as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
            let mut received_r2 = BTreeMap::new();
            for (other_id, packages) in &r2_packages_map {
                if other_id != device_id {
                    if let Some(pkg) = packages.get(&my_id) {
                        let other_frost_id = frost::Identifier::try_from(*other_id as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
                        received_r2.insert(other_frost_id, pkg.clone());
                    }
                }
            }
            let mut all_r1 = r1_packages.clone();
            all_r1.remove(&my_id);
            let (key_package, public_key_package) = common::dkg_phase3(&r2_secret, &all_r1, &received_r2)?;
            let sig_seed = Self::generate_seed(b"signing_key", n, t, *device_id, 0);
            let mut sig_rng = ChaCha20Rng::from_seed(sig_seed);
            let signing_key = SigningKey::generate(&mut sig_rng);
            completed_dkg.push(DeviceOutput {
                device_id: *device_id,
                key_package: key_package.serialize().map_err(|e| AggError::CryptoError(format!("Serialize failed: {:?}", e)))?.to_vec(),
                public_package: public_key_package.serialize().map_err(|e| AggError::CryptoError(format!("Serialize failed: {:?}", e)))?.to_vec(),
                signing_pubkey: signing_key.verifying_key().to_bytes()
            });
            let mut r1_for_device = Vec::new();
            for (frost_id, pkg) in &r1_packages {
                if frost_id != &my_id {
                    r1_for_device.push(pkg.serialize().map_err(|e| AggError::CryptoError(format!("Serialize failed: {:?}", e)))?.to_vec());
                }
            }
            round1_for_devices.insert(*device_id, r1_for_device);
            let mut r2_for_device = Vec::new();
            for (_frost_id, pkg) in &received_r2 {
                r2_for_device.push(pkg.serialize().map_err(|e| AggError::CryptoError(format!("Serialize failed: {:?}", e)))?.to_vec());
            }
            round2_for_devices.insert(*device_id, r2_for_device);
        }
        let all_round1: Vec<Vec<u8>> = r1_packages.values().map(|pkg| pkg.serialize().map(|s| s.to_vec())).collect::<Result<Vec<_>, _>>().map_err(|e| AggError::CryptoError(format!("Serialize failed: {:?}", e)))?;
        Ok(DKGCeremony {
            n,
            t,
            round1_packages: round1_for_devices,
            round2_packages: round2_for_devices,
            all_round1,
            completed_dkg
        })
    }
    fn generate_zkp_artifacts(zkp_type: ZKPType, ceremony: &DKGCeremony, halo2_setup: Option<&snark::Halo2Setup>) -> Result<ZKPArtifacts, AggError> { //Generate ZKP-specific artifacts for testing
        let n = ceremony.n;
        let t = ceremony.t;
        //Step 1: Create verified ciphertexts from all n devices (alternating states 0,1)
        let mut verified_ciphertexts_raw = Vec::new();
        let public_package = frost::keys::PublicKeyPackage::deserialize(&ceremony.completed_dkg[0].public_package).map_err(|e| AggError::CryptoError(format!("PublicKeyPackage deser: {:?}", e)))?;
        let h = common::frost_to_point(&public_package.verifying_key())?;
        let g = RISTRETTO_BASEPOINT_POINT;
        for (i, device_output) in ceremony.completed_dkg.iter().enumerate() {
            let state = (i % 2) as u8;
            let device_id = device_output.device_id;
            let r_seed = Self::generate_seed(b"ciphertext_r", n, t, device_id, state as u32);
            let mut r_rng = ChaCha20Rng::from_seed(r_seed);
            let mut r_bytes = [0u8; 32];
            use rand::RngCore;
            r_rng.fill_bytes(&mut r_bytes);
            let r = Scalar::from_bytes_mod_order(r_bytes);
            let c1 = g * r;
            let c2 = g * Scalar::from(state as u64) + h * r;
            let ts = common::timestamp();
            let verified_ct = VerifiedCiphertext { timestamp: ts, c1, c2 };
            let ct_bytes = bincode::serialize(&verified_ct).map_err(|e| AggError::CryptoError(format!("VerifiedCT serialize: {}", e)))?;
            verified_ciphertexts_raw.push(ct_bytes);
        }
        //Step 2: Generate sample proof (from device 1, state=1)
        let sample_device_id = 1u32;
        let sample_state = 1u8;
        let sample_proof = Self::generate_single_proof(zkp_type, ceremony, halo2_setup, sample_device_id, sample_state)?;
        //Step 3: Generate partials from first t devices
        let mut threshold_partials = Vec::new();
        for i in 0..t {
            let device_id = (i + 1) as u32;
            let partial = Self::generate_single_partial(zkp_type, ceremony, halo2_setup, device_id, &verified_ciphertexts_raw)?;
            threshold_partials.push(partial);
        }
        //Step 4: Compute aggregate points for partial verification
        let mut aggregate_c1 = RistrettoPoint::identity();
        let mut aggregate_c2 = RistrettoPoint::identity();
        for ct_bytes in &verified_ciphertexts_raw {
            let ct: VerifiedCiphertext = bincode::deserialize(ct_bytes).map_err(|e| AggError::CryptoError(format!("CT deser: {}", e)))?;
            aggregate_c1 += ct.c1;
            aggregate_c2 += ct.c2;
        }
        //Step 5: Create VerifiedPartialData with pre-computed aggregate
        let sample_partial = VerifiedPartialData { device_id: 1, partial_bytes: threshold_partials[0].clone(), aggregate_c1_bytes: *aggregate_c1.compress().as_bytes(), aggregate_c2_bytes: *aggregate_c2.compress().as_bytes() };
        Ok(ZKPArtifacts { zkp_type, n, t, sample_proof, verified_ciphertexts: verified_ciphertexts_raw, sample_partial, threshold_partials })
    }
    fn generate_single_proof(zkp_type: ZKPType, ceremony: &DKGCeremony, halo2_setup: Option<&snark::Halo2Setup>, device_id: u32, state: u8) -> Result<Vec<u8>, AggError> { //Generate a single proof for testing
        let device_output = ceremony.completed_dkg.iter().find(|d| d.device_id == device_id).ok_or_else(|| AggError::CryptoError("Device not found".into()))?;
        let key_package = frost::keys::KeyPackage::deserialize(&device_output.key_package).map_err(|e| AggError::CryptoError(format!("KeyPackage deser: {:?}", e)))?;
        let public_package = frost::keys::PublicKeyPackage::deserialize(&device_output.public_package).map_err(|e| AggError::CryptoError(format!("PublicKeyPackage deser: {:?}", e)))?;
        let sig_seed = Self::generate_seed(b"signing_key", ceremony.n, ceremony.t, device_id, 0);
        let mut sig_rng = ChaCha20Rng::from_seed(sig_seed);
        let signing_key = SigningKey::generate(&mut sig_rng);
        let mut all_signing_keys = HashMap::new();
        for d in &ceremony.completed_dkg {
            let s_seed = Self::generate_seed(b"signing_key", ceremony.n, ceremony.t, d.device_id, 0);
            let mut s_rng = ChaCha20Rng::from_seed(s_seed);
            let s_key = SigningKey::generate(&mut s_rng);
            all_signing_keys.insert(d.device_id, s_key.verifying_key());
        }
        let proof_bytes = match zkp_type {
            ZKPType::Bulletproof => { let device = bulletproof::IoTDevice::new(device_id, ceremony.t, key_package, public_package, all_signing_keys, Some(signing_key))?; let proof = device.generate_proof(state)?; bincode::serialize(&proof).map_err(|e| AggError::CryptoError(format!("Proof serialize: {}", e)))? },
            ZKPType::SNARK => { let setup = halo2_setup.ok_or_else(|| AggError::CryptoError("Halo2 setup not available".into()))?; let device = snark::IoTDevice::new(device_id, ceremony.t, key_package, public_package, all_signing_keys, setup.clone(), Some(signing_key))?; let proof = device.generate_proof(state)?; bincode::serialize(&proof).map_err(|e| AggError::CryptoError(format!("Proof serialize: {}", e)))? },
            ZKPType::STARK => { let device = stark::IoTDevice::new(device_id, ceremony.t, key_package, public_package, all_signing_keys, Some(signing_key))?; let proof = device.generate_proof(state)?; bincode::serialize(&proof).map_err(|e| AggError::CryptoError(format!("Proof serialize: {}", e)))? }
        };
        Ok(proof_bytes)
    }
    fn generate_single_partial(_zkp_type: ZKPType, ceremony: &DKGCeremony, _halo2_setup: Option<&snark::Halo2Setup>, device_id: u32, verified_ciphertexts: &[Vec<u8>]) -> Result<Vec<u8>, AggError> { //Generate a single partial decryption for testing
        let device_output = ceremony.completed_dkg.iter().find(|d| d.device_id == device_id).ok_or_else(|| AggError::CryptoError("Device not found".into()))?;
        let key_package = frost::keys::KeyPackage::deserialize(&device_output.key_package).map_err(|e| AggError::CryptoError(format!("KeyPackage deser: {:?}", e)))?;
        let public_package = frost::keys::PublicKeyPackage::deserialize(&device_output.public_package).map_err(|e| AggError::CryptoError(format!("PublicKeyPackage deser: {:?}", e)))?;
        let sig_seed = Self::generate_seed(b"signing_key", ceremony.n, ceremony.t, device_id, 0);
        let mut sig_rng = ChaCha20Rng::from_seed(sig_seed);
        let signing_key = SigningKey::generate(&mut sig_rng);
        let mut cts_vec = Vec::new();
        for ct_bytes in verified_ciphertexts {
            let ct: VerifiedCiphertext = bincode::deserialize(ct_bytes).map_err(|e| AggError::CryptoError(format!("VerifiedCT deser: {}", e)))?;
            cts_vec.push(ct);
        }
        let partial = common::generate_partial_decryption(device_id, &key_package, &public_package, &signing_key, &cts_vec)?;
        let partial_bytes = bincode::serialize(&partial).map_err(|e| AggError::CryptoError(format!("Partial serialize: {}", e)))?;
        Ok(partial_bytes)
    }
    fn generate_seed(domain: &[u8], n: usize, t: usize, device_id: u32, extra: u32) -> [u8; 32] { //Generate deterministic seed for reproducibility
        use sha2::{Sha256, Digest};
        let mut hasher = Sha256::new();
        hasher.update(domain);
        hasher.update(&n.to_le_bytes());
        hasher.update(&t.to_le_bytes());
        hasher.update(&device_id.to_le_bytes());
        hasher.update(&extra.to_le_bytes());
        let result = hasher.finalize();
        let mut seed = [0u8; 32];
        seed.copy_from_slice(&result);
        seed
    }
    fn estimate_size_mb(&self) -> f64 { //Estimate cache size in MB
        let mut total_bytes = 0usize;
        for ceremony in self.dkg_ceremonies.values() {
            total_bytes += ceremony.completed_dkg.len() * 500;
            total_bytes += ceremony.all_round1.len() * 200;
            for pkgs in ceremony.round1_packages.values() { total_bytes += pkgs.len() * pkgs.get(0).map(|p| p.len()).unwrap_or(200); }
            for pkgs in ceremony.round2_packages.values() { total_bytes += pkgs.len() * pkgs.get(0).map(|p| p.len()).unwrap_or(200); }
        }
        for artifacts in self.zkp_artifacts.values() {
            total_bytes += artifacts.sample_proof.len();
            total_bytes += artifacts.verified_ciphertexts.len() * 100;
            total_bytes += artifacts.sample_partial.partial_bytes.len() + 64;
            total_bytes += artifacts.threshold_partials.len() * 100;
        }
        total_bytes as f64 / 1_048_576.0
    }
}

//API ENDPOINTS
#[get("/api/dkg/completed/{n}/{t}/{device_id}")]
async fn get_dkg_completed(path: web::Path<(usize, usize, u32)>, cache: web::Data<Arc<FixtureCache>>) -> HttpResponse { //Get completed DKG output for a specific device
    let (n, t, device_id) = path.into_inner();
    let ceremony = match cache.dkg_ceremonies.get(&(n, t)) { Some(c) => c, None => return HttpResponse::NotFound().json(serde_json::json!({"error": format!("DKG ceremony not found for n={}, t={}", n, t)})) };
    let device_output = match ceremony.completed_dkg.iter().find(|d| d.device_id == device_id) { Some(d) => d, None => return HttpResponse::NotFound().json(serde_json::json!({"error": format!("Device {} not found", device_id)})) };
    HttpResponse::Ok().json(device_output)
}

#[get("/api/dkg/round1/{n}/{t}/{device_id}")]
async fn get_dkg_round1(path: web::Path<(usize, usize, u32)>, cache: web::Data<Arc<FixtureCache>>) -> HttpResponse { //Get round1 packages for DKG Phase 2
    let (n, t, device_id) = path.into_inner();
    let ceremony = match cache.dkg_ceremonies.get(&(n, t)) { Some(c) => c, None => return HttpResponse::NotFound().json(serde_json::json!({"error": format!("DKG ceremony not found for n={}, t={}", n, t)})) };
    let packages = match ceremony.round1_packages.get(&device_id) { Some(p) => p, None => return HttpResponse::NotFound().json(serde_json::json!({"error": format!("Round1 packages not found for device {}", device_id)})) };
    let encoded: Vec<String> = packages.iter().map(|p| general_purpose::STANDARD.encode(p)).collect();
    HttpResponse::Ok().json(encoded)
}

#[get("/api/dkg/round2/{n}/{t}/{device_id}")]
async fn get_dkg_round2(path: web::Path<(usize, usize, u32)>, cache: web::Data<Arc<FixtureCache>>) -> HttpResponse { //Get round2 packages for DKG Phase 3
    let (n, t, device_id) = path.into_inner();
    let ceremony = match cache.dkg_ceremonies.get(&(n, t)) { Some(c) => c, None => return HttpResponse::NotFound().json(serde_json::json!({"error": format!("DKG ceremony not found for n={}, t={}", n, t)})) };
    let r1_packages = match ceremony.round1_packages.get(&device_id) { Some(p) => p, None => return HttpResponse::NotFound().json(serde_json::json!({"error": format!("Round1 packages not found for device {}", device_id)})) };
    let r2_packages = match ceremony.round2_packages.get(&device_id) { Some(p) => p, None => return HttpResponse::NotFound().json(serde_json::json!({"error": format!("Round2 packages not found for device {}", device_id)})) };
    let r1_encoded: Vec<String> = r1_packages.iter().map(|p| general_purpose::STANDARD.encode(p)).collect();
    let r2_encoded: Vec<String> = r2_packages.iter().map(|p| general_purpose::STANDARD.encode(p)).collect();
    HttpResponse::Ok().json(serde_json::json!({"round1_packages": r1_encoded, "round2_packages": r2_encoded}))
}

#[get("/api/proof/{zkp_type}/{n}/{t}")]
async fn get_sample_proof(path: web::Path<(String, usize, usize)>, cache: web::Data<Arc<FixtureCache>>) -> HttpResponse { //Get sample proof for verification testing
    let (zkp_str, n, t) = path.into_inner();
    let zkp_type = match zkp_str.parse::<ZKPType>() { Ok(z) => z, Err(e) => return HttpResponse::BadRequest().json(serde_json::json!({"error": e})) };
    let artifacts = match cache.zkp_artifacts.get(&(zkp_type, n, t)) { Some(a) => a, None => return HttpResponse::NotFound().json(serde_json::json!({"error": format!("ZKP artifacts not found for {:?}, n={}, t={}", zkp_type, n, t)})) };
    HttpResponse::Ok().content_type("application/octet-stream").body(artifacts.sample_proof.clone())
}

#[get("/api/ciphertexts/{zkp_type}/{n}/{t}")]
async fn get_ciphertexts(path: web::Path<(String, usize, usize)>, cache: web::Data<Arc<FixtureCache>>) -> HttpResponse { //Get verified ciphertexts for partial generation testing
    let (zkp_str, n, t) = path.into_inner();
    let zkp_type = match zkp_str.parse::<ZKPType>() { Ok(z) => z, Err(e) => return HttpResponse::BadRequest().json(serde_json::json!({"error": e})) };
    let artifacts = match cache.zkp_artifacts.get(&(zkp_type, n, t)) { Some(a) => a, None => return HttpResponse::NotFound().json(serde_json::json!({"error": format!("ZKP artifacts not found for {:?}, n={}, t={}", zkp_type, n, t)})) };
    let encoded: Vec<String> = artifacts.verified_ciphertexts.iter().map(|ct| general_purpose::STANDARD.encode(ct)).collect();
    HttpResponse::Ok().json(encoded)
}

#[get("/api/partial/{zkp_type}/{n}/{t}")]
async fn get_sample_partial(path: web::Path<(String, usize, usize)>, cache: web::Data<Arc<FixtureCache>>) -> HttpResponse { //Get sample partial for verification testing
    let (zkp_str, n, t) = path.into_inner();
    let zkp_type = match zkp_str.parse::<ZKPType>() { Ok(z) => z, Err(e) => return HttpResponse::BadRequest().json(serde_json::json!({"error": e})) };
    let artifacts = match cache.zkp_artifacts.get(&(zkp_type, n, t)) { Some(a) => a, None => return HttpResponse::NotFound().json(serde_json::json!({"error": format!("ZKP artifacts not found for {:?}, n={}, t={}", zkp_type, n, t)})) };
    HttpResponse::Ok().json(&artifacts.sample_partial)
}

#[get("/api/partials/{zkp_type}/{n}/{t}")]
async fn get_threshold_partials(path: web::Path<(String, usize, usize)>, cache: web::Data<Arc<FixtureCache>>) -> HttpResponse { //Get threshold partials for aggregate computation testing
    let (zkp_str, n, t) = path.into_inner();
    let zkp_type = match zkp_str.parse::<ZKPType>() { Ok(z) => z, Err(e) => return HttpResponse::BadRequest().json(serde_json::json!({"error": e})) };
    let artifacts = match cache.zkp_artifacts.get(&(zkp_type, n, t)) { Some(a) => a, None => return HttpResponse::NotFound().json(serde_json::json!({"error": format!("ZKP artifacts not found for {:?}, n={}, t={}", zkp_type, n, t)})) };
    let encoded: Vec<String> = artifacts.threshold_partials.iter().map(|p| general_purpose::STANDARD.encode(p)).collect();
    HttpResponse::Ok().json(encoded)
}

#[get("/health")]
async fn health_check(cache: web::Data<Arc<FixtureCache>>) -> HttpResponse { //Health check endpoint
    HttpResponse::Ok().json(serde_json::json!({"status": "ready", "cache_size_mb": cache.estimate_size_mb(), "dkg_ceremonies": cache.dkg_ceremonies.len(), "zkp_artifacts": cache.zkp_artifacts.len()}))
}

//MAIN SERVER
#[actix_web::main]
async fn main() -> std::io::Result<()> {
    println!("Starting Fixture Server...\n");
    let cache = match FixtureCache::initialize() { Ok(c) => Arc::new(c), Err(e) => { eprintln!("Failed to initialize cache: {}", e); std::process::exit(1); } }; //Initialize cache with all pre-computed artifacts
    let bind_addr = "0.0.0.0:8080";
    println!("Starting HTTP server on {}", bind_addr);
    HttpServer::new(move || { App::new().app_data(web::Data::new(cache.clone())).wrap(middleware::Logger::default()).service(get_dkg_completed).service(get_dkg_round1).service(get_dkg_round2).service(get_sample_proof).service(get_ciphertexts).service(get_sample_partial).service(get_threshold_partials).service(health_check) }).bind(bind_addr)?.run().await
}