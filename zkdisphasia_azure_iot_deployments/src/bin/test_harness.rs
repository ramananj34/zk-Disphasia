//This was made with AI Assistance

//! Test Harness for ZK-DISPHASIA Benchmarking - Optimized to avoid redundant testing of shared functions

use serde::{Deserialize, Serialize}; //Serialize/deserialize
use std::collections::{HashMap, BTreeMap}; //Data structures
use std::time::Instant; //Timing
use std::fs::{File, OpenOptions}; //File I/O
use std::io::Write; //Write trait
use clap::Parser; //CLI parsing
use reqwest::blocking::Client; //HTTP client
use base64::Engine; //Base64 encoding
use frost_ristretto255 as frost; //FROST threshold signatures
use ed25519_dalek::{VerifyingKey, SigningKey}; //Digital signatures

use zk_disphasia_azure_test::common::{self, VerifiedCiphertext, VerifiedPartial, PartialDecryption}; //Main library imports
use zk_disphasia_azure_test::bulletproof; //Bulletproof ZKP
use zk_disphasia_azure_test::snark; //SNARK ZKP
use zk_disphasia_azure_test::stark; //STARK ZKP

#[derive(Parser, Debug)]
#[command(author, version, about = "ZK-DISPHASIA Test Harness")]
struct Args { #[arg(long, default_value = "http://fixture-server:8080")] fixture_server: String, #[arg(long)] vm_profile: String, #[arg(long)] device_id: u32, #[arg(long, default_value = "/tmp/metrics.jsonl")] output: String } //Command-line arguments

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
enum ZKPType { Bulletproof, SNARK, STARK } //ZKP type enum

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
enum TestFunction { DKG1, DKG2, DKG3, PartialGen, PartialVerify, AggCompute, ProofGen, ProofVerify } //Function being tested (shared + ZKP-specific)

#[derive(Debug, Clone, Serialize, Deserialize)]
struct TestConfig { zkp_type: Option<ZKPType>, function: TestFunction, n: usize, t: usize, device_id: u32, run: usize } //Test configuration (zkp_type is None for shared functions)

#[derive(Debug, Serialize, Deserialize)]
struct Metrics { timestamp: String, vm_profile: String, vm_arch: String, test_config: TestConfig, status: String, failure_reason: Option<String>, wall_time_us: u128, cpu_time_user_us: u128, cpu_time_system_us: u128, peak_rss_kb: u64, initial_rss_kb: u64, delta_rss_kb: i64, disk_read_kb: u64, disk_write_kb: u64, cycles: Option<u64>, instructions: Option<u64>, cache_misses: Option<u64>, energy_estimate_joules: Option<f64>, output_size_bytes: Option<usize> } //Performance metrics

struct FixtureClient { base_url: String, client: Client } //Fixture server client
impl FixtureClient {
    fn new(base_url: String) -> Self { Self { base_url, client: Client::new() } }
    fn get_dkg_completed(&self, n: usize, t: usize, device_id: u32) -> Result<DeviceOutput, String> { let url = format!("{}/api/dkg/completed/{}/{}/{}", self.base_url, n, t, device_id); self.client.get(&url).send().map_err(|e| format!("HTTP error: {}", e))?.json().map_err(|e| format!("JSON error: {}", e)) }
    fn get_round1_packages(&self, n: usize, t: usize, device_id: u32) -> Result<Vec<Vec<u8>>, String> { let url = format!("{}/api/dkg/round1/{}/{}/{}", self.base_url, n, t, device_id); let encoded: Vec<String> = self.client.get(&url).send().map_err(|e| format!("HTTP error: {}", e))?.json().map_err(|e| format!("JSON error: {}", e))?; encoded.iter().map(|s| base64::engine::general_purpose::STANDARD.decode(s).map_err(|e| format!("Base64 error: {}", e))).collect() }
    fn get_round2_packages(&self, n: usize, t: usize, device_id: u32) -> Result<(Vec<Vec<u8>>, Vec<Vec<u8>>), String> { let url = format!("{}/api/dkg/round2/{}/{}/{}", self.base_url, n, t, device_id); #[derive(Deserialize)] struct Response { round1_packages: Vec<String>, round2_packages: Vec<String> } let resp: Response = self.client.get(&url).send().map_err(|e| format!("HTTP error: {}", e))?.json().map_err(|e| format!("JSON error: {}", e))?; let r1: Result<Vec<_>, _> = resp.round1_packages.iter().map(|s| base64::engine::general_purpose::STANDARD.decode(s).map_err(|e| format!("Base64 error: {}", e))).collect(); let r2: Result<Vec<_>, _> = resp.round2_packages.iter().map(|s| base64::engine::general_purpose::STANDARD.decode(s).map_err(|e| format!("Base64 error: {}", e))).collect(); Ok((r1?, r2?)) }
    fn get_sample_proof(&self, zkp_type: ZKPType, n: usize, t: usize) -> Result<Vec<u8>, String> { let zkp_str = match zkp_type { ZKPType::Bulletproof => "bulletproof", ZKPType::SNARK => "snark", ZKPType::STARK => "stark" }; let url = format!("{}/api/proof/{}/{}/{}", self.base_url, zkp_str, n, t); self.client.get(&url).send().map_err(|e| format!("HTTP error: {}", e))?.bytes().map(|b| b.to_vec()).map_err(|e| format!("HTTP error: {}", e)) }
    fn get_ciphertexts(&self, zkp_type: ZKPType, n: usize, t: usize) -> Result<Vec<VerifiedCiphertext>, String> { let zkp_str = match zkp_type { ZKPType::Bulletproof => "bulletproof", ZKPType::SNARK => "snark", ZKPType::STARK => "stark" }; let url = format!("{}/api/ciphertexts/{}/{}/{}", self.base_url, zkp_str, n, t); let encoded: Vec<String> = self.client.get(&url).send().map_err(|e| format!("HTTP error: {}", e))?.json().map_err(|e| format!("JSON error: {}", e))?; encoded.iter().map(|s| { let bytes = base64::engine::general_purpose::STANDARD.decode(s).map_err(|e| format!("Base64 error: {}", e))?; bincode::deserialize(&bytes).map_err(|e| format!("Bincode error: {}", e)) }).collect() }
    fn get_sample_partial(&self, zkp_type: ZKPType, n: usize, t: usize) -> Result<VerifiedPartialData, String> { let zkp_str = match zkp_type { ZKPType::Bulletproof => "bulletproof", ZKPType::SNARK => "snark", ZKPType::STARK => "stark" }; let url = format!("{}/api/partial/{}/{}/{}", self.base_url, zkp_str, n, t); self.client.get(&url).send().map_err(|e| format!("HTTP error: {}", e))?.json().map_err(|e| format!("JSON error: {}", e)) }
    fn get_threshold_partials(&self, zkp_type: ZKPType, n: usize, t: usize) -> Result<Vec<PartialDecryption>, String> { let zkp_str = match zkp_type { ZKPType::Bulletproof => "bulletproof", ZKPType::SNARK => "snark", ZKPType::STARK => "stark" }; let url = format!("{}/api/partials/{}/{}/{}", self.base_url, zkp_str, n, t); let encoded: Vec<String> = self.client.get(&url).send().map_err(|e| format!("HTTP error: {}", e))?.json().map_err(|e| format!("JSON error: {}", e))?; encoded.iter().map(|s| { let bytes = base64::engine::general_purpose::STANDARD.decode(s).map_err(|e| format!("Base64 error: {}", e))?; bincode::deserialize(&bytes).map_err(|e| format!("Bincode error: {}", e)) }).collect() }
}

#[derive(Debug, Deserialize)]
#[allow(dead_code)]
struct DeviceOutput { device_id: u32, key_package: Vec<u8>, public_package: Vec<u8>, signing_pubkey: [u8; 32] } //DKG ceremony output for one device

#[derive(Debug, Deserialize)]
#[allow(dead_code)]
struct VerifiedPartialData { device_id: u32, partial_bytes: Vec<u8>, aggregate_c1_bytes: [u8; 32], aggregate_c2_bytes: [u8; 32] } //Partial with pre-computed aggregate

struct TestRunner { fixture_client: FixtureClient, output_file: File, vm_profile: String, device_id: u32, halo2_setup: Option<snark::Halo2Setup>, peer_keys_cache: HashMap<(usize, usize), HashMap<u32, VerifyingKey>> } //Main test runner with caching
impl TestRunner {
    fn new(args: &Args) -> Result<Self, Box<dyn std::error::Error>> { let halo2_setup = if std::path::Path::new("./trusted_setup/kzg_bn254_5.params").exists() { println!("Loading Halo2 setup..."); Some(snark::setup_halo2()?) } else { println!("Warning: Halo2 params not found, SNARK tests will fail"); None }; let output_file = OpenOptions::new().create(true).append(true).open(&args.output)?; Ok(Self { fixture_client: FixtureClient::new(args.fixture_server.clone()), output_file, vm_profile: args.vm_profile.clone(), device_id: args.device_id, halo2_setup, peer_keys_cache: HashMap::new() }) }
    fn get_cached_peer_keys(&mut self, n: usize, t: usize) -> Result<HashMap<u32, VerifyingKey>, Box<dyn std::error::Error>> { if let Some(cached) = self.peer_keys_cache.get(&(n, t)) { return Ok(cached.clone()); } let mut peer_keys = HashMap::new(); for i in 1..=n { let dev_out = self.fixture_client.get_dkg_completed(n, t, i as u32)?; let vk = VerifyingKey::from_bytes(&dev_out.signing_pubkey)?; peer_keys.insert(i as u32, vk); } self.peer_keys_cache.insert((n, t), peer_keys.clone()); Ok(peer_keys) } //Fetch and cache peer signing keys
    fn run_all_tests(&mut self) { //Run all tests with optimized structure (shared functions once, ZKP-specific per type)
        let network_sizes = vec![5, 10, 20, 50]; //let network_sizes = vec![5, 10, 20, 50, 100, 500, 1000, 2500, 5000, 10000];
        let threshold_ratios = vec![0.5, 0.67, 0.75];
        let shared_functions = vec![TestFunction::DKG1, TestFunction::DKG2, TestFunction::DKG3, TestFunction::PartialGen, TestFunction::PartialVerify, TestFunction::AggCompute]; //Shared functions (tested once per n, t)
        let zkp_functions = vec![TestFunction::ProofGen, TestFunction::ProofVerify]; //ZKP-specific functions (tested per zkp_type, n, t)
        let zkp_types = vec![ZKPType::Bulletproof, ZKPType::SNARK, ZKPType::STARK];
        let mut test_count = 0;
        let total_tests = (network_sizes.len() * threshold_ratios.len() * shared_functions.len() * 30) + (zkp_types.len() * network_sizes.len() * threshold_ratios.len() * zkp_functions.len() * 30);
        println!("=== Starting Test Suite ===\nVM Profile: {}\nTotal tests to run: {}\n", self.vm_profile, total_tests);
        let mut success_count = 0; let mut failure_count = 0;
        println!("Testing shared functions (DKG, Partial, Aggregate)..."); //Test shared functions (no ZKP type needed)
        for n in &network_sizes { for t_ratio in &threshold_ratios { let t = (*n as f64 * t_ratio).ceil() as usize; for function in &shared_functions { for run in 1..=30 { test_count += 1; let config = TestConfig { zkp_type: None, function: *function, n: *n, t, device_id: self.device_id, run }; println!("[{}/{}] {:?} n={} t={} run={}", test_count, total_tests, function, n, t, run); match self.run_single_test(&config) { Ok(metrics) => { self.write_metrics(&metrics); if metrics.status == "SUCCESS" { success_count += 1; } else { failure_count += 1; } } Err(e) => { eprintln!("  Error: {}", e); failure_count += 1; } } } } } }
        println!("\nTesting ZKP-specific functions (ProofGen, ProofVerify)..."); //Test ZKP-specific functions
        for zkp_type in &zkp_types { println!("\n--- Testing {:?} ---", zkp_type); for n in &network_sizes { for t_ratio in &threshold_ratios { let t = (*n as f64 * t_ratio).ceil() as usize; for function in &zkp_functions { for run in 1..=30 { test_count += 1; let config = TestConfig { zkp_type: Some(*zkp_type), function: *function, n: *n, t, device_id: self.device_id, run }; println!("[{}/{}] {:?} {:?} n={} t={} run={}", test_count, total_tests, zkp_type, function, n, t, run); match self.run_single_test(&config) { Ok(metrics) => { self.write_metrics(&metrics); if metrics.status == "SUCCESS" { success_count += 1; } else { failure_count += 1; } } Err(e) => { eprintln!("  Error: {}", e); failure_count += 1; } } } } } } }
        println!("\n=== Test Suite Complete ===\nTotal tests: {}\nSuccesses: {}\nFailures: {}\nSuccess rate: {:.1}%", test_count, success_count, failure_count, (success_count as f64 / test_count as f64) * 100.0);
    }
    fn run_single_test(&mut self, config: &TestConfig) -> Result<Metrics, Box<dyn std::error::Error>> { //Run a single test with full instrumentation
        if config.run <= 2 { let _ = self.run_function(config); let _ = self.run_function(config); std::thread::sleep(std::time::Duration::from_millis(10)); } //Warm up CPU caches and JIT
        let initial_rss = Self::get_rss_kb()?; let wall_start = Instant::now(); let result = self.run_function(config); let wall_time_us = wall_start.elapsed().as_micros();
        let peak_rss = Self::get_peak_rss_kb()?; let delta_rss = peak_rss as i64 - initial_rss as i64; let (user_time_us, system_time_us) = Self::get_cpu_times()?; let (disk_read_kb, disk_write_kb) = Self::get_io_stats()?;
        let cpu_freq = match std::env::consts::ARCH { "x86_64" => 2_500_000_000u64, "aarch64" => 2_000_000_000u64, _ => 2_000_000_000u64 }; //Estimate CPU cycles and energy
        let total_cpu_us = user_time_us + system_time_us; let estimated_cycles = (total_cpu_us as u64) * (cpu_freq / 1_000_000); let energy_joules = estimated_cycles as f64 * 0.5e-9;
        let mut metrics = Metrics { timestamp: Self::timestamp_iso8601(), vm_profile: self.vm_profile.clone(), vm_arch: std::env::consts::ARCH.to_string(), test_config: config.clone(), status: if result.is_ok() { "SUCCESS".to_string() } else { "FAILED".to_string() }, failure_reason: result.as_ref().err().map(|e| e.to_string()), wall_time_us, cpu_time_user_us: user_time_us, cpu_time_system_us: system_time_us, peak_rss_kb: peak_rss, initial_rss_kb: initial_rss, delta_rss_kb: delta_rss, disk_read_kb, disk_write_kb, cycles: Some(estimated_cycles), instructions: None, cache_misses: None, energy_estimate_joules: Some(energy_joules), output_size_bytes: result.ok() };
        if let Ok((cycles, instructions, cache_misses)) = Self::get_hardware_counters() { metrics.cycles = Some(cycles); metrics.instructions = Some(instructions); metrics.cache_misses = Some(cache_misses); metrics.energy_estimate_joules = Some(cycles as f64 * 0.5e-9); } //Try to get hardware counters
        Ok(metrics)
    }
    fn run_function(&mut self, config: &TestConfig) -> Result<usize, Box<dyn std::error::Error>> { //Route to the appropriate test function
        match config.function { TestFunction::DKG1 => self.test_dkg_phase1(config), TestFunction::DKG2 => self.test_dkg_phase2(config), TestFunction::DKG3 => self.test_dkg_phase3(config), TestFunction::PartialGen => self.test_partial_generation(config), TestFunction::PartialVerify => self.test_partial_verification(config), TestFunction::AggCompute => self.test_aggregate_computation(config), TestFunction::ProofGen => self.test_proof_generation(config), TestFunction::ProofVerify => self.test_proof_verification(config) }
    }
    fn test_dkg_phase1(&mut self, config: &TestConfig) -> Result<usize, Box<dyn std::error::Error>> { let (_secret_pkg, round1_pkg) = common::dkg_phase1(config.device_id, config.n, config.t)?; let size = bincode::serialize(&round1_pkg)?.len(); Ok(size) } //DKG Phase 1 (uses common module directly)
    fn test_dkg_phase2(&mut self, config: &TestConfig) -> Result<usize, Box<dyn std::error::Error>> { //DKG Phase 2 (uses common module directly)
        let r1_packages_bytes = self.fixture_client.get_round1_packages(config.n, config.t, config.device_id)?; //Get fixtures
        let mut received_r1 = BTreeMap::new(); let all_ids: Vec<u16> = (1..=config.n as u16).filter(|&id| id != config.device_id as u16).collect(); //Deserialize round1 packages
        for (i, pkg_bytes) in r1_packages_bytes.iter().enumerate() { let pkg = frost::keys::dkg::round1::Package::deserialize(&pkg_bytes[..])?; let id = frost::Identifier::try_from(all_ids[i])?; received_r1.insert(id, pkg); }
        let (secret_pkg, _) = common::dkg_phase1(config.device_id, config.n, config.t)?; //Get our secret package (from phase 1)
        let (_round2_secret, round2_packages) = common::dkg_phase2(secret_pkg, &received_r1)?; //MEASURED OPERATION
        let size = round2_packages.values().map(|pkg| bincode::serialize(pkg).unwrap_or_default().len()).sum(); Ok(size) //Return total size of round2 packages
    }
    fn test_dkg_phase3(&mut self, config: &TestConfig) -> Result<usize, Box<dyn std::error::Error>> { //DKG Phase 3 (uses common module directly)
        let (r1_packages_bytes, r2_packages_bytes) = self.fixture_client.get_round2_packages(config.n, config.t, config.device_id)?; //Get fixtures
        let all_ids: Vec<u16> = (1..=config.n as u16).filter(|&id| id != config.device_id as u16).collect(); //Deserialize packages
        let mut received_r1 = BTreeMap::new(); for (i, pkg_bytes) in r1_packages_bytes.iter().enumerate() { let pkg = frost::keys::dkg::round1::Package::deserialize(&pkg_bytes[..])?; let id = frost::Identifier::try_from(all_ids[i])?; received_r1.insert(id, pkg); }
        let mut received_r2 = BTreeMap::new(); for (i, pkg_bytes) in r2_packages_bytes.iter().enumerate() { let pkg = frost::keys::dkg::round2::Package::deserialize(&pkg_bytes[..])?; let id = frost::Identifier::try_from(all_ids[i])?; received_r2.insert(id, pkg); }
        let (secret_pkg, _) = common::dkg_phase1(config.device_id, config.n, config.t)?; let (round2_secret, _) = common::dkg_phase2(secret_pkg, &received_r1)?; //Get round2 secret (from phase 2)
        let (key_package, public_package) = common::dkg_phase3(&round2_secret, &received_r1, &received_r2)?; //MEASURED OPERATION
        let size = bincode::serialize(&key_package)?.len() + bincode::serialize(&public_package)?.len(); Ok(size) //Return size of key package
    }
    fn test_partial_generation(&mut self, config: &TestConfig) -> Result<usize, Box<dyn std::error::Error>> { //Partial Generation (uses common module directly)
        let device_output = self.fixture_client.get_dkg_completed(config.n, config.t, config.device_id)?; //Get DKG outputs (not measured)
        let key_package = frost::keys::KeyPackage::deserialize(&device_output.key_package).map_err(|e| format!("KeyPackage deser: {:?}", e))?;
        let public_package = frost::keys::PublicKeyPackage::deserialize(&device_output.public_package).map_err(|e| format!("PublicPackage deser: {:?}", e))?;
        let signing_key = SigningKey::from_bytes(&device_output.signing_pubkey); //Get signing key
        let ciphertexts = self.fixture_client.get_ciphertexts(ZKPType::Bulletproof, config.n, config.t)?; //Get verified ciphertexts (use any ZKP type, they're all the same)
        let partial = common::generate_partial_decryption(config.device_id, &key_package, &public_package, &signing_key, &ciphertexts)?; //MEASURED OPERATION
        let size = bincode::serialize(&partial)?.len(); Ok(size)
    }
    fn test_partial_verification(&mut self, config: &TestConfig) -> Result<usize, Box<dyn std::error::Error>> { //Partial Verification (uses common module directly)
        let partial_data = self.fixture_client.get_sample_partial(ZKPType::Bulletproof, config.n, config.t)?; //Get fixtures
        let partial: PartialDecryption = bincode::deserialize(&partial_data.partial_bytes)?;
        let device_output = self.fixture_client.get_dkg_completed(config.n, config.t, config.device_id)?;
        let public_package = frost::keys::PublicKeyPackage::deserialize(&device_output.public_package).map_err(|e| format!("PublicPackage deser: {:?}", e))?;
        let peer_keys = self.get_cached_peer_keys(config.n, config.t)?; //Get peer keys (all devices)
        let ciphertexts = self.fixture_client.get_ciphertexts(ZKPType::Bulletproof, config.n, config.t)?;
        let mut verified_partials = Vec::new(); let mut rates = HashMap::new();
        let verified = common::receive_partial(partial, &peer_keys, &public_package, &ciphertexts, &mut verified_partials, &mut rates)?; //MEASURED OPERATION
        Ok(std::mem::size_of_val(&verified))
    }
    fn test_aggregate_computation(&mut self, config: &TestConfig) -> Result<usize, Box<dyn std::error::Error>> { //Aggregate Computation (uses common module directly)
        let ciphertexts = self.fixture_client.get_ciphertexts(ZKPType::Bulletproof, config.n, config.t)?; //Get fixtures
        let partial_decryptions = self.fixture_client.get_threshold_partials(ZKPType::Bulletproof, config.n, config.t)?;
        let verified_partials: Vec<VerifiedPartial> = partial_decryptions.iter().map(|p| VerifiedPartial { device_id: p.device_id, timestamp: p.timestamp, partial: p.partial.0.decompress().unwrap() }).collect(); //Convert to VerifiedPartial
        let (count, total) = common::compute_aggregate(config.t, &ciphertexts, &verified_partials)?; //MEASURED OPERATION
        println!("  Result: {}/{}", count, total); Ok(std::mem::size_of::<(usize, usize)>())
    }
    fn test_proof_generation(&mut self, config: &TestConfig) -> Result<usize, Box<dyn std::error::Error>> { //Proof Generation (ZKP-specific)
        let zkp_type = config.zkp_type.ok_or("ZKP type required for ProofGen")?;
        let device_output = self.fixture_client.get_dkg_completed(config.n, config.t, config.device_id)?; //Get DKG outputs
        let key_package = frost::keys::KeyPackage::deserialize(&device_output.key_package).map_err(|e| format!("KeyPackage deser: {:?}", e))?;
        let public_package = frost::keys::PublicKeyPackage::deserialize(&device_output.public_package).map_err(|e| format!("PublicPackage deser: {:?}", e))?;
        let peer_keys = self.get_cached_peer_keys(config.n, config.t)?; //Get peer keys
        let state = 1u8; //Test with state=1
        let proof_bytes = match zkp_type { //MEASURED OPERATION (ZKP-specific)
            ZKPType::Bulletproof => { let device = bulletproof::IoTDevice::new(config.device_id, config.t, key_package, public_package, peer_keys, None)?; let proof = device.generate_proof(state)?; bincode::serialize(&proof)? }
            ZKPType::SNARK => { let setup = self.halo2_setup.as_ref().ok_or("Halo2 setup not loaded")?; let device = snark::IoTDevice::new(config.device_id, config.t, key_package, public_package, peer_keys, setup.clone(), None)?; let proof = device.generate_proof(state)?; bincode::serialize(&proof)? }
            ZKPType::STARK => { let device = stark::IoTDevice::new(config.device_id, config.t, key_package, public_package, peer_keys, None)?; let proof = device.generate_proof(state)?; bincode::serialize(&proof)? }
        };
        Ok(proof_bytes.len())
    }
    fn test_proof_verification(&mut self, config: &TestConfig) -> Result<usize, Box<dyn std::error::Error>> { //Proof Verification (ZKP-specific)
        let zkp_type = config.zkp_type.ok_or("ZKP type required for ProofVerify")?;
        let proof_bytes = self.fixture_client.get_sample_proof(zkp_type, config.n, config.t)?; //Get sample proof from fixture server
        let device_output = self.fixture_client.get_dkg_completed(config.n, config.t, config.device_id)?; //Get DKG outputs
        let key_package = frost::keys::KeyPackage::deserialize(&device_output.key_package).map_err(|e| format!("KeyPackage deser: {:?}", e))?;
        let public_package = frost::keys::PublicKeyPackage::deserialize(&device_output.public_package).map_err(|e| format!("PublicPackage deser: {:?}", e))?;
        let peer_keys = self.get_cached_peer_keys(config.n, config.t)?; //Get peer keys
        match zkp_type { //MEASURED OPERATION (ZKP-specific)
            ZKPType::Bulletproof => { let mut device = bulletproof::IoTDevice::new(config.device_id, config.t, key_package, public_package, peer_keys, None)?; let proof: bulletproof::DeviceProof = bincode::deserialize(&proof_bytes)?; device.receive_proof(proof)?; }
            ZKPType::SNARK => { let setup = self.halo2_setup.as_ref().ok_or("Halo2 setup not loaded")?; let mut device = snark::IoTDevice::new(config.device_id, config.t, key_package, public_package, peer_keys, setup.clone(), None)?; let proof: snark::DeviceProof = bincode::deserialize(&proof_bytes)?; device.receive_proof(proof)?; }
            ZKPType::STARK => { let mut device = stark::IoTDevice::new(config.device_id, config.t, key_package, public_package, peer_keys, None)?; let proof: stark::DeviceProof = bincode::deserialize(&proof_bytes)?; device.receive_proof(proof)?; }
        }
        Ok(proof_bytes.len())
    }
    fn get_rss_kb() -> Result<u64, Box<dyn std::error::Error>> { let pid = std::process::id(); let status = std::fs::read_to_string(format!("/proc/{}/status", pid))?; for line in status.lines() { if line.starts_with("VmRSS:") { let kb: u64 = line.split_whitespace().nth(1).and_then(|s| s.parse().ok()).unwrap_or(0); return Ok(kb); } } Ok(0) } //Get current RSS memory
    fn get_peak_rss_kb() -> Result<u64, Box<dyn std::error::Error>> { let pid = std::process::id(); let status = std::fs::read_to_string(format!("/proc/{}/status", pid))?; for line in status.lines() { if line.starts_with("VmHWM:") { let kb: u64 = line.split_whitespace().nth(1).and_then(|s| s.parse().ok()).unwrap_or(0); return Ok(kb); } } Ok(0) } //Get peak RSS memory
    fn get_cpu_times() -> Result<(u128, u128), Box<dyn std::error::Error>> { //Read /proc/self/stat for CPU times
        let pid = std::process::id(); let stat = std::fs::read_to_string(format!("/proc/{}/stat", pid))?; let parts: Vec<&str> = stat.split_whitespace().collect(); //Parse the stat file (format: pid (comm) state ppid pgrp session tty_nr tpgid flags minflt cminflt majflt cmajflt utime stime cutime cstime ...)
        if parts.len() < 15 { return Ok((0, 0)); }
        let utime_ticks: u64 = parts[13].parse().unwrap_or(0); let stime_ticks: u64 = parts[14].parse().unwrap_or(0); //utime is at index 13, stime is at index 14 (in clock ticks)
        let clock_ticks_per_sec = 100u64; let utime_us = (utime_ticks * 1_000_000) / clock_ticks_per_sec; let stime_us = (stime_ticks * 1_000_000) / clock_ticks_per_sec; //Convert from clock ticks to microseconds (most Linux systems use 100 ticks/second)
        Ok((utime_us as u128, stime_us as u128))
    }
    fn get_io_stats() -> Result<(u64, u64), Box<dyn std::error::Error>> { //Read /proc/self/io (may fail on some systems)
        let pid = std::process::id();
        match std::fs::read_to_string(format!("/proc/{}/io", pid)) { Ok(io_str) => { let mut read_bytes = 0u64; let mut write_bytes = 0u64; for line in io_str.lines() { if line.starts_with("read_bytes:") { read_bytes = line.split_whitespace().nth(1).and_then(|s| s.parse().ok()).unwrap_or(0); } else if line.starts_with("write_bytes:") { write_bytes = line.split_whitespace().nth(1).and_then(|s| s.parse().ok()).unwrap_or(0); } } Ok((read_bytes / 1024, write_bytes / 1024)) } Err(_) => Ok((0, 0)) } //If /proc/self/io is not available, return zeros
    }
    fn get_hardware_counters() -> Result<(u64, u64, u64), Box<dyn std::error::Error>> { //Try to use 'perf stat' to get hardware counters (may not work on all VMs, especially ARM or restricted environments)
        use std::process::Command;
        let perf_check = Command::new("which").arg("perf").output(); //Check if perf is available
        if perf_check.is_err() || !perf_check.unwrap().status.success() { return Err("perf not available".into()); } //perf not available
        Err("Hardware counters require manual perf setup".into()) //Note: This is tricky because we'd need to attach perf to our own process. For now, we'll return an error and let the caller handle it gracefully. Alternative: Use 'perf_event_open' syscall directly, but that requires unsafe code
    }
    fn timestamp_iso8601() -> String { chrono::Utc::now().to_rfc3339() } //Get ISO8601 timestamp
    fn write_metrics(&mut self, metrics: &Metrics) { let json = serde_json::to_string(metrics).unwrap(); writeln!(self.output_file, "{}", json).ok(); self.output_file.flush().ok(); } //Write metrics to JSONL file
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();
    println!("=== ZK-DISPHASIA Test Harness ===\nVM Profile: {}\nDevice ID: {}\nFixture Server: {}\nOutput: {}\n", args.vm_profile, args.device_id, args.fixture_server, args.output);
    let mut runner = TestRunner::new(&args)?;
    runner.run_all_tests();
    println!("\n=== Test harness completed ===");
    Ok(())
}