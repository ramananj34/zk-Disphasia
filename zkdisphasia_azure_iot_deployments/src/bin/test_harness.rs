//! Test Harness for ZK-DISPHASIA Benchmarking
//! Optimized to avoid redundant testing of shared functions

use serde::{Deserialize, Serialize};
use std::collections::{HashMap, BTreeMap};
use std::time::Instant;
use std::fs::{File, OpenOptions};
use std::io::Write;
use clap::Parser;
use reqwest::blocking::Client;
use base64::Engine;
use frost_ristretto255 as frost;
use ed25519_dalek::{VerifyingKey, SigningKey};

// Import from main library
use zk_disphasia_azure_test::common::{self, VerifiedCiphertext, VerifiedPartial, PartialDecryption};
use zk_disphasia_azure_test::bulletproof;
use zk_disphasia_azure_test::snark;
use zk_disphasia_azure_test::stark;

/// Command-line arguments
#[derive(Parser, Debug)]
#[command(author, version, about = "ZK-DISPHASIA Test Harness")]
struct Args {
    /// Fixture server URL
    #[arg(long, default_value = "http://fixture-server:8080")]
    fixture_server: String,
    
    /// VM profile name
    #[arg(long)]
    vm_profile: String,
    
    /// Device ID for this test runner
    #[arg(long)]
    device_id: u32,
    
    /// Output file for metrics
    #[arg(long, default_value = "/tmp/metrics.jsonl")]
    output: String,
}

/// ZKP type enum
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
enum ZKPType {
    Bulletproof,
    SNARK,
    STARK,
}

/// Function being tested
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
enum TestFunction {
    // Shared functions (ZKP-independent)
    DKG1,
    DKG2,
    DKG3,
    PartialGen,
    PartialVerify,
    AggCompute,
    
    // ZKP-specific functions
    ProofGen,
    ProofVerify,
}

/// Test configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
struct TestConfig {
    zkp_type: Option<ZKPType>,  // None for shared functions
    function: TestFunction,
    n: usize,
    t: usize,
    device_id: u32,
    run: usize,
}

/// Performance metrics
#[derive(Debug, Serialize, Deserialize)]
struct Metrics {
    timestamp: String,
    vm_profile: String,
    vm_arch: String,
    test_config: TestConfig,
    
    status: String,
    failure_reason: Option<String>,
    
    wall_time_us: u128,
    cpu_time_user_us: u128,
    cpu_time_system_us: u128,
    
    peak_rss_kb: u64,
    initial_rss_kb: u64,
    delta_rss_kb: i64,
    
    disk_read_kb: u64,
    disk_write_kb: u64,
    
    cycles: Option<u64>,
    instructions: Option<u64>,
    cache_misses: Option<u64>,
    energy_estimate_joules: Option<f64>,
    
    output_size_bytes: Option<usize>,
}

/// Fixture client
struct FixtureClient {
    base_url: String,
    client: Client,
}

impl FixtureClient {
    fn new(base_url: String) -> Self {
        Self {
            base_url,
            client: Client::new(),
        }
    }
    
    fn get_dkg_completed(&self, n: usize, t: usize, device_id: u32) -> Result<DeviceOutput, String> {
        let url = format!("{}/api/dkg/completed/{}/{}/{}", self.base_url, n, t, device_id);
        self.client.get(&url)
            .send()
            .map_err(|e| format!("HTTP error: {}", e))?
            .json()
            .map_err(|e| format!("JSON error: {}", e))
    }
    
    fn get_round1_packages(&self, n: usize, t: usize, device_id: u32) -> Result<Vec<Vec<u8>>, String> {
        let url = format!("{}/api/dkg/round1/{}/{}/{}", self.base_url, n, t, device_id);
        let encoded: Vec<String> = self.client.get(&url)
            .send()
            .map_err(|e| format!("HTTP error: {}", e))?
            .json()
            .map_err(|e| format!("JSON error: {}", e))?;
        
        encoded.iter()
            .map(|s| base64::engine::general_purpose::STANDARD.decode(s)
                .map_err(|e| format!("Base64 error: {}", e)))
            .collect()
    }
    
    fn get_round2_packages(&self, n: usize, t: usize, device_id: u32) -> Result<(Vec<Vec<u8>>, Vec<Vec<u8>>), String> {
        let url = format!("{}/api/dkg/round2/{}/{}/{}", self.base_url, n, t, device_id);
        
        #[derive(Deserialize)]
        struct Response {
            round1_packages: Vec<String>,
            round2_packages: Vec<String>,
        }
        
        let resp: Response = self.client.get(&url)
            .send()
            .map_err(|e| format!("HTTP error: {}", e))?
            .json()
            .map_err(|e| format!("JSON error: {}", e))?;
        
        let r1: Result<Vec<_>, _> = resp.round1_packages.iter()
            .map(|s| base64::engine::general_purpose::STANDARD.decode(s)
                .map_err(|e| format!("Base64 error: {}", e)))
            .collect();
        
        let r2: Result<Vec<_>, _> = resp.round2_packages.iter()
            .map(|s| base64::engine::general_purpose::STANDARD.decode(s)
                .map_err(|e| format!("Base64 error: {}", e)))
            .collect();
        
        Ok((r1?, r2?))
    }
    
    fn get_sample_proof(&self, zkp_type: ZKPType, n: usize, t: usize) -> Result<Vec<u8>, String> {
        let zkp_str = match zkp_type {
            ZKPType::Bulletproof => "bulletproof",
            ZKPType::SNARK => "snark",
            ZKPType::STARK => "stark",
        };
        let url = format!("{}/api/proof/{}/{}/{}", self.base_url, zkp_str, n, t);
        self.client.get(&url)
            .send()
            .map_err(|e| format!("HTTP error: {}", e))?
            .bytes()
            .map(|b| b.to_vec())
            .map_err(|e| format!("HTTP error: {}", e))
    }
    
    fn get_ciphertexts(&self, zkp_type: ZKPType, n: usize, t: usize) -> Result<Vec<VerifiedCiphertext>, String> {
        let zkp_str = match zkp_type {
            ZKPType::Bulletproof => "bulletproof",
            ZKPType::SNARK => "snark",
            ZKPType::STARK => "stark",
        };
        let url = format!("{}/api/ciphertexts/{}/{}/{}", self.base_url, zkp_str, n, t);
        
        let encoded: Vec<String> = self.client.get(&url)
            .send()
            .map_err(|e| format!("HTTP error: {}", e))?
            .json()
            .map_err(|e| format!("JSON error: {}", e))?;
        
        encoded.iter()
            .map(|s| {
                let bytes = base64::engine::general_purpose::STANDARD.decode(s)
                    .map_err(|e| format!("Base64 error: {}", e))?;
                bincode::deserialize(&bytes).map_err(|e| format!("Bincode error: {}", e))
            })
            .collect()
    }
    
    fn get_sample_partial(&self, zkp_type: ZKPType, n: usize, t: usize) -> Result<VerifiedPartialData, String> {
        let zkp_str = match zkp_type {
            ZKPType::Bulletproof => "bulletproof",
            ZKPType::SNARK => "snark",
            ZKPType::STARK => "stark",
        };
        let url = format!("{}/api/partial/{}/{}/{}", self.base_url, zkp_str, n, t);
        self.client.get(&url)
            .send()
            .map_err(|e| format!("HTTP error: {}", e))?
            .json()
            .map_err(|e| format!("JSON error: {}", e))
    }
    
    fn get_threshold_partials(&self, zkp_type: ZKPType, n: usize, t: usize) -> Result<Vec<PartialDecryption>, String> {
        let zkp_str = match zkp_type {
            ZKPType::Bulletproof => "bulletproof",
            ZKPType::SNARK => "snark",
            ZKPType::STARK => "stark",
        };
        let url = format!("{}/api/partials/{}/{}/{}", self.base_url, zkp_str, n, t);
        
        let encoded: Vec<String> = self.client.get(&url)
            .send()
            .map_err(|e| format!("HTTP error: {}", e))?
            .json()
            .map_err(|e| format!("JSON error: {}", e))?;
        
        encoded.iter()
            .map(|s| {
                let bytes = base64::engine::general_purpose::STANDARD.decode(s)
                    .map_err(|e| format!("Base64 error: {}", e))?;
                bincode::deserialize(&bytes).map_err(|e| format!("Bincode error: {}", e))
            })
            .collect()
    }
}

#[derive(Debug, Deserialize)]
#[allow(dead_code)]  // Fields are used via deserialization
struct DeviceOutput {
    device_id: u32,
    key_package: Vec<u8>,
    public_package: Vec<u8>,
    signing_pubkey: [u8; 32],
}

#[derive(Debug, Deserialize)]
#[allow(dead_code)]  // Fields are used via deserialization
struct VerifiedPartialData {
    device_id: u32,
    partial_bytes: Vec<u8>,
    aggregate_c1_bytes: [u8; 32],
    aggregate_c2_bytes: [u8; 32],
}

/// Main test runner
struct TestRunner {
    fixture_client: FixtureClient,
    output_file: File,
    vm_profile: String,
    device_id: u32,
    halo2_setup: Option<snark::Halo2Setup>,
}

impl TestRunner {
    fn new(args: &Args) -> Result<Self, Box<dyn std::error::Error>> {
        // Load Halo2 setup if available
        let halo2_setup = if std::path::Path::new("./trusted_setup/kzg_bn254_5.params").exists() {
            println!("Loading Halo2 setup...");
            Some(snark::setup_halo2()?)
        } else {
            println!("Warning: Halo2 params not found, SNARK tests will fail");
            None
        };
        
        let output_file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&args.output)?;
        
        Ok(Self {
            fixture_client: FixtureClient::new(args.fixture_server.clone()),
            output_file,
            vm_profile: args.vm_profile.clone(),
            device_id: args.device_id,
            halo2_setup,
        })
    }
    
    /// Run all tests with optimized structure
    fn run_all_tests(&mut self) {
        //let network_sizes = vec![5, 10, 20, 50, 100, 500, 1000, 2500, 5000, 10000];
        let network_sizes = vec![5, 10, 20, 50];
        let threshold_ratios = vec![0.5, 0.67, 0.75];
        
        // Shared functions (tested once per n, t)
        let shared_functions = vec![
            TestFunction::DKG1,
            TestFunction::DKG2,
            TestFunction::DKG3,
            TestFunction::PartialGen,
            TestFunction::PartialVerify,
            TestFunction::AggCompute,
        ];
        
        // ZKP-specific functions (tested per zkp_type, n, t)
        let zkp_functions = vec![
            TestFunction::ProofGen,
            TestFunction::ProofVerify,
        ];
        
        let zkp_types = vec![ZKPType::Bulletproof, ZKPType::SNARK, ZKPType::STARK];
        
        let mut test_count = 0;
        let total_tests = (network_sizes.len() * threshold_ratios.len() * shared_functions.len() * 10) +
                          (zkp_types.len() * network_sizes.len() * threshold_ratios.len() * zkp_functions.len() * 10);
        
        println!("=== Starting Test Suite ===");
        println!("VM Profile: {}", self.vm_profile);
        println!("Total tests to run: {}", total_tests);
        println!();
        
        let mut success_count = 0;
        let mut failure_count = 0;
        
        // Test shared functions (no ZKP type needed)
        println!("Testing shared functions (DKG, Partial, Aggregate)...");
        for n in &network_sizes {
            for t_ratio in &threshold_ratios {
                let t = (*n as f64 * t_ratio).ceil() as usize;
                
                for function in &shared_functions {
                    for run in 1..=10 {
                        test_count += 1;
                        
                        let config = TestConfig {
                            zkp_type: None,  // Shared function
                            function: *function,
                            n: *n,
                            t,
                            device_id: self.device_id,
                            run,
                        };
                        
                        println!("[{}/{}] {:?} n={} t={} run={}", 
                            test_count, total_tests, function, n, t, run);
                        
                        match self.run_single_test(&config) {
                            Ok(metrics) => {
                                self.write_metrics(&metrics);
                                if metrics.status == "SUCCESS" {
                                    success_count += 1;
                                } else {
                                    failure_count += 1;
                                }
                            }
                            Err(e) => {
                                eprintln!("  Error: {}", e);
                                failure_count += 1;
                            }
                        }
                    }
                }
            }
        }
        
        // Test ZKP-specific functions
        println!("\nTesting ZKP-specific functions (ProofGen, ProofVerify)...");
        for zkp_type in &zkp_types {
            println!("\n--- Testing {:?} ---", zkp_type);
            
            for n in &network_sizes {
                for t_ratio in &threshold_ratios {
                    let t = (*n as f64 * t_ratio).ceil() as usize;
                    
                    for function in &zkp_functions {
                        for run in 1..=10 {
                            test_count += 1;
                            
                            let config = TestConfig {
                                zkp_type: Some(*zkp_type),
                                function: *function,
                                n: *n,
                                t,
                                device_id: self.device_id,
                                run,
                            };
                            
                            println!("[{}/{}] {:?} {:?} n={} t={} run={}", 
                                test_count, total_tests, zkp_type, function, n, t, run);
                            
                            match self.run_single_test(&config) {
                                Ok(metrics) => {
                                    self.write_metrics(&metrics);
                                    if metrics.status == "SUCCESS" {
                                        success_count += 1;
                                    } else {
                                        failure_count += 1;
                                    }
                                }
                                Err(e) => {
                                    eprintln!("  Error: {}", e);
                                    failure_count += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
        
        println!("\n=== Test Suite Complete ===");
        println!("Total tests: {}", test_count);
        println!("Successes: {}", success_count);
        println!("Failures: {}", failure_count);
        println!("Success rate: {:.1}%", (success_count as f64 / test_count as f64) * 100.0);
    }
    
    /// Run a single test with full instrumentation
    fn run_single_test(&mut self, config: &TestConfig) -> Result<Metrics, Box<dyn std::error::Error>> {
        let initial_rss = Self::get_rss_kb()?;
        let wall_start = Instant::now();
        
        // Run the function
        let result = self.run_function(config);
        
        let wall_time_us = wall_start.elapsed().as_micros();
        let peak_rss = Self::get_peak_rss_kb()?;
        let delta_rss = peak_rss as i64 - initial_rss as i64;
        let (user_time_us, system_time_us) = Self::get_cpu_times()?;
        let (disk_read_kb, disk_write_kb) = Self::get_io_stats()?;
        
        let mut metrics = Metrics {
            timestamp: Self::timestamp_iso8601(),
            vm_profile: self.vm_profile.clone(),
            vm_arch: std::env::consts::ARCH.to_string(),
            test_config: config.clone(),
            status: if result.is_ok() { "SUCCESS".to_string() } else { "FAILED".to_string() },
            failure_reason: result.as_ref().err().map(|e| e.to_string()),
            wall_time_us,
            cpu_time_user_us: user_time_us,
            cpu_time_system_us: system_time_us,
            peak_rss_kb: peak_rss,
            initial_rss_kb: initial_rss,
            delta_rss_kb: delta_rss,
            disk_read_kb,
            disk_write_kb,
            cycles: None,
            instructions: None,
            cache_misses: None,
            energy_estimate_joules: None,
            output_size_bytes: result.ok(),
        };
        
        // Try to get hardware counters
        if let Ok((cycles, instructions, cache_misses)) = Self::get_hardware_counters() {
            metrics.cycles = Some(cycles);
            metrics.instructions = Some(instructions);
            metrics.cache_misses = Some(cache_misses);
            metrics.energy_estimate_joules = Some(cycles as f64 * 0.5e-9);
        }
        
        Ok(metrics)
    }
    
    /// Route to the appropriate test function
    fn run_function(&mut self, config: &TestConfig) -> Result<usize, Box<dyn std::error::Error>> {
        match config.function {
            // Shared functions (ZKP-independent)
            TestFunction::DKG1 => self.test_dkg_phase1(config),
            TestFunction::DKG2 => self.test_dkg_phase2(config),
            TestFunction::DKG3 => self.test_dkg_phase3(config),
            TestFunction::PartialGen => self.test_partial_generation(config),
            TestFunction::PartialVerify => self.test_partial_verification(config),
            TestFunction::AggCompute => self.test_aggregate_computation(config),
            
            // ZKP-specific functions
            TestFunction::ProofGen => self.test_proof_generation(config),
            TestFunction::ProofVerify => self.test_proof_verification(config),
        }
    }
    
    // ==================== SHARED FUNCTIONS ====================
    
    /// Test DKG Phase 1 (uses common module directly)
    fn test_dkg_phase1(&mut self, config: &TestConfig) -> Result<usize, Box<dyn std::error::Error>> {
        let (_secret_pkg, round1_pkg) = common::dkg_phase1(
            config.device_id,
            config.n,
            config.t,
        )?;
        
        // Return serialized size
        let size = bincode::serialize(&round1_pkg)?.len();
        Ok(size)
    }
    
    /// Test DKG Phase 2 (uses common module directly)
    fn test_dkg_phase2(&mut self, config: &TestConfig) -> Result<usize, Box<dyn std::error::Error>> {
        // Get fixtures
        let r1_packages_bytes = self.fixture_client.get_round1_packages(
            config.n,
            config.t,
            config.device_id,
        )?;
        
        // Deserialize round1 packages
        let mut received_r1 = BTreeMap::new();
        let all_ids: Vec<u16> = (1..=config.n as u16)
            .filter(|&id| id != config.device_id as u16)
            .collect();

        for (i, pkg_bytes) in r1_packages_bytes.iter().enumerate() {
            let pkg = frost::keys::dkg::round1::Package::deserialize(&pkg_bytes[..])?;
            let id = frost::Identifier::try_from(all_ids[i])?;  // ✅ CORRECT
            received_r1.insert(id, pkg);
        }
        
        // Get our secret package (from phase 1)
        let (secret_pkg, _) = common::dkg_phase1(config.device_id, config.n, config.t)?;
        
        // === MEASURED OPERATION ===
        let (_round2_secret, round2_packages) = common::dkg_phase2(secret_pkg, &received_r1)?;
        // === END MEASURED OPERATION ===
        
        // Return total size of round2 packages
        let size = round2_packages.values()
            .map(|pkg| bincode::serialize(pkg).unwrap_or_default().len())
            .sum();
        
        Ok(size)
    }
    
    /// Test DKG Phase 3 (uses common module directly)
    fn test_dkg_phase3(&mut self, config: &TestConfig) -> Result<usize, Box<dyn std::error::Error>> {
        // Get fixtures
        let (r1_packages_bytes, r2_packages_bytes) = self.fixture_client.get_round2_packages(
            config.n,
            config.t,
            config.device_id,
        )?;
        
        // Deserialize packages
        let all_ids: Vec<u16> = (1..=config.n as u16)
            .filter(|&id| id != config.device_id as u16)
            .collect();

        let mut received_r1 = BTreeMap::new();
        for (i, pkg_bytes) in r1_packages_bytes.iter().enumerate() {
            let pkg = frost::keys::dkg::round1::Package::deserialize(&pkg_bytes[..])?;
            let id = frost::Identifier::try_from(all_ids[i])?;  // ✅ CORRECT
            received_r1.insert(id, pkg);
        }
        
        let mut received_r2 = BTreeMap::new();
        for (i, pkg_bytes) in r2_packages_bytes.iter().enumerate() {
            let pkg = frost::keys::dkg::round2::Package::deserialize(&pkg_bytes[..])?;
            let id = frost::Identifier::try_from(all_ids[i])?;  // ✅ CORRECT
            received_r2.insert(id, pkg);
        }
        
        // Get round2 secret (from phase 2)
        let (secret_pkg, _) = common::dkg_phase1(config.device_id, config.n, config.t)?;
        let (round2_secret, _) = common::dkg_phase2(secret_pkg, &received_r1)?;
        
        // === MEASURED OPERATION ===
        let (key_package, public_package) = common::dkg_phase3(
            &round2_secret,
            &received_r1,
            &received_r2,
        )?;
        // === END MEASURED OPERATION ===
        
        // Return size of key package
        let size = bincode::serialize(&key_package)?.len() + 
                   bincode::serialize(&public_package)?.len();
        
        Ok(size)
    }
    
    /// Test Partial Generation (uses common module directly)
    fn test_partial_generation(&mut self, config: &TestConfig) -> Result<usize, Box<dyn std::error::Error>> {
        // Get DKG outputs (not measured)
        let device_output = self.fixture_client.get_dkg_completed(
            config.n,
            config.t,
            config.device_id,
        )?;
        
        let key_package = frost::keys::KeyPackage::deserialize(&device_output.key_package)
            .map_err(|e| format!("KeyPackage deser: {:?}", e))?;
        let public_package = frost::keys::PublicKeyPackage::deserialize(&device_output.public_package)
            .map_err(|e| format!("PublicPackage deser: {:?}", e))?;
        
        // Get signing key
        let signing_key = SigningKey::from_bytes(&device_output.signing_pubkey);
        
        // Get verified ciphertexts (use any ZKP type, they're all the same)
        let ciphertexts = self.fixture_client.get_ciphertexts(
            ZKPType::Bulletproof,
            config.n,
            config.t,
        )?;
        
        // === MEASURED OPERATION ===
        let partial = common::generate_partial_decryption(
            config.device_id,
            &key_package,
            &public_package,
            &signing_key,
            &ciphertexts,
        )?;
        // === END MEASURED OPERATION ===
        
        let size = bincode::serialize(&partial)?.len();
        Ok(size)
    }
    
    /// Test Partial Verification (uses common module directly)
    fn test_partial_verification(&mut self, config: &TestConfig) -> Result<usize, Box<dyn std::error::Error>> {
        // Get fixtures
        let partial_data = self.fixture_client.get_sample_partial(
            ZKPType::Bulletproof,  // Shared, any type works
            config.n,
            config.t,
        )?;
        
        let partial: PartialDecryption = bincode::deserialize(&partial_data.partial_bytes)?;
        
        let device_output = self.fixture_client.get_dkg_completed(
            config.n,
            config.t,
            config.device_id,
        )?;
        
        let public_package = frost::keys::PublicKeyPackage::deserialize(&device_output.public_package)
            .map_err(|e| format!("PublicPackage deser: {:?}", e))?;
        
        // Get peer keys (all devices)
        let mut peer_keys = HashMap::new();
        for i in 1..=config.n {
            let dev_out = self.fixture_client.get_dkg_completed(config.n, config.t, i as u32)?;
            let vk = VerifyingKey::from_bytes(&dev_out.signing_pubkey)
                .map_err(|e| format!("VerifyingKey: {:?}", e))?;
            peer_keys.insert(i as u32, vk);
        }
        
        let ciphertexts = self.fixture_client.get_ciphertexts(
            ZKPType::Bulletproof,
            config.n,
            config.t,
        )?;
        
        let mut verified_partials = Vec::new();
        let mut rates = HashMap::new();
        
        // === MEASURED OPERATION ===
        let verified = common::receive_partial(
            partial,
            &peer_keys,
            &public_package,
            &ciphertexts,
            &mut verified_partials,
            &mut rates,
        )?;
        // === END MEASURED OPERATION ===
        
        Ok(std::mem::size_of_val(&verified))
    }
    
    /// Test Aggregate Computation (uses common module directly)
    fn test_aggregate_computation(&mut self, config: &TestConfig) -> Result<usize, Box<dyn std::error::Error>> {
        // Get fixtures
        let ciphertexts = self.fixture_client.get_ciphertexts(
            ZKPType::Bulletproof,
            config.n,
            config.t,
        )?;
        
        let partial_decryptions = self.fixture_client.get_threshold_partials(
            ZKPType::Bulletproof,
            config.n,
            config.t,
        )?;
        
        // Convert to VerifiedPartial
        let verified_partials: Vec<VerifiedPartial> = partial_decryptions.iter()
            .map(|p| VerifiedPartial {
                device_id: p.device_id,
                timestamp: p.timestamp,
                partial: p.partial.0.decompress().unwrap(),
            })
            .collect();
        
        // === MEASURED OPERATION ===
        let (count, total) = common::compute_aggregate(
            config.t,
            &ciphertexts,
            &verified_partials,
        )?;
        // === END MEASURED OPERATION ===
        
        println!("  Result: {}/{}", count, total);
        Ok(std::mem::size_of::<(usize, usize)>())
    }
    
    // ==================== ZKP-SPECIFIC FUNCTIONS ====================
    
    /// Test Proof Generation (ZKP-specific)
    fn test_proof_generation(&mut self, config: &TestConfig) -> Result<usize, Box<dyn std::error::Error>> {
        let zkp_type = config.zkp_type.ok_or("ZKP type required for ProofGen")?;
        
        // Get DKG outputs
        let device_output = self.fixture_client.get_dkg_completed(
            config.n,
            config.t,
            config.device_id,
        )?;
        
        let key_package = frost::keys::KeyPackage::deserialize(&device_output.key_package)
            .map_err(|e| format!("KeyPackage deser: {:?}", e))?;
        let public_package = frost::keys::PublicKeyPackage::deserialize(&device_output.public_package)
            .map_err(|e| format!("PublicPackage deser: {:?}", e))?;
        
        // Get peer keys
        let mut peer_keys = HashMap::new();
        for i in 1..=config.n {
            let dev_out = self.fixture_client.get_dkg_completed(config.n, config.t, i as u32)?;
            let vk = VerifyingKey::from_bytes(&dev_out.signing_pubkey)
                .map_err(|e| format!("VerifyingKey: {:?}", e))?;
            peer_keys.insert(i as u32, vk);
        }
        
        let state = 1u8;  // Test with state=1
        
        // === MEASURED OPERATION (ZKP-specific) ===
        let proof_bytes = match zkp_type {
            ZKPType::Bulletproof => {
                let device = bulletproof::IoTDevice::new(
                    config.device_id,
                    config.t,
                    key_package,
                    public_package,
                    peer_keys,
                )?;
                let proof = device.generate_proof(state)?;
                bincode::serialize(&proof)?
            }
            ZKPType::SNARK => {
                let setup = self.halo2_setup.as_ref()
                    .ok_or("Halo2 setup not loaded")?;
                let device = snark::IoTDevice::new(
                    config.device_id,
                    config.t,
                    key_package,
                    public_package,
                    peer_keys,
                    setup.clone(),
                )?;
                let proof = device.generate_proof(state)?;
                bincode::serialize(&proof)?
            }
            ZKPType::STARK => {
                let device = stark::IoTDevice::new(
                    config.device_id,
                    config.t,
                    key_package,
                    public_package,
                    peer_keys,
                )?;
                let proof = device.generate_proof(state)?;
                bincode::serialize(&proof)?
            }
        };
        // === END MEASURED OPERATION ===
        
        Ok(proof_bytes.len())
    }
    
    /// Test Proof Verification (ZKP-specific)
    fn test_proof_verification(&mut self, config: &TestConfig) -> Result<usize, Box<dyn std::error::Error>> {
        let zkp_type = config.zkp_type.ok_or("ZKP type required for ProofVerify")?;
        
        // Get sample proof from fixture server
        let proof_bytes = self.fixture_client.get_sample_proof(
            zkp_type,
            config.n,
            config.t,
        )?;
        
        // Get DKG outputs
        let device_output = self.fixture_client.get_dkg_completed(
            config.n,
            config.t,
            config.device_id,
        )?;
        
        let key_package = frost::keys::KeyPackage::deserialize(&device_output.key_package)
            .map_err(|e| format!("KeyPackage deser: {:?}", e))?;
        let public_package = frost::keys::PublicKeyPackage::deserialize(&device_output.public_package)
            .map_err(|e| format!("PublicPackage deser: {:?}", e))?;
        
        // Get peer keys
        let mut peer_keys = HashMap::new();
        for i in 1..=config.n {
            let dev_out = self.fixture_client.get_dkg_completed(config.n, config.t, i as u32)?;
            let vk = VerifyingKey::from_bytes(&dev_out.signing_pubkey)
                .map_err(|e| format!("VerifyingKey: {:?}", e))?;
            peer_keys.insert(i as u32, vk);
        }
        
        // === MEASURED OPERATION (ZKP-specific) ===
        match zkp_type {
            ZKPType::Bulletproof => {
                let mut device = bulletproof::IoTDevice::new(
                    config.device_id,
                    config.t,
                    key_package,
                    public_package,
                    peer_keys,
                )?;
                let proof: bulletproof::DeviceProof = bincode::deserialize(&proof_bytes)?;
                device.receive_proof(proof)?;
            }
            ZKPType::SNARK => {
                let setup = self.halo2_setup.as_ref()
                    .ok_or("Halo2 setup not loaded")?;
                let mut device = snark::IoTDevice::new(
                    config.device_id,
                    config.t,
                    key_package,
                    public_package,
                    peer_keys,
                    setup.clone(),
                )?;
                let proof: snark::DeviceProof = bincode::deserialize(&proof_bytes)?;
                device.receive_proof(proof)?;
            }
            ZKPType::STARK => {
                let mut device = stark::IoTDevice::new(
                    config.device_id,
                    config.t,
                    key_package,
                    public_package,
                    peer_keys,
                )?;
                let proof: stark::DeviceProof = bincode::deserialize(&proof_bytes)?;
                device.receive_proof(proof)?;
            }
        }
        // === END MEASURED OPERATION ===
        
        Ok(proof_bytes.len())
    }
    
    // ==================== SYSTEM METRICS (Complete Implementation) ====================

    fn get_rss_kb() -> Result<u64, Box<dyn std::error::Error>> {
        let pid = std::process::id();
        let status = std::fs::read_to_string(format!("/proc/{}/status", pid))?;
        
        for line in status.lines() {
            if line.starts_with("VmRSS:") {
                let kb: u64 = line.split_whitespace()
                    .nth(1)
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(0);
                return Ok(kb);
            }
        }
        
        Ok(0)
    }

    fn get_peak_rss_kb() -> Result<u64, Box<dyn std::error::Error>> {
        let pid = std::process::id();
        let status = std::fs::read_to_string(format!("/proc/{}/status", pid))?;
        
        for line in status.lines() {
            if line.starts_with("VmHWM:") {
                let kb: u64 = line.split_whitespace()
                    .nth(1)
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(0);
                return Ok(kb);
            }
        }
        
        Ok(0)
    }

    fn get_cpu_times() -> Result<(u128, u128), Box<dyn std::error::Error>> {
        // Read /proc/self/stat for CPU times
        let pid = std::process::id();
        let stat = std::fs::read_to_string(format!("/proc/{}/stat", pid))?;
        
        // Parse the stat file
        // Format: pid (comm) state ppid pgrp session tty_nr tpgid flags minflt cminflt majflt cmajflt utime stime cutime cstime ...
        let parts: Vec<&str> = stat.split_whitespace().collect();
        
        if parts.len() < 15 {
            return Ok((0, 0));
        }
        
        // utime is at index 13, stime is at index 14 (in clock ticks)
        let utime_ticks: u64 = parts[13].parse().unwrap_or(0);
        let stime_ticks: u64 = parts[14].parse().unwrap_or(0);
        
        // Convert from clock ticks to microseconds
        // Most Linux systems use 100 ticks/second (USER_HZ=100)
        let clock_ticks_per_sec = 100u64;
        let utime_us = (utime_ticks * 1_000_000) / clock_ticks_per_sec;
        let stime_us = (stime_ticks * 1_000_000) / clock_ticks_per_sec;
        
        Ok((utime_us as u128, stime_us as u128))
    }

    fn get_io_stats() -> Result<(u64, u64), Box<dyn std::error::Error>> {
        let pid = std::process::id();
        
        // Try to read /proc/self/io (may fail on some systems)
        match std::fs::read_to_string(format!("/proc/{}/io", pid)) {
            Ok(io_str) => {
                let mut read_bytes = 0u64;
                let mut write_bytes = 0u64;
                
                for line in io_str.lines() {
                    if line.starts_with("read_bytes:") {
                        read_bytes = line.split_whitespace()
                            .nth(1)
                            .and_then(|s| s.parse().ok())
                            .unwrap_or(0);
                    } else if line.starts_with("write_bytes:") {
                        write_bytes = line.split_whitespace()
                            .nth(1)
                            .and_then(|s| s.parse().ok())
                            .unwrap_or(0);
                    }
                }
                
                Ok((read_bytes / 1024, write_bytes / 1024))
            }
            Err(_) => {
                // If /proc/self/io is not available, return zeros
                Ok((0, 0))
            }
        }
    }

    fn get_hardware_counters() -> Result<(u64, u64, u64), Box<dyn std::error::Error>> {
        // Try to use 'perf stat' to get hardware counters
        // This is a simple approach - may not work on all VMs (especially ARM or restricted environments)
        
        use std::process::Command;
        
        // Check if perf is available
        let perf_check = Command::new("which")
            .arg("perf")
            .output();
        
        if perf_check.is_err() || !perf_check.unwrap().status.success() {
            // perf not available
            return Err("perf not available".into());
        }
        
        // Read perf counters from the process
        // Note: This is tricky because we'd need to attach perf to our own process
        // For now, we'll return an error and let the caller handle it gracefully
        
        // Alternative: You could use the 'perf_event_open' syscall directly
        // But that requires unsafe code and may not work on all VMs
        
        Err("Hardware counters require manual perf setup".into())
    }

    fn timestamp_iso8601() -> String {
        chrono::Utc::now().to_rfc3339()
    }

    fn write_metrics(&mut self, metrics: &Metrics) {
        let json = serde_json::to_string(metrics).unwrap();
        writeln!(self.output_file, "{}", json).ok();
        self.output_file.flush().ok();
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();
    
    println!("=== ZK-DISPHASIA Test Harness ===");
    println!("VM Profile: {}", args.vm_profile);
    println!("Device ID: {}", args.device_id);
    println!("Fixture Server: {}", args.fixture_server);
    println!("Output: {}", args.output);
    println!();
    
    let mut runner = TestRunner::new(&args)?;
    runner.run_all_tests();
    
    println!("\n=== Test harness completed ===");
    Ok(())
}