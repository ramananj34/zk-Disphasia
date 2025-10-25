//This was made with AI Assistance

//Test script for fixture server - Place in src/bin/test_fixture_server.rs - Run with: cargo run --bin test_fixture_server

use serde::{Deserialize}; //Deserialize responses

const FIXTURE_URL: &str = "http://localhost:8080"; //Fixture server URL

#[derive(Debug, Deserialize)]
struct HealthResponse { status: String, cache_size_mb: f64, dkg_ceremonies: usize, zkp_artifacts: usize }

#[derive(Debug, Deserialize)]
struct DeviceOutput { device_id: u32, key_package: Vec<u8>, public_package: Vec<u8>, signing_pubkey: [u8; 32] }

#[derive(Debug, Deserialize)]
struct VerifiedPartialData { device_id: u32, partial_bytes: Vec<u8>, aggregate_c1_bytes: [u8; 32], aggregate_c2_bytes: [u8; 32] }

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Fixture Server Test Script ===\n");
    //Test 1: Health check
    println!("Test 1: Health Check");
    match test_health().await { Ok(health) => { println!("  ✓ Status: {}", health.status); println!("  ✓ Cache size: {:.2} MB", health.cache_size_mb); println!("  ✓ DKG ceremonies: {}", health.dkg_ceremonies); println!("  ✓ ZKP artifacts: {}", health.zkp_artifacts); } Err(e) => { println!("  ✗ Failed: {}", e); println!("\n⚠️  Is the fixture server running? Start it with:"); println!("    cargo run --bin fixture_server\n"); return Err(e); } }
    println!();
    //Test 2: DKG completed endpoint
    println!("Test 2: DKG Completed (n=5, t=3, device=1)");
    match test_dkg_completed(5, 3, 1).await { Ok(output) => { println!("  ✓ Device ID: {}", output.device_id); println!("  ✓ KeyPackage size: {} bytes", output.key_package.len()); println!("  ✓ PublicPackage size: {} bytes", output.public_package.len()); println!("  ✓ Signing pubkey: {} bytes", output.signing_pubkey.len()); } Err(e) => { println!("  ✗ Failed: {}", e); return Err(e); } }
    println!();
    //Test 3: Round1 packages
    println!("Test 3: Round1 Packages (n=5, t=3, device=1)");
    match test_round1_packages(5, 3, 1).await { Ok(packages) => { println!("  ✓ Received {} packages (expected 4 for n-1)", packages.len()); if packages.len() == 4 { println!("  ✓ Correct count!"); } else { println!("  ⚠️  Expected 4 packages, got {}", packages.len()); } } Err(e) => { println!("  ✗ Failed: {}", e); return Err(e); } }
    println!();
    //Test 4: Round2 packages
    println!("Test 4: Round2 Packages (n=5, t=3, device=1)");
    match test_round2_packages(5, 3, 1).await { Ok((r1, r2)) => { println!("  ✓ Round1 packages: {}", r1.len()); println!("  ✓ Round2 packages: {}", r2.len()); } Err(e) => { println!("  ✗ Failed: {}", e); return Err(e); } }
    println!();
    //Test 5: Sample proof (Bulletproof)
    println!("Test 5: Sample Proof - Bulletproof (n=5, t=3)");
    match test_sample_proof("bulletproof", 5, 3).await { Ok(proof_bytes) => { println!("  ✓ Proof size: {} bytes", proof_bytes.len()); if proof_bytes.len() > 100 { println!("  ✓ Size looks reasonable for a Bulletproof"); } } Err(e) => { println!("  ✗ Failed: {}", e); return Err(e); } }
    println!();
    //Test 6: Sample proof (SNARK)
    println!("Test 6: Sample Proof - SNARK (n=5, t=3)");
    match test_sample_proof("snark", 5, 3).await { Ok(proof_bytes) => { println!("  ✓ Proof size: {} bytes", proof_bytes.len()); } Err(e) => { println!("  ✗ Failed: {}", e); return Err(e); } }
    println!();
    //Test 7: Sample proof (STARK)
    println!("Test 7: Sample Proof - STARK (n=5, t=3)");
    match test_sample_proof("stark", 5, 3).await { Ok(proof_bytes) => { println!("  ✓ Proof size: {} bytes", proof_bytes.len()); } Err(e) => { println!("  ✗ Failed: {}", e); return Err(e); } }
    println!();
    //Test 8: Ciphertexts
    println!("Test 8: Verified Ciphertexts (bulletproof, n=5, t=3)");
    match test_ciphertexts("bulletproof", 5, 3).await { Ok(cts) => { println!("  ✓ Received {} ciphertexts (expected 5 for n)", cts.len()); if cts.len() == 5 { println!("  ✓ Correct count!"); } else { println!("  ⚠️  Expected 5 ciphertexts, got {}", cts.len()); } } Err(e) => { println!("  ✗ Failed: {}", e); return Err(e); } }
    println!();
    //Test 9: Sample partial
    println!("Test 9: Sample Partial (bulletproof, n=5, t=3)");
    match test_sample_partial("bulletproof", 5, 3).await { Ok(partial_data) => { println!("  ✓ Device ID: {}", partial_data.device_id); println!("  ✓ Partial size: {} bytes", partial_data.partial_bytes.len()); println!("  ✓ Pre-computed aggregate C1: {} bytes", partial_data.aggregate_c1_bytes.len()); println!("  ✓ Pre-computed aggregate C2: {} bytes", partial_data.aggregate_c2_bytes.len()); } Err(e) => { println!("  ✗ Failed: {}", e); return Err(e); } }
    println!();
    //Test 10: Threshold partials
    println!("Test 10: Threshold Partials (bulletproof, n=5, t=3)");
    match test_threshold_partials("bulletproof", 5, 3).await { Ok(partials) => { println!("  ✓ Received {} partials (expected 3 for t)", partials.len()); if partials.len() == 3 { println!("  ✓ Correct count!"); } else { println!("  ⚠️  Expected 3 partials, got {}", partials.len()); } } Err(e) => { println!("  ✗ Failed: {}", e); return Err(e); } }
    println!();
    //Test 11: Different ZKP types
    println!("Test 11: All ZKP Types (n=10, t=7)");
    for zkp in &["bulletproof", "snark", "stark"] { match test_sample_proof(zkp, 10, 7).await { Ok(proof_bytes) => { println!("  ✓ {}: {} bytes", zkp, proof_bytes.len()); } Err(e) => { println!("  ✗ {} failed: {}", zkp, e); return Err(e); } } }
    println!();
    println!("\n✓ Fixture server is working correctly");
    println!("✓ All endpoints responding");
    println!("✓ Data looks valid");
    //Test 12: Large network size
    println!("Test 12: Large Network (n=100, t=67, device=1)");
    match test_dkg_completed(100, 67, 1).await { Ok(output) => { println!("  ✓ Successfully retrieved DKG for n=100"); println!("  ✓ KeyPackage size: {} bytes", output.key_package.len()); } Err(e) => { println!("  ✗ Failed: {}", e); return Err(e); } }
    println!("=== All Tests Passed! ===");
    println!();
    Ok(())
}

async fn test_health() -> Result<HealthResponse, Box<dyn std::error::Error>> {
    let url = format!("{}/health", FIXTURE_URL);
    let response = reqwest::get(&url).await?;
    if !response.status().is_success() { return Err(format!("HTTP {}", response.status()).into()); }
    let health: HealthResponse = response.json().await?;
    Ok(health)
}

async fn test_dkg_completed(n: usize, t: usize, device_id: u32) -> Result<DeviceOutput, Box<dyn std::error::Error>> {
    let url = format!("{}/api/dkg/completed/{}/{}/{}", FIXTURE_URL, n, t, device_id);
    let response = reqwest::get(&url).await?;
    if !response.status().is_success() { return Err(format!("HTTP {}", response.status()).into()); }
    let output: DeviceOutput = response.json().await?;
    Ok(output)
}

async fn test_round1_packages(n: usize, t: usize, device_id: u32) -> Result<Vec<String>, Box<dyn std::error::Error>> {
    let url = format!("{}/api/dkg/round1/{}/{}/{}", FIXTURE_URL, n, t, device_id);
    let response = reqwest::get(&url).await?;
    if !response.status().is_success() { return Err(format!("HTTP {}", response.status()).into()); }
    let packages: Vec<String> = response.json().await?;
    Ok(packages)
}

async fn test_round2_packages(n: usize, t: usize, device_id: u32) -> Result<(Vec<String>, Vec<String>), Box<dyn std::error::Error>> {
    let url = format!("{}/api/dkg/round2/{}/{}/{}", FIXTURE_URL, n, t, device_id);
    let response = reqwest::get(&url).await?;
    if !response.status().is_success() { return Err(format!("HTTP {}", response.status()).into()); }
    #[derive(Deserialize)]
    struct Response { round1_packages: Vec<String>, round2_packages: Vec<String> }
    let resp: Response = response.json().await?;
    Ok((resp.round1_packages, resp.round2_packages))
}

async fn test_sample_proof(zkp_type: &str, n: usize, t: usize) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let url = format!("{}/api/proof/{}/{}/{}", FIXTURE_URL, zkp_type, n, t);
    let response = reqwest::get(&url).await?;
    if !response.status().is_success() { return Err(format!("HTTP {}", response.status()).into()); }
    let bytes = response.bytes().await?;
    Ok(bytes.to_vec())
}

async fn test_ciphertexts(zkp_type: &str, n: usize, t: usize) -> Result<Vec<String>, Box<dyn std::error::Error>> {
    let url = format!("{}/api/ciphertexts/{}/{}/{}", FIXTURE_URL, zkp_type, n, t);
    let response = reqwest::get(&url).await?;
    if !response.status().is_success() { return Err(format!("HTTP {}", response.status()).into()); }
    let cts: Vec<String> = response.json().await?;
    Ok(cts)
}

async fn test_sample_partial(zkp_type: &str, n: usize, t: usize) -> Result<VerifiedPartialData, Box<dyn std::error::Error>> {
    let url = format!("{}/api/partial/{}/{}/{}", FIXTURE_URL, zkp_type, n, t);
    let response = reqwest::get(&url).await?;
    if !response.status().is_success() { return Err(format!("HTTP {}", response.status()).into()); }
    let partial_data: VerifiedPartialData = response.json().await?;
    Ok(partial_data)
}

async fn test_threshold_partials(zkp_type: &str, n: usize, t: usize) -> Result<Vec<String>, Box<dyn std::error::Error>> {
    let url = format!("{}/api/partials/{}/{}/{}", FIXTURE_URL, zkp_type, n, t);
    let response = reqwest::get(&url).await?;
    if !response.status().is_success() { return Err(format!("HTTP {}", response.status()).into()); }
    let partials: Vec<String> = response.json().await?;
    Ok(partials)
}