////////////////////////////////////////////////////////////////////////////
/// Setup the Public Ceremony

use std::fs::{self, File};
use std::io::{self, Write, BufReader};
use std::path::Path;
use halo2_proofs::poly::commitment::Params;
use halo2_proofs::poly::kzg::commitment::ParamsKZG;
use halo2_proofs::halo2curves::bn256::Bn256;

const HALO2_K: u32 = 8;
const PARAMS_DIR: &str = "./trusted_setup";
const PARAMS_FILE: &str = "kzg_bn254_8.params";

fn main() -> Result<(), Box<dyn std::error::Error>> {
    
    // Create directory for parameters
    fs::create_dir_all(PARAMS_DIR)?;
    let params_path = Path::new(PARAMS_DIR).join(PARAMS_FILE);
    
    println!("KZG trusted setup parameters for k={}.", HALO2_K);
    
    // Check if params already exist
    if params_path.exists() {
        println!("Param file at: {}", params_path.display());
        print!("Do you want to regenerate or verify? (r/v): ");
        io::stdout().flush()?;
        
        let mut input = String::new();
        io::stdin().read_line(&mut input)?;
        
        if !input.trim().eq_ignore_ascii_case("r") {
            verify_and_display_params(&params_path)?;
            return Ok(());
        }
    }
    
    println!("\nDownload Hermez/PSE Ceremony from https://trusted-setup-halo2kzg.s3.eu-central-1.amazonaws.com/hermez-raw-{}, rename to {PARAMS_FILE}, place in a folder called {}, re-run this script when done to verify", HALO2_K, PARAMS_DIR);
    
    Ok(())
}

fn verify_and_display_params(params_path: &Path) -> Result<(), Box<dyn std::error::Error>> {
    
    // Read and verify the parameters
    let mut file = BufReader::new(File::open(params_path)?);
    let params = ParamsKZG::<Bn256>::read(&mut file)?;
    
    // Get file size
    let metadata = fs::metadata(params_path)?;
    let file_size = metadata.len();
    
    //Print statistics
    println!("\nParameter Details:");
    println!("  k value: {}", params.k());
    println!("  Max degree: {} (2^{})", 1 << params.k(), params.k());
    println!("  File size: {} bytes ({:.2} KB)", file_size, file_size as f64 / 1024.0);
    println!("  Location: {}", params_path.display());
    
    Ok(())
}