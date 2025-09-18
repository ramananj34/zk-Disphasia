//Necessary Libraries:

//Lets us convert Rust to and from formats that can be sent over the network
use serde::{Deserialize, Serialize};

//Imports operations for curve25519, maintained by Dalek. CompressedRistretto is a point on a Risetto Prime Order Subgroup, Scalar is just a scalar for ECC operations
use curve25519_dalek_ng::{ristretto::CompressedRistretto, scalar::Scalar};

//Bulletproofs library, mainatined by Dalek:
//BulletproofGens are precomputed ECC points for proofs
//PedersenGens are Pedersen Generators for Pedersen Commitments (the actual commitments)
//RangeProof is the specific type of comitment we are using that is consistent with BulletProofs
use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};

//Fiat-Shamir Transcript used in conjunction with aggregation to ensure that the proofs reflect the correct information
use merlin::Transcript;

//Standard HashMap library
use std::collections::HashMap;

//-------------------------------------------------

//Structures I will use

//This will be a proof
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceProof {
    pub device_id: u32, //Corresponds to the device which generated the proof
    pub commitment: CompressedRistretto, //Secretly store the state
    pub proof: Vec<u8>, // Serialized RangeProof, the evidence that the comitment satisfies the conditions
    pub timestamp: u64, //Stores when the proof was created
}

//This will represent an IoT device
#[derive(Debug, Clone)]
pub struct IoTDevice {
    pub id: u32, //Unique ID
    pub state: u8, // 0 or 1
    pub blinding_factor: Scalar, //For Petersen commitment, random secret
}

//Bulletproof Aggregator
pub struct BulletproofsAggregator {
    pub bulletproof_gens: BulletproofGens, //Precomputed Bulletproof generators (for batches aggregation)
    pub pedersen_gens: PedersenGens, //Precomputed Pedersen Generator Commitments (for batches verification)
    pub devices: HashMap<u32, DeviceProof>, //Stores devices and proofs
    pub threshold_percentage: f64, //What percent does the aggregation have to meet?
}

#[derive(Debug)]
pub struct AggregationStats {
    pub total_devices: usize, //Total devices
    pub threshold_count: usize, //Number of devices meeting condition
    pub threshold_met: bool, //Whether or not the condition is met
    pub threshold_percentage: f64, //Percentage necessary
}

fn main() {
    println!("Hello, World");
}