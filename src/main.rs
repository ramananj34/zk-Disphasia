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
    pub proof: Vec<u8>, //Serialized RangeProof, the evidence that the comitment satisfies the conditions
    pub timestamp: u64, //Stores when the proof was created
}

//This will represent an IoT device
#[derive(Debug, Clone)]
pub struct IoTDevice {
    pub id: u32, //Unique ID
    pub state: u8, //0 or 1
    pub blinding_factor: Scalar, //For Petersen commitment, random secret
}

//Aggregation Stats
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

//-------------------------------------------------

//The fun part

impl BulletproofsAggregator {
    //Constructor
    pub fn new(max_devices: usize, threshold_percentage: f64) -> Self {
        //Takes in the max number of devices and threshold percentage defined earlier

        //Generate bulletproof and pedersen generators for the maximum number of devices. These will be used for aggregation
        //Each proof will be 64-bit range (0 or 1, but we use 64-bit for compatibility)
        let bulletproof_gens = BulletproofGens::new(64, max_devices);
        let pedersen_gens = PedersenGens::default();
        
        //Defines what we need. The generators we just made, the devices/commitments, and the threshold percentage. 
        Self {
            bulletproof_gens,
            pedersen_gens,
            devices: HashMap::new(),
            threshold_percentage,
        }
    }

    //Generate a zero-knowledge proof for a device's state (0 or 1)
    pub fn generate_device_proof(&self, device: &IoTDevice) -> Result<DeviceProof, Box<dyn std::error::Error>> {
        //Takes in the IoT device, and creates a proof or an error if something goes wrong

        //In practice we need a transcript, which is a register of the inputs to ensure that they are tamper proof. This includes replay attacks and proof collisions if the states are the same
        let mut transcript = Transcript::new(b"IoT Device State Proof");
        transcript.append_message(b"device_id", &device.id.to_le_bytes());
        
        //Create commitment to the device state. It is a pederson commitment that takes the state and binding factor (the aformentioned secret)
        let commitment = self.pedersen_gens.commit(
            Scalar::from(device.state as u64),
            device.blinding_factor,
        );

        //Generate range proof that the committed value is either 0 or 1, using bulletproofs on top of the Pedersen Commitment
        //The transcript is passed to prove_single and used internally by Bulletproofs
        //Also takes the generators, device state, binding factor, and 1 (one bit because it is 0 or 1)
        let (proof, _) = RangeProof::prove_single(&self.bulletproof_gens, &self.pedersen_gens, &mut transcript, device.state as u64, &device.blinding_factor, 1)?;

        //Serialize the proof for transmission
        let proof_bytes = bincode::serialize(&proof)?;

        //Now we create and return the proof. It contains the device id, commitment, proof, and timestamp
        Ok(DeviceProof {
            device_id: device.id,
            commitment: commitment.compress(),
            proof: proof_bytes,
            timestamp: std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)?.as_secs(),
        })
    }


    //Verify the proof
    pub fn verify_device_proof(&self, device_proof: &DeviceProof) -> Result<bool, Box<dyn std::error::Error>> {
        //Takes in the proof, and returns whether it is valid or invalid

        //As mentioned before, we need a transcript to ensure that there was no tampering. We use the ID again
        let mut transcript = Transcript::new(b"IoT Device State Proof");
        transcript.append_message(b"device_id", &device_proof.device_id.to_le_bytes());
        
        //Deserialize the proof
        let proof: RangeProof = bincode::deserialize(&device_proof.proof)?;
        
        //Decompress the commitment
        let commitment = device_proof.commitment.decompress().ok_or("Failed to decompress commitment")?;

        //Verify the range proof
        let verification_result = proof.verify_single(&self.bulletproof_gens,&self.pedersen_gens,&mut transcript, &commitment.compress(),1);

        //Return if the proof is valid or not
        Ok(verification_result.is_ok())
    }

    //Add or update a device proof in the aggregator
    pub fn add_device_proof(&mut self, device_proof: DeviceProof) -> Result<(), Box<dyn std::error::Error>> {
        //Takes in the proof, and returns if it was sucsesfully added or not

        //Verify the proof before adding
        if !self.verify_device_proof(&device_proof)? {
            return Err("Invalid device proof".into());
        }

        //Add the proof
        self.devices.insert(device_proof.device_id, device_proof);

        //Returns if it worked or not
        Ok(())
    }

    //Remove a device from the aggregation
    pub fn remove_device(&mut self, device_id: u32) {
        //Takes in the device ID and removes the proof

        //Very straight forward
        self.devices.remove(&device_id);
    }

    //Check if the threshold is met using homomorphic properties. This creates an aggregated proof without revealing individual values
    pub fn check_threshold_with_proof(&self) -> Result<bool, Box<dyn std::error::Error>> {

        //Gets total devices and the number of devices we need
        let total_devices = self.devices.len();
        let required_active = ((total_devices as f64) * (self.threshold_percentage / 100.0)).ceil() as usize;

        //If we have no devices, then we just return
        if total_devices == 0 {
            return Ok(false);
        }

        //Verify all the proofs
        for device_proof in self.devices.values() {
            if !self.verify_device_proof(device_proof)? {
                return Err("Invalid device proof".into());
            }
        }

        //Homomorphic aggregation
        let mut sum_commitment = self.pedersen_gens.commit(Scalar::zero(), Scalar::zero()); //Pedersen commitment
        for device_proof in self.devices.values() { //For each device
            let commitment = device_proof.commitment.decompress() //Get the commitment
                .ok_or("Failed to decompress commitment")?;
            sum_commitment = sum_commitment + commitment; //Add the commitment
        }

        //Extract total count using discrete log (not ideal, but there is no other way without breaking secrecy)
        let active_count = self.discrete_log_extract(sum_commitment, total_devices)?;
        
        //Return threshold result
        Ok(active_count >= required_active)
    }

    //Extract discrete log using baby-step giant-step algorithm
    fn discrete_log_extract(&self, point: curve25519_dalek_ng::ristretto::RistrettoPoint, max_devices: usize) -> Result<usize, Box<dyn std::error::Error>> {
        let generator = self.pedersen_gens.B; //Pedersen generator for values
        
        //Baby-step giant-step for efficiency with larger device counts
        let sqrt_max = ((max_devices as f64).sqrt() as usize) + 1;
        let mut baby_steps = std::collections::HashMap::new();
        
        //Baby steps:
        let mut current = curve25519_dalek_ng::ristretto::RistrettoPoint::default();
        for i in 0..sqrt_max { //Precompute points
            baby_steps.insert(current.compress(), i);
            if i < sqrt_max - 1 { current = current + generator; }
        }
        
        //Giant steps:
        let giant_step = generator * Scalar::from(sqrt_max as u64);
        let mut gamma = point;
        
        for j in 0..sqrt_max {
            if let Some(&i) = baby_steps.get(&gamma.compress()) {
                let result = j * sqrt_max + i;
                if result <= max_devices {
                    return Ok(result);
                }
            }
            gamma = gamma - giant_step;
        }
        
        Err("Discrete log not found - sum may be outside expected range".into())
    }


    //Get aggregation statistics
    pub fn get_stats(&self) -> AggregationStats {
        let total_devices = self.devices.len();
        let threshold_count = ((total_devices as f64) * (self.threshold_percentage / 100.0)).ceil() as usize;
        let threshold_met = self.check_threshold_with_proof().unwrap_or(false);

        AggregationStats {
            total_devices,
            threshold_count,
            threshold_met,
            threshold_percentage: self.threshold_percentage, //Use the stored percentage
        }
    }

}






//Testing 
//Bulletproof Aggregator. This is just for testing, the class has everything else I need
pub struct BulletproofsAggregator {
    pub bulletproof_gens: BulletproofGens, //Precomputed Bulletproof generators (for batches aggregation)
    pub pedersen_gens: PedersenGens, //Precomputed Pedersen Generator Commitments (for batches verification)
    pub devices: HashMap<u32, DeviceProof>, //Stores devices and proofs
    pub threshold_percentage: f64, //What percent does the aggregation have to meet?
}