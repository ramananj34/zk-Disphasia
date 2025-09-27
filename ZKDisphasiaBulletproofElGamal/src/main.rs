////////////////////////////////////////////////////////////////////////////
/// Libraries

//Serialization/deserialization
use serde::{Deserialize, Serialize, Deserializer, Serializer};
use serde_with::{serde_as, Bytes};

//The curve
use curve25519_dalek_ng::{ristretto::{CompressedRistretto, RistrettoPoint}, scalar::Scalar, traits::Identity, constants::RISTRETTO_BASEPOINT_POINT};

//Bulletproofs (Dalek)
use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};

//Transcript
use merlin::Transcript;

//Frost
use frost_ristretto255 as frost;

//ECDSA
use ed25519_dalek::{SigningKey, VerifyingKey, Signature, Signer, Verifier};

//Side Channel Protection
use subtle::ConstantTimeEq;
use zeroize::Zeroize;

//Random
use rand::rngs::OsRng;

//Standard Data Structures
use std::collections::{HashMap, BTreeMap};
use std::error::Error;

////////////////////////////////////////////////////////////////////////////
/// Configuration

const PROOF_EXPIRATION_SECS: u64 = 300; //How long proofs last before expiration (5 minutes)
const RECOMPUTE_INTERVAL_SECS: u64 = 30; //How often to recompute the aggregate
const MAX_DEVICES: usize = 10000; //Max devices in the network
const MAX_BULLETPROOF_BYTES: usize = 8192; //Max bulletproof size (for DoS protection)
const RATE_WINDOW_SECS: u64 = 10; //Rate limiting - how often to reset peer limits
const MAX_MESSAGES_PER_WINDOW: u32 = 10; //Rate limiting - maximum messages per window

////////////////////////////////////////////////////////////////////////////
/// Actual Logic

//The first struct is a custom error type for the aggregation system
#[derive(Debug)]
pub enum AggError {
    InvalidProof(String), //Proof validation failed
    ExpiredProof, //Proof expired
    ThresholdNotMet, //Not enough partial decryptions
    CryptoError(String), //Generic cryptographic error
    DkgIncomplete, //DKG setup not done
    RateLimited, //A device is blocked due to rate limiting
}
impl std::fmt::Display for AggError { //Now we make the errors more verbose for debugging:
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
impl Error for AggError {} //Make it behave like a error

//This is custom serialization/desesrialization logic for cryptography
macro_rules! impl_serde_wrapper {
    ($name:ident, $inner:ty, $size:expr, $from:expr) => {
        //Name is the new wrapper struct, inner is the type it wraps, size:expr is the expected size, and from:expr is a function to rebuild
        #[derive(Debug, Clone)]
        pub struct $name(pub $inner);
        //Serialization steps:
        impl Serialize for $name {
            fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
                s.serialize_bytes(self.0.as_bytes())
            }
        }
        //Deserialization steps:
        impl<'de> Deserialize<'de> for $name {
            fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
                let bytes = Vec::<u8>::deserialize(d)?;
                if bytes.len() != $size {
                    return Err(serde::de::Error::custom(concat!("Invalid ", stringify!($name), " length")));
                }
                let mut arr = [0u8; $size];
                arr.copy_from_slice(&bytes);
                Ok($name($from(arr)))
            }
        }
        //Make it easier to go to and from the wrapper and inner type
        impl From<$inner> for $name {
            fn from(v: $inner) -> Self { $name(v) }
        }
        impl From<$name> for $inner {
            fn from(v: $name) -> Self { v.0 }
        }
    };
}
//Use the custom wrapper on CompressedRistertto and Scalars, which do not have serde built in
impl_serde_wrapper!(SerializableCompressedRistretto, CompressedRistretto, 32, CompressedRistretto);
impl_serde_wrapper!(SerializableScalar, Scalar, 32, Scalar::from_bytes_mod_order);

//This will be a device proof
#[serde_as]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceProof {
    pub device_id: u32, //Unique device ID
    pub timestamp: u64, //Timestamp
    pub elgamal_c1: SerializableCompressedRistretto, //c1 (ElGamal)
    pub elgamal_c2: SerializableCompressedRistretto, //c2 (ElGamal)
    pub commitment: SerializableCompressedRistretto, //Pederson
    pub bulletproof: Vec<u8>, //Bulletproof
    #[serde_as(as = "Bytes")]
    pub signature: [u8; 64], //DSA
}

//This will be a partial decryption
#[serde_as]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PartialDecryption {
    pub device_id: u32, //Device ID
    pub timestamp: u64, //Timestamp
    pub partial: SerializableCompressedRistretto, //Decryption
    pub proof: SchnorrProof, //Schnorr proof for decryption
    #[serde_as(as = "Bytes")]
    pub signature: [u8; 64], //Signature
}

//Now we have our non-interactive Schnorr proof for discrete log equality
//Use Fiat-Shamir transform to make it non-interactive
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SchnorrProof {
    pub commitment: SerializableCompressedRistretto,
    pub response: SerializableScalar,
}
impl SchnorrProof {
    //First we generate the proof
    fn prove_dlog_equality(secret: &Scalar, sum_c1: &RistrettoPoint, partial: &RistrettoPoint, ts: u64, id: u32) -> Self {
        let r = Scalar::random(&mut OsRng); //Create a random nonce
        let commitment = sum_c1 * r; //Comitment = r*sum_c1
        let challenge = Self::challenge(&sum_c1, &partial, &commitment, ts, id); //Helper function Fiat-Shamir challange
        let response = r + challenge * secret; //Response is r+cx
        Self { commitment: commitment.compress().into(), response: response.into() }
    }
    //Now we can verify the proof
    fn verify_dlog_equality(&self, sum_c1: &RistrettoPoint, partial: &RistrettoPoint, ts: u64, id: u32) -> bool {
        let commitment = match self.commitment.0.decompress() { Some(c) => c, None => return false }; //Get the commitment point
        let challenge = Self::challenge(&sum_c1, &partial, &commitment, ts, id); //Recompute the challange
        sum_c1 * self.response.0 == commitment + partial * challenge //Verify the challange and validity of the proof
    }
    //Helper function for the challange (Fiat-Shamir Transform)
    fn challenge(sum_c1: &RistrettoPoint, partial: &RistrettoPoint, commitment: &RistrettoPoint, ts: u64, id: u32) -> Scalar {
        let mut t = Transcript::new(b"schnorr-dlog-equality"); //New Merlin Transcript. Label gives domain-seperation
        t.append_u64(b"timestamp", ts); //Binding data (replay attack protection)
        t.append_u64(b"device", id as u64); //Binding data (replay attack protection)
        t.append_message(b"sum_c1", sum_c1.compress().as_bytes()); //State data
        t.append_message(b"partial", partial.compress().as_bytes()); //State data
        t.append_message(b"commitment", commitment.compress().as_bytes()); //State data
        //Now we use the Merlin transcript to derive a strong scalar challange (Hashes internlly). It is deterministic on the state
        let mut bytes = [0u8; 64];
        t.challenge_bytes(b"challenge", &mut bytes);
        Scalar::from_bytes_mod_order_wide(&bytes)
    }
}

//Now we have the IoT Device
pub struct IoTDevice {
    pub id: u32, //Device ID
    pub frost_key_package: frost::keys::KeyPackage, //Private key share for FROST
    pub group_public: frost::keys::PublicKeyPackage, //Public key for FROST
    pub signing_key: SigningKey, //ECDSA signing key
    pub peer_keys: HashMap<u32, VerifyingKey>, //Peer public signing keys
    pub received_proofs: HashMap<u32, DeviceProof>, //Proofs recieved
    pub received_partials: HashMap<u32, PartialDecryption>, //Partials recieved
    pub current_aggregate_c1: Option<RistrettoPoint>, //Running sum of encrypted states/Risteretto Points
    pub current_aggregate_c2: Option<RistrettoPoint>, //Running sum of encrypted states/Risteretto Points
    bulletproof_gens: BulletproofGens, //Bulletproof Generators
    pedersen_gens: PedersenGens, //Pederson Generators
    pub threshold: usize, //Threshold for full decryptions
    peer_rates: HashMap<u32, (u64, u32)>, //Rate limiting for Peers
    last_recompute: u64,
}
impl IoTDevice {
    //Constructor
    pub fn new(id: u32, threshold: usize, key_package: frost::keys::KeyPackage, 
               public_package: frost::keys::PublicKeyPackage, peer_keys: HashMap<u32, VerifyingKey>) -> Self {
        Self {
            id, frost_key_package: key_package, group_public: public_package, //No FROST setup yet
            signing_key: SigningKey::generate(&mut OsRng), peer_keys, //Random signing key
            received_proofs: HashMap::new(), received_partials: HashMap::new(), //Empty maps
            current_aggregate_c1: None, current_aggregate_c2: None, //No current aggregate
            bulletproof_gens: BulletproofGens::new(64, 1), //Random generator
            pedersen_gens: PedersenGens::default(), threshold, //Random generator
            peer_rates: HashMap::new(), //Empty HashMap
            last_recompute: 0,
        }
    }
    //Generate a proof
    pub fn generate_proof(&self, state: u8) -> Result<DeviceProof, AggError> {
        //Verify sate is 0 or 1
        if state > 1 { return Err(AggError::CryptoError("State must be 0 or 1".into())); }
        //Get timestamp, random nonce, and Risteretto base point
        let (ts, mut r, g) = (current_timestamp(), Scalar::random(&mut OsRng), RISTRETTO_BASEPOINT_POINT);
        //Get public key
        let h = frost_pubkey_to_point(&self.group_public.verifying_key())?;
        //ElGamal Encryption (c1 and c2)
        let (c1, c2) = (g * r, g * Scalar::from(state as u64) + h * r);
        //Pederson Commitment (hide and bind)
        let commitment = self.pedersen_gens.commit(Scalar::from(state as u64), r);
        //Use a Merlin Transcript to generate a challange
        let mut transcript = Transcript::new(b"iot-range-proof");
        //Generate the Bulletproof
        let (proof, _) = RangeProof::prove_single(&self.bulletproof_gens, &self.pedersen_gens, &mut transcript, state as u64, &r, 8).map_err(|e| { r.zeroize(); AggError::CryptoError(format!("Bulletproof failed: {:?}", e)) })?;
        //Safely delete the temporary scalar
        r.zeroize();
        //Construct and return the proof
        Ok(DeviceProof {
            device_id: self.id, timestamp: ts,
            elgamal_c1: c1.compress().into(), elgamal_c2: c2.compress().into(),
            commitment: commitment.compress().into(), bulletproof: proof.to_bytes(),
            signature: self.sign_data(&[&ts.to_le_bytes(), &self.id.to_le_bytes(), c1.compress().as_bytes(), c2.compress().as_bytes()]),
        })
    }
    //Get rid of expired proofs
    pub fn cleanup_expired_proofs(&mut self) {
        //Find the expiration threshold
        let thresh = current_timestamp().saturating_sub(PROOF_EXPIRATION_SECS);
        //Get rid of expired proofs
        self.received_proofs.retain(|_, p| p.timestamp > thresh);
        //Get rid of expired partials
        self.received_partials.retain(|_, p| p.timestamp > thresh);
        //Recompute the aggregate
        self.maybe_recompute();
    }
    //Wrapper to recompute the aggregate to cut down on how often we do it
    fn maybe_recompute(&mut self) {
        let now = current_timestamp();
        //Only recompute the aggregate if a certain time interval has passed
        if now >= self.last_recompute + RECOMPUTE_INTERVAL_SECS {
            self.recompute_aggregate();
            self.last_recompute = now;
        }
    }
    //Recompute the aggregate
    fn recompute_aggregate(&mut self) {
        if self.received_proofs.is_empty() { //If we have no proofs, the aggreagete is zero
            self.current_aggregate_c1 = None;
            self.current_aggregate_c2 = None;
        } else { //If we have proofs
            //Initialize c1/c2
            let (mut c1, mut c2) = (RistrettoPoint::identity(), RistrettoPoint::identity());
            //For each proof
            for p in self.received_proofs.values() {
                if let (Some(p1), Some(p2)) = (p.elgamal_c1.0.decompress(), p.elgamal_c2.0.decompress()) { //Decompress the proof
                    c1 += p1; c2 += p2; //Sum the aggreagte
                }
            }
            //Now we store the aggregate in the device state
            self.current_aggregate_c1 = Some(c1);
            self.current_aggregate_c2 = Some(c2);
        }
    }
    //Enforce the rate limiting logic
    fn check_rate(&mut self, id: u32) -> Result<(), AggError> {
        let now = current_timestamp();
        //Get the P2P neighbor from the hashmap or make a new entry
        let entry = self.peer_rates.entry(id).or_insert((now, 0));
        //If window is expiried, make a new window
        if now >= entry.0 + RATE_WINDOW_SECS { *entry = (now, 0); }
        //If device has too many entries, Rate Limit Error it
        if entry.1 >= MAX_MESSAGES_PER_WINDOW { return Err(AggError::RateLimited); }
        //Increment message count and return
        entry.1 += 1;
        Ok(())
    }
    //Handel the recieving of a proof
    pub fn receive_proof(&mut self, proof: DeviceProof) -> Result<(), AggError> {
        //First we check the rate limiting
        self.check_rate(proof.device_id)?;
        let now = current_timestamp();
        //Now we make sure the proof is not expired
        if proof.timestamp + PROOF_EXPIRATION_SECS < now { return Err(AggError::ExpiredProof); }
        //Now we make sure the proof is not a duplicate
        if self.received_proofs.get(&proof.device_id).map_or(false, |e| e.timestamp + PROOF_EXPIRATION_SECS > now) {
            return Err(AggError::InvalidProof("Duplicate proof".into()));
        }
        //Now we make sure the proof is not too large
        if proof.bulletproof.len() > MAX_BULLETPROOF_BYTES { return Err(AggError::InvalidProof("Bulletproof too large".into())); }
        //Now we verfiy the signature
        let pubkey = self.peer_keys.get(&proof.device_id).ok_or(AggError::InvalidProof("Unknown device".into()))?;
        self.verify_sig(pubkey, &[&proof.timestamp.to_le_bytes(), &proof.device_id.to_le_bytes(), 
            proof.elgamal_c1.0.as_bytes(), proof.elgamal_c2.0.as_bytes()], &proof.signature)?;
        //Now we deserialize the proof and verify it
        let mut transcript = Transcript::new(b"iot-range-proof");
        RangeProof::from_bytes(&proof.bulletproof).map_err(|_| AggError::InvalidProof("Invalid bulletproof".into()))? //Decompression
            .verify_single(&self.bulletproof_gens, &self.pedersen_gens, &mut transcript, &proof.commitment.0, 8) //Verification
            .map_err(|_| AggError::InvalidProof("Bulletproof verification failed".into()))?; //Error Handling
        //Record the proof
        self.received_proofs.insert(proof.device_id, proof);
        //Recompute the aggregate (may want to change so it only recomputes )
        self.maybe_recompute();
        Ok(())
    }
    //Now we generate a partial decryption
    pub fn generate_partial_decryption(&mut self) -> Result<PartialDecryption, AggError> {
        self.recompute_aggregate(); //Make sure the aggregate is correct
        //Get c1 and timestamp
        let sum_c1 = self.current_aggregate_c1.ok_or(AggError::CryptoError("No aggregate".into()))?;
        let ts = current_timestamp();
        //Get the FROST secret key
        let mut secret = scalar_from_frost_signing(&self.frost_key_package.signing_share())?;
        //Construct the partial decryption
        let partial = sum_c1 * secret;
        //Construct the Schnorr proof for the partial
        let proof = SchnorrProof::prove_dlog_equality(&secret, &sum_c1, &partial, ts, self.id);
        //Safley delet the secret
        secret.zeroize();
        //Construct the PartialDecryption object w ith everything we did
        Ok(PartialDecryption {
            device_id: self.id, timestamp: ts, partial: partial.compress().into(), proof,
            signature: self.sign_data(&[&ts.to_le_bytes(), &self.id.to_le_bytes(), partial.compress().as_bytes()]),
        })
    }
    //Logic to recieve the partial decryptions
    pub fn receive_partial(&mut self, partial: PartialDecryption) -> Result<(), AggError> {
        //Rate check the device for DoS protection
        self.check_rate(partial.device_id)?;
        //Make sure the proof is not expired
        if partial.timestamp + PROOF_EXPIRATION_SECS < current_timestamp() { return Err(AggError::ExpiredProof); }
        //Determine the authenticity of the partial decryption
        let pubkey = self.peer_keys.get(&partial.device_id).ok_or(AggError::InvalidProof("Unknown device".into()))?;
        self.verify_sig(pubkey, &[&partial.timestamp.to_le_bytes(), &partial.device_id.to_le_bytes(), 
            partial.partial.0.as_bytes()], &partial.signature)?;
        //Add it to the aggregate
        self.received_partials.insert(partial.device_id, partial);
        Ok(())
    }
    //Now we compute the aggregate using the partial decryptions
    pub fn compute_aggregate(&mut self) -> Result<(usize, usize), AggError> {
        //Make sure the aggregate is up to date
        self.recompute_aggregate();
        //Now we get the valid proofs and valid partial decrtptions
        let thresh = current_timestamp().saturating_sub(PROOF_EXPIRATION_SECS);
        let valid_proofs: Vec<_> = self.received_proofs.values().filter(|p| p.timestamp > thresh).collect();
        if valid_proofs.is_empty() { return Ok((0, 0)); }
        let valid_partials: Vec<_> = self.received_partials.values().filter(|p| p.timestamp > thresh).collect();
        //Make sure we have the necessary number of partial decryptions
        if valid_partials.len() < self.threshold { return Err(AggError::ThresholdNotMet); }
        //Get the aggregate points
        let sum_c1 = self.current_aggregate_c1.ok_or(AggError::CryptoError("No aggregate".into()))?;
        let sum_c2 = self.current_aggregate_c2.ok_or(AggError::CryptoError("No aggregate".into()))?;
        //This will store the verified partial decryptions
        let mut verified = Vec::new();
        //For each partial
        for p in valid_partials.iter().take(self.threshold) {
            //Decompress the partial
            let point = p.partial.0.decompress().ok_or(AggError::CryptoError("Invalid partial".into()))?;
            //Verify the Schnorr proof
            if !p.proof.verify_dlog_equality(&sum_c1, &point, p.timestamp, p.device_id) {
                return Err(AggError::InvalidProof(format!("Schnorr failed for device {}", p.device_id)));
            }
            //Add it to the list of verified partials
            verified.push((p.device_id, point));
        }
        //Convert the IDs to scalars for Lagrange Interpolation
        let participants: Vec<Scalar> = verified.iter().map(|(id, _)| Scalar::from(*id as u64)).collect();
        //Now we perform Lagrange Interpolation to combine the points to C1*Secret
        let mut combined = RistrettoPoint::identity();
        for i in 0..verified.len() {
            let mut lambda = Scalar::one();
            for j in 0..verified.len() {
                if i != j { lambda *= -participants[j] * (participants[i] - participants[j]).invert(); }
            }
            combined += verified[i].1 * lambda;
        }
        //Finally, we use the Babby Step Giant Step Algorithm to extract the final aggregate
        Ok((bsgs_discrete_log(sum_c2 - combined, RISTRETTO_BASEPOINT_POINT)?, valid_proofs.len()))
    }
    //This is just ECDSA
    fn sign_data(&self, parts: &[&[u8]]) -> [u8; 64] {
        //Put all the data into a single byte vector
        let mut data = Vec::new();
        for p in parts { data.extend_from_slice(p); }
        //Sign the data
        self.signing_key.sign(&data).to_bytes()
    }
    //Also just ECDSA
    fn verify_sig(&self, key: &VerifyingKey, parts: &[&[u8]], sig: &[u8; 64]) -> Result<(), AggError> {
        //Puts all of the data into a byte vector
        let mut data = Vec::new();
        for p in parts { data.extend_from_slice(p); }
        //Get the signature
        let sig = Signature::try_from(&sig[..]).map_err(|_| AggError::InvalidProof("Invalid sig".into()))?;
        //Verify the signature
        key.verify(&data, &sig).map_err(|_| AggError::InvalidProof("Sig failed".into()))
    }
}

//This is the implementation of the Baby Step Giant Step Algorithm to obtain the DLP extraction
fn bsgs_discrete_log(target: RistrettoPoint, base: RistrettoPoint) -> Result<usize, AggError> {
    //Step size
    let m = ((MAX_DEVICES as f64).sqrt() as usize) + 1;
    //Now we do the Baby Step Table
    let mut baby = Vec::with_capacity(m);
    let mut current = RistrettoPoint::identity();
    for _ in 0..m {
        baby.push(current.compress().to_bytes());
        current += base;
    }
    //Now we do the Giant Steps Setup
    let factor = base * Scalar::from(m as u64);
    let mut gamma = target;
    //And do the Giant Steps
    for j in 0..m {
        let gamma_bytes = gamma.compress().to_bytes();
        for (i, entry) in baby.iter().enumerate() {
            if entry.ct_eq(&gamma_bytes).unwrap_u8() == 1 {
                let result = j * m + i;
                if result <= MAX_DEVICES { return Ok(result); }
            }
        }
        gamma -= factor;
    }
    //If we do not get a match, that is an error
    Err(AggError::CryptoError("Discrete log not found".into()))
}

//Here is the DKG logic
pub fn setup_dkg(num: usize, threshold: usize) -> Result<Vec<(u32, frost::keys::KeyPackage, frost::keys::PublicKeyPackage)>, AggError> {
    //Round 1 Setup
    let mut rng = OsRng;
    let mut r1_packages = BTreeMap::new();
    let mut r1_secrets = HashMap::new();
    //Round 1: 
    for i in 1..=num {
        //Each device gets a Frost Identifier
        let id = frost::Identifier::try_from(i as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
        //Each device gets a secret (Round 1 Secret) and a Package (Public Info)
        let (secret, package) = frost::keys::dkg::part1(id, num as u16, threshold as u16, &mut rng)
            .map_err(|e| AggError::CryptoError(e.to_string()))?;
        //Save the Secret and Package
        r1_secrets.insert(i as u32, secret);
        r1_packages.insert(id, package);
    }
    //Round 2: 
    let mut r2_packages = HashMap::new();
    //Each Device,
    for (i, secret) in &r1_secrets {
        //Copy Round 1 Packages
        let mut received = r1_packages.clone();
        //Remove your own packages
        let id = frost::Identifier::try_from(*i as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
        received.remove(&id);
        //Compute Round 2 Secret based on Round 1 Contributions
        let (r2_secret, packages) = frost::keys::dkg::part2(secret.clone(), &received)
            .map_err(|e| AggError::CryptoError(e.to_string()))?;
        //Store the Round 2 Packages
        r2_packages.insert(*i, (r2_secret, packages));
    }
    //Round 3:
    let mut results = Vec::new();
    for i in 1..=num {
        //Each device gets there Round 2 Secret and Packages
        let id = frost::Identifier::try_from(i as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
        let (r2_secret, _) = r2_packages.get(&(i as u32)).ok_or(AggError::DkgIncomplete)?;
        let mut received_r2 = BTreeMap::new();
        //Get all of the Round 2 Packages sent to the device
        for (j, (_, packages)) in &r2_packages {
            if *j != i as u32 {
                if let Some(p) = packages.get(&id) {
                    let sender_id = frost::Identifier::try_from(*j as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
                    received_r2.insert(sender_id, p.clone());
                }
            }
        }
        //Copy round 1 secrets and remove your own package
        let mut received_r1 = r1_packages.clone();
        received_r1.remove(&id);
        //Final FROST call, geting the final key package for the public and private keys.
        let (key_package, pubkey_package) = frost::keys::dkg::part3(r2_secret, &received_r1, &received_r2)
            .map_err(|e| AggError::CryptoError(e.to_string()))?;
        //Save the results
        results.push((i as u32, key_package, pubkey_package));
    }
    //Return the results
    Ok(results)
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

////////////////////////////////////////////////////////////////////////////
/// Main Testing Method

fn main() -> Result<(), AggError> {
    //Show Configuration
    println!("\n\nZK-DISPHASIA in Action\n");
    println!("Configuration:\nProof expiration: every {} seconds\n", PROOF_EXPIRATION_SECS);
    
    //DKG Setup
    let (num_devices, threshold, states) = (5, 3, [1u8, 0, 1, 1, 0]);
    println!("Setting up DKG for {} devices (threshold: {})...", num_devices, threshold);
    let dkg_results = setup_dkg(num_devices, threshold)?;
    println!("DKG Setup Succsess");

    //Create the Devices
    println!("Creating the Devices");
    let mut devices = Vec::new();
    let mut all_keys = HashMap::new();
    //Giving them Keys
    for (id, key_pkg, pub_pkg) in &dkg_results {
        let d = IoTDevice::new(*id, threshold, key_pkg.clone(), pub_pkg.clone(), HashMap::new());
        all_keys.insert(*id, d.signing_key.verifying_key());
        devices.push(d);
    }
    //Sharing the Keys
    for d in devices.iter_mut() { d.peer_keys = all_keys.clone(); }
    println!("System initialized\n\nSimulating device states: {:?}", states);

    //Generating Proofs
    for (i, state) in states.iter().enumerate() {
        let proof = devices[i].generate_proof(*state)?;
        println!("  Device {} generated proof for state {}", i + 1, state);
        for (j, device) in devices.iter_mut().enumerate() {
            if let Err(e) = device.receive_proof(proof.clone()) {
                if i != j { println!("    Device {} rejected proof from {}: {}", j + 1, i + 1, e); }
            }
        }
    }

    //Generating Partial Decryptions
    println!("\nGenerating partial decryptions:");
    for i in 0..threshold {
        if devices[i].received_proofs.len() >= num_devices {
            let partial = devices[i].generate_partial_decryption()?;
            println!("  Device {} generated partial", i + 1);
            for d in devices.iter_mut() { d.receive_partial(partial.clone()).ok(); }
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