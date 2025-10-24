use zk_disphasia_azure_test::common::{self, AggError};
use zk_disphasia_azure_test::snark::{IoTDevice, setup_halo2};
use std::collections::{HashMap, BTreeMap};
use frost_ristretto255 as frost;

fn main() -> Result<(), AggError> {
    let (n, t, states) = (5, 3, [1u8, 0, 1, 1, 0]);
    println!("Setting up DKG for {} devices with threshold {}...", n, t);

    let mut r1_secrets = Vec::new();
    let mut r1_packages = BTreeMap::new();
    for i in 1..=n {
        let (secret, package) = common::dkg_phase1(i as u32, n, t)?;
        let id = frost::Identifier::try_from(i as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
        r1_secrets.push((i as u32, secret));
        r1_packages.insert(id, package);
    }

    let mut r2_secrets = Vec::new();
    let mut r2_packages_map = HashMap::new();
    for (device_id, r1_secret) in &r1_secrets {
        let my_id = frost::Identifier::try_from(*device_id as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
        let mut received_r1 = r1_packages.clone();
        received_r1.remove(&my_id);
        let (r2_secret, r2_packages) = common::dkg_phase2(r1_secret.clone(), &received_r1)?;
        r2_secrets.push((*device_id, r2_secret));
        r2_packages_map.insert(*device_id, r2_packages);
    }

    let mut dkg = Vec::new();
    for (device_id, r2_secret) in &r2_secrets {
        let my_id = frost::Identifier::try_from(*device_id as u16).map_err(|e| AggError::CryptoError(e.to_string()))?;
        
        let mut received_r2 = BTreeMap::new();
        for (other_id, packages) in &r2_packages_map {
            if other_id != device_id {
                if let Some(pkg) = packages.get(&my_id) {
                    let other_frost_id = frost::Identifier::try_from(*other_id as u16)
                        .map_err(|e| AggError::CryptoError(e.to_string()))?;
                    received_r2.insert(other_frost_id, pkg.clone());
                }
            }
        }
        
        let mut all_r1 = r1_packages.clone();
        all_r1.remove(&my_id);
        
        let (key_package, public_key_package) = common::dkg_phase3(&r2_secret, &all_r1, &received_r2)?;
        
        dkg.push((*device_id, key_package, public_key_package));
    }


    println!("Setting up Halo2 proving/verification keys...");
    let halo2_setup = setup_halo2()?;
    let mut devs = Vec::new();
    let mut all_keys = HashMap::new();
    for (id, kpkg, ppkg) in &dkg {
        let d = IoTDevice::new(*id, t, kpkg.clone(), ppkg.clone(), HashMap::new(), halo2_setup.clone())?;
        all_keys.insert(*id, d.sig_key.verifying_key());
        devs.push(d);
    }
    for d in devs.iter_mut() {
        d.peer_keys = all_keys.clone();
        d.valid_participant_ids.clear();
        d.valid_participant_ids.insert(d.id);
        for peer_id in d.peer_keys.keys() {
            d.valid_participant_ids.insert(*peer_id);
        }
    }
    println!("Generating proofs...");
    for (i, &state) in states.iter().enumerate() {
        let proof = devs[i].generate_proof(state)?;
        for d in devs.iter_mut() {
            d.receive_proof(proof.clone())?;
        }
    }
    println!("Generating partial decryptions...");
    for i in 0..t {
        let partial = devs[i].generate_partial_decryption()?;
        for d in devs.iter_mut() {
            d.receive_partial(partial.clone()).ok();
        }
    }
    println!("Computing aggregates...");
    for d in &mut devs {
        if let Ok((sum, total)) = d.compute_aggregate() {
            println!("Device {}: sum={}/{}", d.id, sum, total);
        }
    }
    Ok(())
}