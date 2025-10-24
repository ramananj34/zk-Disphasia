use zk_disphasia_azure_test::common::{self, AggError};
use zk_disphasia_azure_test::bulletproof::IoTDevice;
use std::collections::HashMap;

fn main() -> Result<(), AggError> {
    let (n, t, states) = (5, 3, [1u8, 0, 1, 1, 0]);
    println!("Setting up DKG for {} devices with threshold {}...", n, t);
    let dkg = common::setup_dkg(n, t)?;
    let mut devs = Vec::new();
    let mut all_keys = HashMap::new();
    for (id, kpkg, ppkg) in &dkg {
        let d = IoTDevice::new(*id, t, kpkg.clone(), ppkg.clone(), HashMap::new())?;
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