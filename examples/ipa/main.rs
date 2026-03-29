use zippel::*;
use std::{path::PathBuf, time::Instant};
use backend::{ArkSecp256k1, Value, ATyp};
use lang::id::{Tid, Vid};
use share::Ctx;

fn main() {
    println!("=== IPA (ArkSecp256k1) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/ipa/ipa.zippel"));
    let mut handler: zippel::ZippelHandler<ArkSecp256k1> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &6usize);
    handler.compile(&sizes);

    let inputs = prover_create_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let proof = handler.run_prover(prover_scheduled, inputs);
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkSecp256k1>(&proof);
    println!("Prover time:    {prover_elapsed:.2?}");
    println!("Proof size:     {proof_bytes} bytes ({} elements)", proof.len());

    let verifier_scheduled = handler.default_schedule_verifier();
    let verifier_start = Instant::now();
    let verifier_result = handler.run_verifier(verifier_scheduled, proof);
    let verifier_elapsed = verifier_start.elapsed();
    let result = check_verification(verifier_result);
    println!("Verifier time:  {verifier_elapsed:.2?}");
    if result.passed {
        println!("Verification:   ✓ PASSED");
    } else {
        println!("Verification:   ✗ FAILED");
        std::process::exit(1);
    }
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkSecp256k1>> {
    let mut rng = rand::rngs::OsRng;
    let n_val_const = 64;

    let u_aux_base: Value<ArkSecp256k1> = Value::<ArkSecp256k1>::random(&mut rng, &ATyp::g1());

    let g_vec: Value<ArkSecp256k1> = Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n_val_const));
    let h_vec: Value<ArkSecp256k1> = Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n_val_const));

    let a_vec_witness: Value<ArkSecp256k1> = Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let b_vec_witness: Value<ArkSecp256k1> = Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let ip_val_claimed: Value<ArkSecp256k1> = a_vec_witness.clone().dot(b_vec_witness.clone());
    let p_initial_commitment: Value<ArkSecp256k1> =
        g_vec.clone().dot(a_vec_witness.clone())
        + h_vec.clone().dot(b_vec_witness.clone());
    let sum_vec: Value<ArkSecp256k1> = 
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec_scalar(n_val_const));

    let inputs = Ctx::<Vid, Value<ArkSecp256k1>>::from_iter([
        (Vid("g_vec".to_string()), g_vec),
        (Vid("h_vec".to_string()), h_vec),
        (Vid("P_initial_commitment".to_string()), p_initial_commitment),
        (Vid("ip_val_claimed".to_string()), ip_val_claimed),
        (Vid("u_aux_base".to_string()), u_aux_base),
        (Vid("a_vec_witness".to_string()), a_vec_witness),
        (Vid("b_vec_witness".to_string()), b_vec_witness),
        (Vid("sum_vec".to_string()), sum_vec),
    ]);

    return inputs;
}