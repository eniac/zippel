use ark_ff::fields::Field;
use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

fn main() {
    println!("=== Membership ===");
    let args = ZippelArgs::new(PathBuf::from("examples/membership/membership.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("N"), &2);
    sizes.insert(&Tid::new("M"), &2);
    handler.compile(&sizes);

    let inputs = prover_create_inputs();
    let public_inputs = inputs
        .clone()
        .into_iter()
        .filter(|(vid, _)| vid.0 != "f_coeffs")
        .collect::<Ctx<Vid, Value<ArkBls12_381>>>();

    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let proof = handler
        .run_prover(prover_scheduled, inputs)
        .expect("run_prover failed");
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkBls12_381>(&proof);
    println!("Prover time:    {prover_elapsed:.2?}");
    println!(
        "Proof size:     {proof_bytes} bytes ({} elements)",
        proof.len()
    );

    let args = ZippelArgs::new(PathBuf::from("examples/membership/membership.zippel"));
    let mut verifier_handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    verifier_handler.compile(&sizes);
    verifier_handler.set_public_inputs(public_inputs);
    let verifier_scheduled = verifier_handler.default_schedule_verifier();
    let verifier_start = Instant::now();
    let verifier_result = verifier_handler
        .run_verifier(verifier_scheduled, proof)
        .expect("run_verifier failed");
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

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let m_size = 2; // For S = {0, 1}

    let g_input = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let g: Value<ArkBls12_381> = Value::G1(g_input);

    let h_input = <ArkBls12_381 as ArkConfig>::G2::rand(&mut rng);
    let h: Value<ArkBls12_381> = Value::G2(h_input);

    let tau_input = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);

    // SRS G1 up to size M (which is 2)
    let ss_g: Value<ArkBls12_381> = Value::VecG1((0..m_size).map(|_| g_input).collect());
    let ss_index = Value::VecScalar((0..m_size).map(|i| tau_input.pow([i as u64])).collect());
    let ss = ss_g.clone() * ss_index.clone();

    // SRS G2_s
    let h_val: Value<ArkBls12_381> = Value::G2(h_input * tau_input);

    // Set S = {0, 1}
    let zero = <ArkBls12_381 as ArkConfig>::F::from(0u64);
    let one = <ArkBls12_381 as ArkConfig>::F::from(1u64);
    let s_val = Value::VecScalar(vec![zero, one]);

    // f_coeffs. f(0) = z = 0. f(X) = c*X. So f_coeffs = [0, c]
    let c = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let f_coeffs = Value::VecScalar(vec![zero, c]);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("f_coeffs".to_string()), f_coeffs),
        (Vid("s".to_string()), s_val),
        (Vid("gen_g1".to_string()), g),
        (Vid("gen_g2".to_string()), h),
        (Vid("srs_g1".to_string()), ss),
        (Vid("srs_g2_s".to_string()), h_val),
    ])
}
