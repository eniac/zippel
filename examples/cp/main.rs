use zippel::*;
use std::{path::PathBuf, time::Instant};
use backend::{ArkBls12_381, Value, ATyp};
use lang::id::Vid;
use share::Ctx;

fn main() {
    println!("=== Chaum-Pedersen (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/cp.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile();

    let inputs = prover_create_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let proof = handler.run_prover(prover_scheduled, inputs);
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkBls12_381>(&proof);
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

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;

    let beta: Value<ArkBls12_381> = Value::random(&mut rng, &ATyp::scalar());
    let g: Value<ArkBls12_381> = Value::random(&mut rng, &ATyp::g1());
    let u: Value<ArkBls12_381> = Value::random(&mut rng, &ATyp::g1());

    let v = g.clone() * beta.clone();
    let w = u.clone() * beta.clone();

    let inputs = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("beta".to_string()), beta),
        (Vid("g".to_string()), g),
        (Vid("u".to_string()), u),
        (Vid("v".to_string()), v),
        (Vid("w".to_string()), w),
    ]);

    inputs
}