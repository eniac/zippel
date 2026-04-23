use zippel::*;
use std::{path::PathBuf, time::Instant};
use backend::{ArkBls12_381, Value, ATyp};
use lang::id::Vid;
use share::Ctx;

fn main() {
    println!("=== MLE (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/mle_example/mle_example.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile(&Ctx::new());

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

    // Static analysis (completeness & ZK)
    println!("\n--- Static Analysis ---");
    let analysis_args = ZippelArgs::new(PathBuf::from("examples/mle_example/mle_example.zippel"));
    let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
    let analysis_start = Instant::now();
    let analysis = analysis_handler.minimal_analysis();
    let analysis_elapsed = analysis_start.elapsed();
    match &analysis.completeness {
        Ok(()) => println!("Completeness:   ✓"),
        Err(e) => println!("Completeness:   ✗ {}", e),
    }
    match &analysis.zk {
        Ok(()) => println!("ZK:             ✓"),
        Err(e) => println!("ZK:             ✗ {}", e),
    }
    println!("Analysis time:  {analysis_elapsed:.2?}");
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let inputs = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("x".to_string()), Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar())),
    ]);

    return inputs;
}