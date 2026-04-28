use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

fn main() {
    println!("=== Reuse Randomness (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from(
        "examples/schnorr_and_two_verify/schnorr_and_two_verify.zippel",
    ));
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile(&Ctx::new());

    let inputs = prover_create_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let proof = handler.run_prover(prover_scheduled, inputs);
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkBls12_381>(&proof);
    println!("Prover time:    {prover_elapsed:.2?}");
    println!(
        "Proof size:     {proof_bytes} bytes ({} elements)",
        proof.len()
    );

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

    println!("\n--- Static Analysis ---");
    let analysis_start = Instant::now();
    let analysis_result = std::panic::catch_unwind(|| {
        let analysis_args = ZippelArgs::new(PathBuf::from(
            "examples/schnorr_and_two_verify/schnorr_and_two_verify.zippel",
        ));
        let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
        analysis_handler.minimal_analysis()
    });
    let analysis_elapsed = analysis_start.elapsed();
    match analysis_result {
        Ok(analysis) => {
            match &analysis.completeness {
                Ok(()) => println!("Completeness:   ✓"),
                Err(e) => println!("Completeness:   ✗ {}", e),
            }
            match &analysis.zk {
                Ok(()) => println!("ZK:             ✓"),
                Err(e) => println!("ZK:             ✗ {}", e),
            }
        }
        Err(_) => println!("Analysis:       ⚠ not supported (non-polynomial operations)"),
    }
    println!("Analysis time:  {analysis_elapsed:.2?}");
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let x = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let y = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let g = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);

    let h1 = g * x;
    let h2 = g * y;

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("x".to_string()), Value::Scalar(x)),
        (Vid("y".to_string()), Value::Scalar(y)),
        (Vid("g".to_string()), Value::G1(g)),
        (Vid("h1".to_string()), Value::G1(h1)),
        (Vid("h2".to_string()), Value::G1(h2)),
    ])
}
