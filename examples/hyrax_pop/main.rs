use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

fn main() {
    println!("=== Hyrax PoP (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/hyrax_pop/hyrax_pop.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
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

    // Static analysis (completeness & ZK)
    println!("\n--- Static Analysis ---");
    let analysis_result = std::panic::catch_unwind(|| {
        let analysis_args = ZippelArgs::new(PathBuf::from("examples/hyrax_pop/hyrax_pop.zippel"));
        let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
        analysis_handler.minimal_analysis()
    });
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
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;

    let x = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let y = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let r_x = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let r_y = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let r_z = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);

    let g = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let h = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);

    let big_x = g * x + h * r_x;
    let big_y = g * y + h * r_y;
    let big_z = g * (x * y) + h * r_z;

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("x".to_string()), Value::Scalar(x)),
        (Vid("y".to_string()), Value::Scalar(y)),
        (Vid("r_X".to_string()), Value::Scalar(r_x)),
        (Vid("r_Y".to_string()), Value::Scalar(r_y)),
        (Vid("r_Z".to_string()), Value::Scalar(r_z)),
        (Vid("g".to_string()), Value::G1(g)),
        (Vid("h".to_string()), Value::G1(h)),
        (Vid("big_x".to_string()), Value::G1(big_x)),
        (Vid("big_y".to_string()), Value::G1(big_y)),
        (Vid("big_z".to_string()), Value::G1(big_z)),
    ])
}
