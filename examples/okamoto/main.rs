use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

fn main() {
    println!("=== Okamoto (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/okamoto/okamoto.zippel"));
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile(&Ctx::new());

    let inputs = prover_create_inputs();
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

    let verifier_scheduled = handler.default_schedule_verifier();
    let verifier_start = Instant::now();
    let verifier_result = handler
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

    // Static analysis (completeness, ZK, & soundness)
    println!("\n--- Static Analysis ---");
    let analysis_args = ZippelArgs::new(PathBuf::from("examples/okamoto/okamoto.zippel"));
    let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
    analysis_handler.compile(&Ctx::new());

    let analysis = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        analysis_handler.minimal_analysis()
    }));
    match analysis {
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

    let soundness_start = Instant::now();
    let soundness_result = analysis_handler.analyze_special_soundness(vec![2]);
    let soundness_elapsed = soundness_start.elapsed();
    match &soundness_result {
        Ok(()) => println!("Soundness:      ✓ (2)-special sound"),
        Err(e) => println!("Soundness:      ✗ {}", e),
    }
    println!("Soundness time: {soundness_elapsed:.2?}");
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    type F = <ArkBls12_381 as ArkConfig>::F;
    type G1 = <ArkBls12_381 as ArkConfig>::G1;

    let x = F::rand(&mut rng);
    let r = F::rand(&mut rng);
    let g = G1::rand(&mut rng);
    let h = G1::rand(&mut rng);

    let comm = g * x + h * r;

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("x".to_string()), Value::Scalar(x)),
        (Vid("r".to_string()), Value::Scalar(r)),
        (Vid("g".to_string()), Value::G1(g)),
        (Vid("h".to_string()), Value::G1(h)),
        (Vid("comm".to_string()), Value::G1(comm)),
    ])
}
