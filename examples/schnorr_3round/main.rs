use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, ArkGroupOps, Value};
use lang::id::Vid;
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

fn main() {
    println!("=== Schnorr 3-Round (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from(
        "examples/schnorr_3round/schnorr_3round.zippel",
    ));
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
        println!("Verification:   PASSED");
    } else {
        println!("Verification:   FAILED");
        std::process::exit(1);
    }

    // Static analysis: completeness, ZK, and (2,2,2)-special soundness
    println!("\n--- Static Analysis ---");
    let analysis_args = ZippelArgs::new(PathBuf::from(
        "examples/schnorr_3round/schnorr_3round.zippel",
    ));
    let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
    let analysis_start = Instant::now();
    let analysis = analysis_handler.minimal_analysis();
    let analysis_elapsed = analysis_start.elapsed();
    match &analysis.completeness {
        Ok(()) => println!("Completeness:   OK"),
        Err(e) => println!("Completeness:   FAIL {}", e),
    }
    match &analysis.zk {
        Ok(()) => println!("ZK:             OK"),
        Err(e) => println!("ZK:             FAIL {}", e),
    }

    // (2,2,2)-special soundness: 3 rounds, each with 2 challenge transcripts
    let soundness_start = Instant::now();
    let soundness_result = analysis_handler.analyze_special_soundness(vec![2, 2, 2]);
    let soundness_elapsed = soundness_start.elapsed();
    match &soundness_result {
        Ok(()) => println!("Soundness:      OK (2,2,2)-special sound"),
        Err(e) => println!("Soundness:      FAIL {}", e),
    }
    println!("Analysis time:  {analysis_elapsed:.2?} + {soundness_elapsed:.2?} soundness");
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let x = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let g = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let h_affines = <ArkBls12_381 as ArkConfig>::G1Ops::vec_mul(&g, &[x]);
    let h = h_affines.into_iter().next().unwrap();
    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("x".to_string()), Value::Scalar(x)),
        (Vid("g".to_string()), Value::G1(g)),
        (Vid("h".to_string()), Value::G1Affine(h)),
    ])
}
