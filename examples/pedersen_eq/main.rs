use ark_std::UniformRand;
use backend::{ArkConfig, ArkSecp256k1, Value};
use lang::id::Vid;
use share::Ctx;
use std::ops::Mul;
use std::{path::PathBuf, time::Instant};
use zippel::*;

fn main() {
    println!("=== Pedersen Equality (ArkSecp256k1) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/pedersen_eq/pedersen_eq.zippel"));
    let mut handler: zippel::ZippelHandler<ArkSecp256k1> = ZippelHandler::new(args);
    handler.compile(&Ctx::new());

    let inputs = prover_create_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let proof = handler
        .run_prover(prover_scheduled, inputs)
        .expect("run_prover failed");
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkSecp256k1>(&proof);
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

    // Static analysis (completeness & ZK)
    println!("\n--- Static Analysis ---");
    let analysis_args = ZippelArgs::new(PathBuf::from("examples/pedersen_eq/pedersen_eq.zippel"));
    let mut analysis_handler: ZippelHandler<ArkSecp256k1> = ZippelHandler::new(analysis_args);
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

fn prover_create_inputs() -> Ctx<Vid, Value<ArkSecp256k1>> {
    let mut rng = rand::rngs::OsRng;

    let m1 = <ArkSecp256k1 as ArkConfig>::F::rand(&mut rng);
    let r1 = <ArkSecp256k1 as ArkConfig>::F::rand(&mut rng);

    let m2 = m1;
    let r2 = <ArkSecp256k1 as ArkConfig>::F::rand(&mut rng);

    let g = <ArkSecp256k1 as ArkConfig>::G1::rand(&mut rng);
    let h = <ArkSecp256k1 as ArkConfig>::G1::rand(&mut rng);

    let c1 = g.mul(m1) + h.mul(r1);
    let c2 = g.mul(m2) + h.mul(r2);

    Ctx::<Vid, Value<ArkSecp256k1>>::from_iter([
        (Vid("m1".to_string()), Value::Scalar(m1)),
        (Vid("r1".to_string()), Value::Scalar(r1)),
        (Vid("m2".to_string()), Value::Scalar(m2)),
        (Vid("r2".to_string()), Value::Scalar(r2)),
        (Vid("g".to_string()), Value::G1(g)),
        (Vid("h".to_string()), Value::G1(h)),
        (Vid("c1".to_string()), Value::G1(c1)),
        (Vid("c2".to_string()), Value::G1(c2)),
    ])
}
