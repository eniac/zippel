use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

fn main() {
    let worker = std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(run_example)
        .expect("failed to spawn worker thread");
    if let Err(payload) = worker.join() {
        std::panic::resume_unwind(payload);
    }
}

fn run_example() {
    println!("=== R1CS Sigma (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/r1cs_sigma/r1cs_sigma.zippel"));
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
    let analysis_args = ZippelArgs::new(PathBuf::from("examples/r1cs_sigma/r1cs_sigma.zippel"));
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
            println!("Completeness time:  {:.2?}", analysis.completeness_time);
            match &analysis.zk {
                Ok(()) => println!("ZK:             ✓"),
                Err(e) => println!("ZK:             ✗ {}", e),
            }
            println!("ZK time:            {:.2?}", analysis.zk_time);
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
    println!("Soundness time:     {:.2?}", soundness_elapsed);
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as ArkConfig>::F;
    type G1 = <ArkBls12_381 as ArkConfig>::G1;
    let mut rng = rand::rngs::OsRng;

    let x0 = F::rand(&mut rng);
    let w0 = x0 * x0; // w = x^2 so that A*z * B*z = C*z

    // Constraint: x * x = w, i.e. x^2 = w
    // A selects x: [1, 0]
    // B selects x: [1, 0]
    // C selects w: [0, 1]
    let mat_a = vec![F::from(1u64), F::from(0u64)];
    let mat_b = vec![F::from(1u64), F::from(0u64)];
    let mat_c = vec![F::from(0u64), F::from(1u64)];

    let ck = G1::rand(&mut rng);
    let h_base = G1::rand(&mut rng);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("ck".to_string()), Value::VecG1(vec![ck])),
        (Vid("h_base".to_string()), Value::G1(h_base)),
        (Vid("mat_A".to_string()), Value::VecScalar(mat_a)),
        (Vid("mat_B".to_string()), Value::VecScalar(mat_b)),
        (Vid("mat_C".to_string()), Value::VecScalar(mat_c)),
        (Vid("x".to_string()), Value::VecScalar(vec![x0])),
        (Vid("w".to_string()), Value::VecScalar(vec![w0])),
    ])
}
