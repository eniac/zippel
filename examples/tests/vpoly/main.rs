use ark_poly::DenseMultilinearExtension;
use backend::VirtualPolynomial;
use backend::poly_variant::PolyVariant;
use backend::{ATyp, ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

const NUM_VARS: usize = 2;

fn main() {
    println!("=== VPoly Product Check (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/tests/vpoly/vpoly.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &2);
    handler.compile(&sizes);

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

    // Static analysis (completeness & ZK)
    println!("\n--- Static Analysis ---");
    let analysis_start = Instant::now();
    let analysis_result = std::panic::catch_unwind(|| {
        let analysis_args = ZippelArgs::new(PathBuf::from("examples/tests/vpoly/vpoly.zippel"));
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
    let eval_count = 1usize << NUM_VARS; // 2^2 = 4 evaluations

    // Random 2-variable MLE: a(x1, x2)
    let a_evals: Vec<_> = (0..eval_count)
        .map(|_| Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar()).into_scalar())
        .collect();
    let a_mle = DenseMultilinearExtension::<<ArkBls12_381 as ArkConfig>::F>::from_evaluations_vec(
        NUM_VARS, a_evals,
    );
    let a = Value::Poly(VirtualPolynomial::from_poly(PolyVariant::DenseMle(a_mle)));

    // Random 2-variable MLE: b(x1, x2)
    let b_evals: Vec<_> = (0..eval_count)
        .map(|_| Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar()).into_scalar())
        .collect();
    let b_mle = DenseMultilinearExtension::<<ArkBls12_381 as ArkConfig>::F>::from_evaluations_vec(
        NUM_VARS, b_evals,
    );
    let b = Value::Poly(VirtualPolynomial::from_poly(PolyVariant::DenseMle(b_mle)));

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("a".to_string()), a),
        (Vid("b".to_string()), b),
    ])
}
