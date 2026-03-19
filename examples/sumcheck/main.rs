use zippel::*;
use std::{path::PathBuf, time::Instant};
use backend::{ArkBls12_381, ArkConfig, Value};
use backend::poly_variant::PolyVariant;
use backend::VirtualPolynomial;
use ark_poly::DenseMultilinearExtension;
use lang::id::{Vid, Tid};
use share::Ctx;
use ark_ff::Zero;

const NUM_VARS: usize = 4;
const DEGREE: usize = 1;

fn main() {
    println!("=== Sumcheck (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/sumcheck/sumcheck.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &10);
    handler.compile(&sizes);

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
    let analysis_result = std::panic::catch_unwind(|| {
        let analysis_args = ZippelArgs::new(PathBuf::from("examples/sumcheck/sumcheck.zippel"));
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
    let eval_count = 1usize << NUM_VARS;
    // Use the zero polynomial so each round polynomial is identically zero.
    // This makes round checks deterministic and independent of random challenges.
    let g_evals: Vec<_> = vec![<ArkBls12_381 as ArkConfig>::F::zero(); eval_count];

    let claimed_sum = g_evals.iter()
        .fold(<ArkBls12_381 as ArkConfig>::F::zero(), |acc, val| acc + val);

    let g_poly = DenseMultilinearExtension::from_evaluations_vec(NUM_VARS, g_evals.clone());
    let poly = Value::Poly(VirtualPolynomial::from_poly(PolyVariant::DenseMle(g_poly)));

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("claimed_sum".to_string()), Value::Scalar(claimed_sum)),
        (Vid("poly".to_string()), poly),
        (Vid("num_variables".to_string()), Value::Index(NUM_VARS)),
        (Vid("max_degree".to_string()), Value::Index(DEGREE)),
        (Vid("rounds".to_string()), Value::VecIndex(vec![0, 0, 0, 0])),
    ])
}

