use ark_ff::Zero;
use ark_poly::DenseMultilinearExtension;
use ark_std::UniformRand;
use backend::VirtualPolynomial;
use backend::poly_variant::PolyVariant;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::{path::PathBuf, thread, time::Instant};
use zippel::*;

const NUM_VARS: usize = 10;
const MLE_SUMCHECK_EXAMPLE_STACK_SIZE: usize = 256 * 1024 * 1024;

fn main() {
    let worker = thread::Builder::new()
        .name("zippel-mle-sumcheck-example".to_string())
        .stack_size(MLE_SUMCHECK_EXAMPLE_STACK_SIZE)
        .spawn(run_mle_sumcheck)
        .expect("failed to spawn mle_sumcheck example worker thread");
    if let Err(payload) = worker.join() {
        std::panic::resume_unwind(payload);
    }
}

fn run_mle_sumcheck() {
    let zippel_file =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/mle_sumcheck/mle_sumcheck.zippel");
    let num_vars = NUM_VARS;

    println!("=== Multilinear Sumcheck (ArkBls12_381) ===");
    println!("num_vars:       {num_vars}");
    let args = ZippelArgs::new(zippel_file.clone());
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("NUM_VARS"), &num_vars);
    sizes.insert(&Tid::new("MAX_DEGREE_CONST"), &1usize);
    handler.compile(&sizes);

    let inputs = prover_create_inputs(num_vars);
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
    let result = check_verification(verifier_result.clone());
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
        let analysis_args = ZippelArgs::new(zippel_file.clone());
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

fn prover_create_inputs(num_vars: usize) -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as ArkConfig>::F;
    let eval_count = 1usize << num_vars;
    let mut rng = rand::rngs::OsRng;
    let base_evals: Vec<F> = (0..eval_count).map(|_| F::rand(&mut rng)).collect();

    // The polynomial is simply the multilinear extension.
    let claimed_sum: F = base_evals.iter().fold(F::zero(), |acc, val| acc + val);

    let base = VirtualPolynomial::from_poly(PolyVariant::DenseMle(
        DenseMultilinearExtension::from_evaluations_vec(num_vars, base_evals),
    ));
    let poly = Value::Poly(base);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("claimed_sum".to_string()), Value::Scalar(claimed_sum)),
        (Vid("poly".to_string()), poly),
    ])
}
