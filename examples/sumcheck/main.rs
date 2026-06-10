use ark_ff::Zero;
use ark_poly::DenseMultilinearExtension;
use ark_std::UniformRand;
use backend::VirtualPolynomial;
use backend::poly_variant::PolyVariant;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::{env, path::PathBuf, thread, time::Instant};
use zippel::*;

const NUM_VARS: usize = 10;
const MAX_DEGREE: usize = 10;
const DROP_EVAL_POINT_TEST: bool = false;
const DEFAULT_SUMCHECK_EXAMPLE_STACK_SIZE: usize = 64 * 1024 * 1024;
const SUMCHECK_EXAMPLE_STACK_ENV: &str = "ZIPPEL_SUMCHECK_EXAMPLE_STACK_SIZE";

fn main() {
    let stack_size = configured_stack_size();
    let worker = thread::Builder::new()
        .name("zippel-sumcheck-example".to_string())
        .stack_size(stack_size)
        .spawn(run_sumcheck_example)
        .expect("failed to spawn sumcheck example worker thread");

    if let Err(payload) = worker.join() {
        std::panic::resume_unwind(payload);
    }
}

fn configured_stack_size() -> usize {
    match env::var(SUMCHECK_EXAMPLE_STACK_ENV) {
        Ok(raw) => raw.parse::<usize>().unwrap_or_else(|_| {
            eprintln!("{SUMCHECK_EXAMPLE_STACK_ENV} must be a decimal byte count; got {raw:?}.");
            std::process::exit(2);
        }),
        Err(env::VarError::NotPresent) => DEFAULT_SUMCHECK_EXAMPLE_STACK_SIZE,
        Err(err) => {
            eprintln!("Could not read {SUMCHECK_EXAMPLE_STACK_ENV}: {err}");
            std::process::exit(2);
        }
    }
}

fn run_sumcheck_example() {
    let zippel_file =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/sumcheck/sumcheck.zippel");
    let num_vars = NUM_VARS;
    let max_degree = MAX_DEGREE;
    if max_degree == 0 {
        eprintln!("SUMCHECK_MAX_DEGREE must be >= 1.");
        std::process::exit(2);
    }

    println!("=== Sumcheck (ArkBls12_381) ===");
    println!("num_vars:       {num_vars}");
    println!("max_degree:     {max_degree}");
    let args = ZippelArgs::new(zippel_file.clone());
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    // Bind both Size parameters so the recursive helper's `V: 2..NUM_VARS_CONST`
    // range and the polynomial array length both follow `num_vars`. The previous
    // `sizes.insert("S", 10)` was a no-op — there's no `S` in the protocol —
    // which left the protocol pinned to its defaults regardless of `num_vars`.
    sizes.insert(&Tid::new("NUM_VARS_CONST"), &num_vars);
    sizes.insert(&Tid::new("MAX_DEGREE_CONST"), &max_degree);
    handler.compile(&sizes);

    let inputs = prover_create_inputs(num_vars, max_degree);
    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let mut proof = handler
        .run_prover(prover_scheduled, inputs)
        .expect("run_prover failed");
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkBls12_381>(&proof);
    println!("Prover time:    {prover_elapsed:.2?}");
    println!(
        "Proof size:     {proof_bytes} bytes ({} elements)",
        proof.len()
    );
    if DROP_EVAL_POINT_TEST {
        let removed = drop_one_eval_point_from_proof(&mut proof);
        println!(
            "Tamper test:    remove one evaluation point -> {}",
            if removed { "applied" } else { "not found" }
        );
    }

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

fn drop_one_eval_point_from_proof(proof: &mut [Value<ArkBls12_381>]) -> bool {
    for value in proof.iter_mut() {
        if drop_one_eval_point_in_value(value) {
            return true;
        }
    }
    false
}

fn drop_one_eval_point_in_value(value: &mut Value<ArkBls12_381>) -> bool {
    match value {
        Value::VecScalar(v) => {
            if !v.is_empty() {
                v.pop();
                return true;
            }
            false
        }
        Value::Record(fields) => {
            let keys: Vec<String> = fields.iter().map(|(k, _)| k.clone()).collect();
            for key in keys {
                if let Some(inner) = fields.get_mut(&key)
                    && drop_one_eval_point_in_value(inner)
                {
                    return true;
                }
            }
            false
        }
        _ => false,
    }
}

fn prover_create_inputs(num_vars: usize, max_degree: usize) -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as ArkConfig>::F;
    let eval_count = 1usize << num_vars;
    let mut rng = rand::rngs::OsRng;
    let base_evals: Vec<F> = (0..eval_count).map(|_| F::rand(&mut rng)).collect();

    // Build a degree-k virtual polynomial as base(x)^k over the boolean hypercube.
    let claimed_sum: F = base_evals
        .iter()
        .map(|x| (0..max_degree).fold(F::from(1u64), |acc, _| acc * *x))
        .fold(F::zero(), |acc, val| acc + val);

    let base = VirtualPolynomial::from_poly(PolyVariant::DenseMle(
        DenseMultilinearExtension::from_evaluations_vec(num_vars, base_evals),
    ));
    let mut full_poly = base.clone();
    for _ in 1..max_degree {
        full_poly = full_poly
            .poly_mul(&base)
            .expect("failed to multiply full_poly by base");
    }
    let poly = Value::Poly(full_poly);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("claimed_sum".to_string()), Value::Scalar(claimed_sum)),
        (Vid("poly".to_string()), poly),
    ])
}
