use zippel::*;
use std::{path::PathBuf, time::Instant};
use backend::{ArkBls12_381, ArkConfig, Value};
use backend::poly_variant::PolyVariant;
use backend::VirtualPolynomial;
use ark_poly::DenseMultilinearExtension;
use lang::id::{Vid, Tid};
use share::Ctx;
use ark_ff::Zero;
use ark_std::UniformRand;

const NUM_VARS: usize = 12;
const DROP_EVAL_POINT_TEST: bool = false;
fn main() {
    println!("=== Sumcheck (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/sumcheck/sumcheck.zippel"))
        .with_pdf(PathBuf::from("target/sumcheck_graphs.pdf"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &10);
    handler.compile(&sizes);

    let inputs = prover_create_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let mut proof = handler.run_prover(prover_scheduled, inputs);
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkBls12_381>(&proof);
    println!("Prover time:    {prover_elapsed:.2?}");
    println!("Proof size:     {proof_bytes} bytes ({} elements)", proof.len());
    if DROP_EVAL_POINT_TEST {
        let removed = drop_one_eval_point_from_proof(&mut proof);
        println!(
            "Tamper test:    remove one evaluation point -> {}",
            if removed { "applied" } else { "not found" }
        );
    }

    let verifier_scheduled = handler.default_schedule_verifier();
    let verifier_start = Instant::now();
    let verifier_result = handler.run_verifier(verifier_scheduled, proof);
    let verifier_elapsed = verifier_start.elapsed();
    let result = check_verification(verifier_result.clone());
    println!("Verifier time:  {verifier_elapsed:.2?}");
    if result.passed {
        println!("Verification:   ✓ PASSED");
    } else {
        println!("Verification:   ✗ FAILED");
        std::process::exit(1);
    }

    // // Static analysis (completeness & ZK)
    // println!("\n--- Static Analysis ---");
    // let analysis_result = std::panic::catch_unwind(|| {
    //     let analysis_args = ZippelArgs::new(PathBuf::from("examples/sumcheck/sumcheck.zippel"));
    //     let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
    //     analysis_handler.minimal_analysis()
    // });
    // match analysis_result {
    //     Ok(analysis) => {
    //         match &analysis.completeness {
    //             Ok(()) => println!("Completeness:   ✓"),
    //             Err(e) => println!("Completeness:   ✗ {}", e),
    //         }
    //         match &analysis.zk {
    //             Ok(()) => println!("ZK:             ✓"),
    //             Err(e) => println!("ZK:             ✗ {}", e),
    //         }
    //     }
    //     Err(_) => println!("Analysis:       ⚠ not supported (non-polynomial operations)"),
    // }
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
                if let Some(inner) = fields.get_mut(&key) {
                    if drop_one_eval_point_in_value(inner) {
                        return true;
                    }
                }
            }
            false
        }
        _ => false,
    }
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as ArkConfig>::F;
    let eval_count = 1usize << NUM_VARS;
    let mut rng = rand::rngs::OsRng;
    // Build a degree-3 virtual polynomial as a product of 3 MLEs.
    let f1_evals: Vec<F> = (0..eval_count).map(|_| F::rand(&mut rng)).collect();
    let f2_evals: Vec<F> = (0..eval_count).map(|_| F::rand(&mut rng)).collect();
    let f3_evals: Vec<F> = (0..eval_count).map(|_| F::rand(&mut rng)).collect();

    // Over the Boolean hypercube, each MLE evaluates to its table entry.
    // So the product polynomial's evaluations are pointwise products.
    let prod_evals: Vec<F> = f1_evals
        .iter()
        .zip(f2_evals.iter())
        .zip(f3_evals.iter())
        .map(|((a, b), c)| *a * *b * *c)
        .collect();
    let claimed_sum: F = prod_evals.iter().fold(F::zero(), |acc, val| acc + val);

    let f1 = VirtualPolynomial::from_poly(PolyVariant::DenseMle(
        DenseMultilinearExtension::from_evaluations_vec(NUM_VARS, f1_evals),
    ));
    let f2 = VirtualPolynomial::from_poly(PolyVariant::DenseMle(
        DenseMultilinearExtension::from_evaluations_vec(NUM_VARS, f2_evals),
    ));
    let f3 = VirtualPolynomial::from_poly(PolyVariant::DenseMle(
        DenseMultilinearExtension::from_evaluations_vec(NUM_VARS, f3_evals),
    ));
    let poly = Value::Poly(
        f1.poly_mul(&f2)
            .expect("failed to multiply f1*f2")
            .poly_mul(&f3)
            .expect("failed to multiply (f1*f2)*f3"),
    );

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("claimed_sum".to_string()), Value::Scalar(claimed_sum)),
        (Vid("poly".to_string()), poly),
    ])
}

