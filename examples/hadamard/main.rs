use zippel::*;
use std::{path::PathBuf, time::Instant};
use backend::{ArkConfig, ArkSecp256k1, Value, ATyp};
use ark_ff::{One, Zero};
use lang::id::{Tid, Vid};
use share::Ctx;

fn main() {
    println!("=== Hadamard (ArkSecp256k1) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/hadamard/hadamard.zippel"));
    let mut handler: zippel::ZippelHandler<ArkSecp256k1> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &5);
    handler.compile(&sizes);

    let inputs = prover_create_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let proof = handler.run_prover(prover_scheduled, inputs);
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkSecp256k1>(&proof);
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
        let analysis_args = ZippelArgs::new(PathBuf::from("examples/hadamard/hadamard.zippel"));
        let mut analysis_handler: ZippelHandler<ArkSecp256k1> = ZippelHandler::new(analysis_args);
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

#[allow(non_snake_case)]
fn prover_create_inputs() -> Ctx<Vid, Value<ArkSecp256k1>> {
    let mut rng = rand::rngs::OsRng;

    // Choose some N in the allowed range 1..5 in the DSL.
    let n_val_const = 4;

    // Random univariate polynomials p_A, p_B, p_C of degree < N.
    let mut p_a_coeffs = Vec::with_capacity(n_val_const);
    let mut p_b_coeffs = Vec::with_capacity(n_val_const);
    let mut p_c_coeffs = Vec::with_capacity(n_val_const);
    for _ in 0..n_val_const {
        let a_i: Value<ArkSecp256k1> =
            Value::<ArkSecp256k1>::random(&mut rng, &ATyp::scalar());
        let b_i: Value<ArkSecp256k1> =
            Value::<ArkSecp256k1>::random(&mut rng, &ATyp::scalar());
        let c_i: Value<ArkSecp256k1> =
            Value::<ArkSecp256k1>::random(&mut rng, &ATyp::scalar());
        p_a_coeffs.push(a_i.into_scalar());
        p_b_coeffs.push(b_i.into_scalar());
        p_c_coeffs.push(c_i.into_scalar());
    }
    let p_A = Value::<ArkSecp256k1>::VecScalar(p_a_coeffs).value_poly();
    let p_B = Value::<ArkSecp256k1>::VecScalar(p_b_coeffs).value_poly();
    let p_C = Value::<ArkSecp256k1>::VecScalar(p_c_coeffs).value_poly();

    // Take v_H to be the constant polynomial 1 of length N:
    // v_H(X) = 1, so any polynomial is divisible by v_H and
    // (p_A * p_B - p_C) % v_H = 0 holds automatically.
    let zero = <ArkSecp256k1 as ArkConfig>::F::zero();
    let one = <ArkSecp256k1 as ArkConfig>::F::one();
    let mut v_h_coeffs = Vec::with_capacity(n_val_const);
    v_h_coeffs.push(one);
    v_h_coeffs.extend(std::iter::repeat(zero).take(n_val_const));
    let v_H = Value::<ArkSecp256k1>::VecScalar(v_h_coeffs).value_poly();

    Ctx::<Vid, Value<ArkSecp256k1>>::from_iter([
        (Vid("p_A".to_string()), p_A),
        (Vid("p_B".to_string()), p_B),
        (Vid("p_C".to_string()), p_C),
        (Vid("v_H".to_string()), v_H),
    ])
}

