use ark_ff::{Field, One, Zero};
use ark_poly::DenseMultilinearExtension;
use ark_std::UniformRand;
use backend::poly_variant::PolyVariant;
use backend::VirtualPolynomial;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

const NX: usize = 2;
const NY: usize = 1;
const NUM_VARS: usize = NX + NY;

fn main() {
    println!("=== KZH (ArkBls12_381, NX={}, NY={}) ===", NX, NY);
    let args = ZippelArgs::new(PathBuf::from("examples/kzh/kzh.zippel"));
    let compile_result = std::panic::catch_unwind(|| {
        let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("NX"), &NX);
        sizes.insert(&Tid::new("NY"), &NY);
        handler.compile(&sizes);
        handler
    });

    let mut handler = match compile_result {
        Ok(h) => h,
        Err(e) => {
            println!("Compilation:    ✗ KZH protocol has syntax not yet supported by the compiler");
            if let Some(msg) = e.downcast_ref::<String>() {
                println!("  Error: {}", msg);
            }
            std::process::exit(0);
        }
    };

    let inputs = prover_create_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let proof = handler.run_prover(prover_scheduled, inputs);
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkBls12_381>(&proof);
    println!("Prover time:    {prover_elapsed:.2?}");
    println!(
        "Proof size:     {proof_bytes} bytes ({} elements)",
        proof.len()
    );

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

    println!("\n--- Static Analysis ---");
    let analysis_result = std::panic::catch_unwind(|| {
        let analysis_args = ZippelArgs::new(PathBuf::from("examples/kzh/kzh.zippel"));
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
    let mut rng = rand::rngs::OsRng;
    let one = <ArkBls12_381 as ArkConfig>::F::one();
    let zero = <ArkBls12_381 as ArkConfig>::F::zero();

    let tau = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let g1 = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let g2 = <ArkBls12_381 as ArkConfig>::G2::rand(&mut rng);

    let h_xy_size = 1usize << (NX + NY);
    let h_y_size = 1usize << NY;
    let d_x_size = 1usize << NX;

    let h_xy_vals: Vec<_> = (0..h_xy_size).map(|k| g1 * tau.pow([k as u64])).collect();
    let h_y_vals: Vec<_> = (0..h_y_size).map(|j| g1 * tau.pow([j as u64])).collect();

    let v_prime = g2 * tau.pow([(d_x_size as u64)]);
    let v_x_vals: Vec<_> = (0..d_x_size).map(|i| g2 * tau.pow([i as u64])).collect();

    let f_evals: Vec<<ArkBls12_381 as ArkConfig>::F> = (0..h_xy_size)
        .map(|_| <ArkBls12_381 as ArkConfig>::F::rand(&mut rng))
        .collect();

    let d_x_vals: Vec<_> = (0..d_x_size)
        .map(|i| {
            let mut d_x_i = <ArkBls12_381 as ArkConfig>::G1::zero();
            for j in 0..h_y_size {
                let f_ij = f_evals[i * h_y_size + j];
                d_x_i = d_x_i + h_y_vals[j] * f_ij;
            }
            d_x_i
        })
        .collect();

    let x0_vals: Vec<<ArkBls12_381 as ArkConfig>::F> = (0..NX)
        .map(|_| <ArkBls12_381 as ArkConfig>::F::rand(&mut rng))
        .collect();
    let y0_vals: Vec<<ArkBls12_381 as ArkConfig>::F> = (0..NY)
        .map(|_| <ArkBls12_381 as ArkConfig>::F::rand(&mut rng))
        .collect();

    let z0 = (0..h_xy_size).fold(zero, |acc, k| {
        let mut weight = one;
        for i in 0..NX {
            let bit = (k >> (NUM_VARS - 1 - i)) & 1;
            if bit == 1 {
                weight = weight * x0_vals[i];
            } else {
                weight = weight * (one - x0_vals[i]);
            }
        }
        for j in 0..NY {
            let bit = (k >> (NUM_VARS - 1 - NX - j)) & 1;
            if bit == 1 {
                weight = weight * y0_vals[j];
            } else {
                weight = weight * (one - y0_vals[j]);
            }
        }
        acc + f_evals[k] * weight
    });

    let mle = DenseMultilinearExtension::from_evaluations_vec(NUM_VARS, f_evals.clone());
    let f_xy_poly = Value::Poly(VirtualPolynomial::from_poly(PolyVariant::DenseMle(mle)));

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("f_xy".to_string()), f_xy_poly),
        (Vid("x0".to_string()), Value::VecScalar(x0_vals)),
        (Vid("y0".to_string()), Value::VecScalar(y0_vals)),
        (Vid("z0".to_string()), Value::Scalar(z0)),
        (Vid("H_xy".to_string()), Value::VecG1(h_xy_vals)),
        (Vid("H_y".to_string()), Value::VecG1(h_y_vals)),
        (Vid("D_x".to_string()), Value::VecG1(d_x_vals)),
        (Vid("V_prime".to_string()), Value::G2(v_prime)),
        (Vid("V_x".to_string()), Value::VecG2(v_x_vals)),
    ])
}
