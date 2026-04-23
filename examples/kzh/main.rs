use ark_ff::Zero;
use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

// NX and NY are hardcoded to 2 in the .zippel protocol (see the challenge block).
const NX: usize = 2;
const NY: usize = 2;

fn main() {
    println!("=== KZH (ArkBls12_381, NX={}, NY={}) ===", NX, NY);
    let args = ZippelArgs::new(PathBuf::from("examples/kzh/kzh.zippel"));
    let compile_result = std::panic::catch_unwind(|| {
        let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
        let sizes = Ctx::new();
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
    let analysis_start = Instant::now();
    let analysis_result = std::panic::catch_unwind(|| {
        let analysis_args = ZippelArgs::new(PathBuf::from("examples/kzh/kzh.zippel"));
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

    // KZH SRS (Figure 2): per-row trapdoors tau_i, per-column generators G_j,
    // blinder alpha. H_{i,j} = tau_i * G_j; H^j = alpha * G_j;
    // V^i = tau_i * V; V' = alpha * V.
    let g2_base = <ArkBls12_381 as ArkConfig>::G2::rand(&mut rng);
    let alpha = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);

    let h_xy_size = 1usize << (NX + NY);
    let h_y_size = 1usize << NY;
    let d_x_size = 1usize << NX;

    let g_cols: Vec<<ArkBls12_381 as ArkConfig>::G1> =
        (0..h_y_size).map(|_| <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng)).collect();
    let tau_rows: Vec<<ArkBls12_381 as ArkConfig>::F> =
        (0..d_x_size).map(|_| <ArkBls12_381 as ArkConfig>::F::rand(&mut rng)).collect();

    let h_xy_vals: Vec<_> = (0..h_xy_size)
        .map(|k| {
            let i = k >> NY;
            let j = k & (h_y_size - 1);
            g_cols[j] * tau_rows[i]
        })
        .collect();
    let h_y_vals: Vec<_> = (0..h_y_size).map(|j| g_cols[j] * alpha).collect();

    let v_prime = g2_base * alpha;
    let v_x_vals: Vec<_> = (0..d_x_size).map(|i| g2_base * tau_rows[i]).collect();

    // Prover's secret polynomial: random evaluations on the boolean hypercube.
    let f_evals: Vec<<ArkBls12_381 as ArkConfig>::F> = (0..h_xy_size)
        .map(|_| <ArkBls12_381 as ArkConfig>::F::rand(&mut rng))
        .collect();

    // Aux cache from commit phase: d_x[i] = sum_j f(i,j) * h_y[j].
    let d_x_vals: Vec<_> = (0..d_x_size)
        .map(|i| {
            let mut acc = <ArkBls12_381 as ArkConfig>::G1::zero();
            for j in 0..h_y_size {
                acc = acc + h_y_vals[j] * f_evals[i * h_y_size + j];
            }
            acc
        })
        .collect();

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("f_evals".to_string()), Value::VecScalar(f_evals)),
        (Vid("h_xy".to_string()),    Value::VecG1(h_xy_vals)),
        (Vid("h_y".to_string()),     Value::VecG1(h_y_vals)),
        (Vid("d_x".to_string()),     Value::VecG1(d_x_vals)),
        (Vid("v_prime".to_string()), Value::G2(v_prime)),
        (Vid("v_x".to_string()),     Value::VecG2(v_x_vals)),
    ])
}
