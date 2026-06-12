//! Standalone PST13 example: sample (p, z), run the zippel prover and verifier,
//! and report timings + a tiny static analysis pass.
//!
//! N (the number of variables / log_2 of the polynomial size) is bound at
//! runtime via the sizes context, so this example covers any N in the range
//! the helpers support (1..=20 — see pst13.zippel).

use ark_std::One;
use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

/// N = number of variables; 2^N = number of polynomial coefficients.
/// Override with the first CLI arg.
const DEFAULT_N: usize = 4;

fn main() {
    let n: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(DEFAULT_N);
    assert!(
        (1..=20).contains(&n),
        "N must be in 1..=20 (pst13.zippel helpers cap at K=20)"
    );

    println!("=== PST13 Multilinear PCS (ArkBls12_381, N={n}) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/pst13/pst13.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("N"), &n);
    handler.compile(&sizes);

    let inputs = prover_create_inputs(n);
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

    let analysis_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        println!("\n--- Static Analysis ---");
        let analysis_args = ZippelArgs::new(PathBuf::from("examples/pst13/pst13.zippel"));
        let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
        let mut analysis_sizes = Ctx::new();
        analysis_sizes.insert(&Tid::new("N"), &n);
        analysis_handler.compile(&analysis_sizes);

        let completeness_start = Instant::now();
        match analysis_handler.analyze_completeness() {
            Ok(()) => println!("Completeness:    ✓"),
            Err(e) => println!("Completeness:    ✗ {}", e),
        }
        println!("Completeness time: {:.2?}", completeness_start.elapsed());

        let zk_start = Instant::now();
        match analysis_handler.analyze_knowledge() {
            Ok(()) => println!("ZK:              ✓"),
            Err(e) => println!("ZK:              ✗ {}", e),
        }
        println!("ZK time:         {:.2?}", zk_start.elapsed());
    }));
    if analysis_result.is_err() {
        println!("Analysis:        ⚠ not supported (non-polynomial operations)");
    }
}

fn prover_create_inputs(n: usize) -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let size = 1usize << n;

    let gen_g = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let gen_h = <ArkBls12_381 as ArkConfig>::G2::rand(&mut rng);

    let one = <ArkBls12_381 as ArkConfig>::F::one();
    let alpha: Vec<_> = (0..n)
        .map(|_| <ArkBls12_381 as ArkConfig>::F::rand(&mut rng))
        .collect();
    let one_m_alpha: Vec<_> = alpha.iter().map(|a| one - a).collect();

    // ck[i] = eq_N(α, i) · G, with i's bits MSB-first so the proto's
    // "split first half / second half" peels variable 1 first.
    let ck_n_scalars: Vec<_> = (0..size)
        .map(|i| {
            (0..n).fold(one, |acc, j| {
                let bit = (i >> (n - 1 - j)) & 1;
                if bit == 1 {
                    acc * alpha[j]
                } else {
                    acc * one_m_alpha[j]
                }
            })
        })
        .collect();
    let ck_n = Value::VecG1(ck_n_scalars.iter().map(|s| gen_g * s).collect());

    let p_scalars: Vec<_> = (0..size)
        .map(|_| <ArkBls12_381 as ArkConfig>::F::rand(&mut rng))
        .collect();
    let p = Value::VecScalar(p_scalars.clone());

    let z_scalars: Vec<_> = (0..n)
        .map(|_| <ArkBls12_381 as ArkConfig>::F::rand(&mut rng))
        .collect();
    let z = Value::VecScalar(z_scalars.clone());

    // y = p̃(z) = Σ_i p_i · eq_N(z, i)
    let y_val = (0..size).fold(<ArkBls12_381 as ArkConfig>::F::from(0u64), |acc, i| {
        let eq_z_i = (0..n).fold(one, |prod, j| {
            let bit = (i >> (n - 1 - j)) & 1;
            if bit == 1 {
                prod * z_scalars[j]
            } else {
                prod * (one - z_scalars[j])
            }
        });
        acc + p_scalars[i] * eq_z_i
    });
    let y = Value::Scalar(y_val);

    let alpha_h = Value::VecG2(alpha.iter().map(|a| gen_h * a).collect());

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("p".to_string()), p),
        (Vid("z".to_string()), z),
        (Vid("y".to_string()), y),
        (Vid("ck_N".to_string()), ck_n),
        (Vid("g_gen".to_string()), Value::G1(gen_g)),
        (Vid("h_gen".to_string()), Value::G2(gen_h)),
        (Vid("alpha_H".to_string()), alpha_h),
    ])
}
