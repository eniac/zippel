use ark_ff::Field;
use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;
use std::ops::Mul;
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
    println!("=== Coin Proof (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/coin_proof/coin_proof.zippel"));
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);

    // Compile the protocol
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

    // Static analysis
    println!("\n--- Static Analysis ---");
    let analysis_args = ZippelArgs::new(PathBuf::from("examples/coin_proof/coin_proof.zippel"));
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
            match &analysis.zk {
                Ok(()) => println!("ZK:             ✓"),
                Err(e) => println!("ZK:             ✗ {}", e),
            }
        }
        Err(_) => println!("Analysis:       ⚠ not supported (non-polynomial operations)"),
    }

    // Soundness: commented out — coin_proof has many Pedersen-commitment
    // witnesses and pairing terms; GB computation is too slow for interactive use.
    // let soundness_start = Instant::now();
    // let soundness_result = analysis_handler.analyze_special_soundness(vec![2]);
    // let soundness_elapsed = soundness_start.elapsed();
    // match &soundness_result {
    //     Ok(()) => println!("Soundness:      ✓ (2)-special sound"),
    //     Err(e) => println!("Soundness:      ✗ {}", e),
    // }
    // println!("Soundness time: {soundness_elapsed:.2?}");
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    type F = <ArkBls12_381 as ArkConfig>::F;
    type G1 = <ArkBls12_381 as ArkConfig>::G1;

    // Generators
    let f = G1::rand(&mut rng);
    let g = G1::rand(&mut rng);
    let h = G1::rand(&mut rng);
    let h1 = G1::rand(&mut rng);
    let h2 = G1::rand(&mut rng);

    // Private scalars
    let x1 = F::rand(&mut rng);
    let x2 = F::rand(&mut rng);
    let r_y = F::rand(&mut rng);
    let sk_u = F::rand(&mut rng);

    // Choose s, t, j
    let s = F::rand(&mut rng);
    let t = F::rand(&mut rng);
    let j = F::rand(&mut rng);

    // Alpha and beta
    let s_plus_j = s + j;
    let alpha = s_plus_j.inverse().unwrap();
    let t_plus_j = t + j;
    let beta = t_plus_j.inverse().unwrap();

    let r_b = F::rand(&mut rng);
    let r_c = F::rand(&mut rng);
    let r_d = F::rand(&mut rng);
    let r_beta = F::rand(&mut rng);

    let r_c_alpha = r_c * alpha;
    let r_d_beta = r_d * beta;

    // Calculate commitments (additive notation)
    let big_b = g.mul(sk_u) + h.mul(r_b);
    let big_c = g.mul(s) + h.mul(r_c);
    let big_d = g.mul(t) + h.mul(r_d);

    let big_y = h1.mul(x1) + h2.mul(x2) + f.mul(r_y);
    let big_s = g.mul(alpha) + g.mul(x1);
    let big_t = g.mul(sk_u) + g.mul(r_beta) + g.mul(x2);

    let k_sk_u = F::rand(&mut rng);
    let k_r_b = F::rand(&mut rng);
    let t_big_b = g.mul(k_sk_u) + h.mul(k_r_b);
    let ch = F::rand(&mut rng);
    let z_sk_u = k_sk_u + sk_u * ch;
    let z_r_b = k_r_b + r_b * ch;
    assert_eq!(
        g.mul(z_sk_u) + h.mul(z_r_b),
        t_big_b + big_b.mul(ch),
        "Native Sigma protocol check failed!"
    );
    println!("Native Sigma Protocol Check: ✓ OK");

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("x1".to_string()), Value::Scalar(x1)),
        (Vid("x2".to_string()), Value::Scalar(x2)),
        (Vid("r_y".to_string()), Value::Scalar(r_y)),
        (Vid("sk_u".to_string()), Value::Scalar(sk_u)),
        (Vid("alpha".to_string()), Value::Scalar(alpha)),
        (Vid("beta".to_string()), Value::Scalar(beta)),
        (Vid("s".to_string()), Value::Scalar(s)),
        (Vid("t".to_string()), Value::Scalar(t)),
        (Vid("r_b".to_string()), Value::Scalar(r_b)),
        (Vid("r_c".to_string()), Value::Scalar(r_c)),
        (Vid("r_d".to_string()), Value::Scalar(r_d)),
        (Vid("r_beta".to_string()), Value::Scalar(r_beta)),
        (Vid("r_c_alpha".to_string()), Value::Scalar(r_c_alpha)),
        (Vid("r_d_beta".to_string()), Value::Scalar(r_d_beta)),
        (Vid("f".to_string()), Value::G1(f)),
        (Vid("g".to_string()), Value::G1(g)),
        (Vid("h".to_string()), Value::G1(h)),
        (Vid("h1".to_string()), Value::G1(h1)),
        (Vid("h2".to_string()), Value::G1(h2)),
        (Vid("big_y".to_string()), Value::G1(big_y)),
        (Vid("big_s".to_string()), Value::G1(big_s)),
        (Vid("big_t".to_string()), Value::G1(big_t)),
        (Vid("big_b".to_string()), Value::G1(big_b)),
        (Vid("big_c".to_string()), Value::G1(big_c)),
        (Vid("big_d".to_string()), Value::G1(big_d)),
        (Vid("j".to_string()), Value::Scalar(j)),
    ])
}
