use ark_ff::{Field, One, UniformRand, Zero};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_std::test_rng;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

use crate::common;

type C = ArkBls12_381;
type F = <C as ArkConfig>::F;
type G1 = <C as ArkConfig>::G1;
type G2 = <C as ArkConfig>::G2;

pub fn run(_args: &[String], opts: &common::RunOptions) {
    println!("=== DeKART Range Proof ===");
    let n_size = 3;
    let b_size = 2;
    let l_chunk = 8;
    let h_deg = (b_size - 1) * n_size;

    let args = ZippelArgs::new(PathBuf::from("examples/dekart/dekart.zippel"));
    let mut handler: ZippelHandler<C> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("n"), &n_size);
    sizes.insert(&Tid::new("b"), &b_size);
    sizes.insert(&Tid::new("l_chunk"), &l_chunk);
    handler.compile(&sizes);

    let inputs = build_inputs(n_size, b_size, l_chunk, h_deg);
    let prover_start = Instant::now();
    let proof = handler.run_prover(&inputs).expect("run_prover failed");
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<C>(&proof);
    println!("Prover time:    {prover_elapsed:.2?}");
    println!(
        "Proof size:     {proof_bytes} bytes ({} elements)",
        proof.len()
    );

    let args = ZippelArgs::new(PathBuf::from("examples/dekart/dekart.zippel"));
    let mut verifier_handler: ZippelHandler<C> = ZippelHandler::new(args);
    verifier_handler.compile(&sizes);
    let verifier_start = Instant::now();
    let verifier_result = verifier_handler
        .run_verifier(&proof, &inputs)
        .expect("run_verifier failed");
    let verifier_elapsed = verifier_start.elapsed();
    let passed = check_verification(&verifier_result);
    println!("Verifier time:  {verifier_elapsed:.2?}");
    if passed {
        println!("Verification:   ✓ PASSED");
    } else {
        println!("Verification:   ✗ FAILED");
        for (i, v) in verifier_result.iter().enumerate() {
            println!("  verify[{i}] = {v}");
        }
        std::process::exit(1);
    }

    if !opts.analyses {
        return;
    }
    let analysis_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        println!("\n--- Static Analysis ---");

        let completeness_start = Instant::now();
        match handler.analyze_completeness() {
            Ok(()) => println!("Completeness:    ✓"),
            Err(e) => println!("Completeness:    ✗ {}", e),
        }
        println!("Completeness time: {:.2?}", completeness_start.elapsed());

        let zk_start = Instant::now();
        match handler.analyze_knowledge() {
            Ok(()) => println!("ZK:              ✓"),
            Err(e) => println!("ZK:              ✗ {}", e),
        }
        println!("ZK time:         {:.2?}", zk_start.elapsed());
    }));
    if analysis_result.is_err() {
        println!("Analysis:        ⚠ not supported (non-polynomial operations)");
    }
}

fn build_inputs(n_size: usize, b_size: usize, l_chunk: usize, h_deg: usize) -> Ctx<Vid, Value<C>> {
    let mut rng = test_rng();

    // 1. Setup generators & trapdoors
    let gen_g1 = G1::rand(&mut rng);
    let gen_g2 = G2::rand(&mut rng);
    let tau = F::rand(&mut rng);
    let xi = F::rand(&mut rng);

    let srs_g2_tau = gen_g2 * tau;
    let srs_g2_xi = gen_g2 * xi;
    let xi_g1 = gen_g1 * xi;

    // 2. SRS in G1: monomial [τ^i]_1 for the quotients, Lagrange [ℓ_i(τ)]_1
    //    over the size-(n+1) domain for the commitments to f and the digits.
    let domain_s = GeneralEvaluationDomain::<F>::new(n_size + 1).unwrap();
    let tau_pows: Vec<F> = (0..=n_size).map(|i| tau.pow([i as u64])).collect();
    let srs_g1_lagr_vec: Vec<G1> = domain_s
        .ifft(&tau_pows)
        .iter()
        .map(|l| gen_g1 * l)
        .collect();

    let mut srs_g1_h_vec = Vec::new();
    let mut current_tau = F::one();
    for _ in 0..=h_deg {
        srs_g1_h_vec.push(gen_g1 * current_tau);
        current_tau *= tau;
    }

    // 3. Witness values to prove (must be in [0, b_size^l_chunk - 1])
    // With n = n_size, b = b_size, l_chunk = l_chunk, values must be in [0, b_size^l_chunk - 1]
    let z_vals = vec![5u64, 12u64, 7u64];
    assert_eq!(z_vals.len(), n_size, "z_vals length must equal n_size");
    for &z in &z_vals {
        assert!(
            z < (b_size as u64).pow(u32::try_from(l_chunk).unwrap()),
            "witness value {} exceeds max allowed range {}",
            z,
            (b_size as u64).pow(u32::try_from(l_chunk).unwrap()) - 1
        );
    }
    let mut f_evals = vec![F::zero()];
    for z in &z_vals {
        f_evals.push(F::from(*z));
    }

    // Decompose values into radix-b digits (the prover blinds f_j(ω^0) itself)
    let mut chunks_bits = Vec::new();
    for j in 0..l_chunk {
        let digits = z_vals
            .iter()
            .map(|z| {
                F::from((z / (b_size as u64).pow(u32::try_from(j).unwrap())) % (b_size as u64))
            })
            .collect();
        chunks_bits.push(Value::VecScalar(digits));
    }

    // Commitment randomness of the statement
    let rho = F::rand(&mut rng);

    // Range constants
    let mut b_pow = Vec::new();
    let mut current_pow = F::one();
    let b_scalar = F::from(b_size as u64);
    for _ in 0..l_chunk {
        b_pow.push(current_pow);
        current_pow *= b_scalar;
    }

    // 4. s0_commit commits to the Lagrange polynomial L_0: [ℓ_0(τ)]_1
    let s0_commit = srs_g1_lagr_vec[0];

    // 5. Statement: com_f = Σ_i f(ω^i)·[ℓ_i(τ)]_1 + ρ·[ξ]_1
    let mut com_f = xi_g1 * rho;
    for (v, g) in f_evals.iter().zip(srs_g1_lagr_vec.iter()) {
        com_f += *g * *v;
    }

    Ctx::<Vid, Value<C>>::from_iter([
        (Vid("f_evals".to_string()), Value::VecScalar(f_evals)),
        (Vid("chunks_bits".to_string()), Value::Vec(chunks_bits)),
        (Vid("rho".to_string()), Value::Scalar(rho)),
        (Vid("com_f".to_string()), Value::G1(com_f)),
        (Vid("b_pow".to_string()), Value::VecScalar(b_pow.clone())),
        (Vid("gen_g1".to_string()), Value::G1(gen_g1)),
        (Vid("gen_g2".to_string()), Value::G2(gen_g2)),
        (Vid("srs_g2_tau".to_string()), Value::G2(srs_g2_tau)),
        (Vid("srs_g2_xi".to_string()), Value::G2(srs_g2_xi)),
        (Vid("xi_g1".to_string()), Value::G1(xi_g1)),
        (Vid("s0_commit".to_string()), Value::G1(s0_commit)),
        (
            Vid("srs_g1_lagr".to_string()),
            Value::VecG1(srs_g1_lagr_vec),
        ),
        (Vid("srs_g1_h".to_string()), Value::VecG1(srs_g1_h_vec)),
        (
            Vid("v_star".to_string()),
            Value::VecScalar(vec![F::one(); n_size + 1]),
        ),
    ])
}
