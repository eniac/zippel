//! PARI (Square R1CS SNARK) — small sanity check.
//!
//! Generates a tiny SR1CS instance (K=16 constraints, N=1 public input,
//! K_VARS=3 variables) in the upstream "instance outliner" layout, runs
//! PARI's setup (G), prover (P), and verifier (V), and asserts that
//! verification passes. Matches the matrix-layout assumptions in
//! `pari.zippel` so the verifier's Lagrange shortcut is sound.

use ark_ff::{Field, One, UniformRand, Zero};
use ark_poly::{
    DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain, Polynomial,
    univariate::DensePolynomial,
};
use ark_std::test_rng;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

type C = ArkBls12_381;
type F = <C as ArkConfig>::F;
type G1 = <C as ArkConfig>::G1;
type G2 = <C as ArkConfig>::G2;

const M_LOG: usize = 4;
const K: usize = 1 << M_LOG; // = 16 constraints
const N_PUB: usize = 1; // public inputs (includes the constant 1 at z[0])
const M_WIT: usize = 1; // "real" witness variables
// Total variables under the instance-outliner layout:
//   z = [1, x[1..N], w[0..M_WIT], aux[0..N]]   with aux[i] = z[i]^2.
const K_VARS: usize = 2 * N_PUB + M_WIT;
const KMN: usize = K_VARS - N_PUB; // length of `w` passed to zippel

fn main() {
    println!("=== PARI (Square R1CS, K={K}, N={N_PUB}, K_VARS={K_VARS}, KMN={KMN}) ===");

    let args = ZippelArgs::new(PathBuf::from("examples/pari/pari.zippel"));
    let mut handler: ZippelHandler<C> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("M"), &M_LOG);
    sizes.insert(&Tid::new("N"), &N_PUB);
    sizes.insert(&Tid::new("KMN"), &KMN);
    handler.compile(&sizes);

    let (inputs, public_inputs) = build_inputs();

    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let proof = handler
        .run_prover(prover_scheduled, inputs)
        .expect("run_prover failed");
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<C>(&proof);
    println!("Prover time:    {prover_elapsed:.2?}");
    println!(
        "Proof size:     {proof_bytes} bytes ({} elements)",
        proof.len()
    );
    for (i, v) in proof.iter().enumerate() {
        let variant = match v {
            Value::Scalar(_) => "Scalar",
            Value::G1(_) | Value::G1Affine(_) => "G1",
            Value::G2(_) | Value::G2Affine(_) => "G2",
            _ => "other",
        };
        println!("  proof[{i}] = {variant}");
    }

    let args = ZippelArgs::new(PathBuf::from("examples/pari/pari.zippel"));
    let mut verifier_handler: ZippelHandler<C> = ZippelHandler::new(args);
    verifier_handler.compile(&sizes);
    verifier_handler.set_public_inputs(public_inputs);
    let verifier_scheduled = verifier_handler.default_schedule_verifier();
    let verifier_start = Instant::now();
    let verifier_result = verifier_handler
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
        let analysis_args = ZippelArgs::new(PathBuf::from("examples/pari/pari.zippel"));
        let mut analysis_handler: ZippelHandler<C> = ZippelHandler::new(analysis_args);
        let mut analysis_sizes = Ctx::new();
        analysis_sizes.insert(&Tid::new("M"), &M_LOG);
        analysis_sizes.insert(&Tid::new("N"), &N_PUB);
        analysis_sizes.insert(&Tid::new("KMN"), &KMN);
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

/// Build a satisfying SR1CS instance in the upstream instance-outliner
/// layout (matching `pari.zippel`'s Lagrange shortcut requirement) and
/// return (full_inputs, public_inputs).
fn build_inputs() -> (Ctx<Vid, Value<C>>, Ctx<Vid, Value<C>>) {
    let mut rng = test_rng();

    // --- z = [1, x[1..N], w[0..M_WIT], aux[0..N]],  aux[i] = z[i]^2 ---
    let mut z = vec![F::zero(); K_VARS];
    z[0] = F::one();
    // With `N_PUB = 1` this loop is empty, but it stays here so the layout
    // generalizes if N_PUB is bumped. Silencing the clippy lint that flags
    // `1..1` as a reversed/empty range literal.
    #[allow(clippy::reversed_empty_ranges)]
    for i in 1..N_PUB {
        z[i] = nonzero(&mut rng);
    }
    for j in N_PUB..N_PUB + M_WIT {
        z[j] = nonzero(&mut rng);
    }
    for i in 0..N_PUB {
        z[N_PUB + M_WIT + i] = z[i] * z[i];
    }

    // --- Build matrices in outliner layout ---
    //   A: rows 0..K-N have nonzero entries only on witness columns
    //      [N_PUB, K_VARS). Rows K-N..K are e_i (one-hot at instance i).
    //   B: rows 0..K-N derived to satisfy (Az)² = Bz, with nonzero only
    //      on witness columns. Rows K-N..K hit the aux witness column
    //      that holds z[i]².
    let original_k = K - N_PUB;
    let mut a_mat = vec![vec![F::zero(); K_VARS]; K];
    let mut b_mat = vec![vec![F::zero(); K_VARS]; K];

    for j in 0..original_k {
        let mut a_row_acc = F::zero();
        // Sparse row: a couple of random nonzero coefficients on the
        // first witness columns, just enough to exercise the code path.
        let cols: Vec<usize> = (N_PUB..K_VARS.min(N_PUB + 2)).collect();
        for &c in &cols {
            let coeff = F::rand(&mut rng);
            a_mat[j][c] = coeff;
            a_row_acc += coeff * z[c];
        }
        // Place (Az)² in a witness column so (Bz)[j] = (Az)[j]².
        let c = N_PUB + (j % KMN);
        b_mat[j][c] = (a_row_acc * a_row_acc) * z[c].inverse().unwrap();
    }
    for i in 0..N_PUB {
        a_mat[original_k + i][i] = F::one();
        b_mat[original_k + i][N_PUB + M_WIT + i] = F::one();
    }

    // Sanity: (Az)² = Bz at every constraint.
    let az: Vec<F> = (0..K)
        .map(|i| (0..K_VARS).map(|j| a_mat[i][j] * z[j]).sum::<F>())
        .collect();
    let bz: Vec<F> = (0..K)
        .map(|i| (0..K_VARS).map(|j| b_mat[i][j] * z[j]).sum::<F>())
        .collect();
    for i in 0..K {
        assert_eq!(az[i] * az[i], bz[i], "SR1CS check failed in setup");
    }

    // ŵ_M = ẑ_M − x̂_M on the constraint domain.
    let mut x_padded = vec![F::zero(); K_VARS];
    x_padded[..N_PUB].copy_from_slice(&z[..N_PUB]);
    let x_a_evals: Vec<F> = (0..K)
        .map(|i| (0..K_VARS).map(|j| a_mat[i][j] * x_padded[j]).sum::<F>())
        .collect();
    let x_b_evals: Vec<F> = (0..K)
        .map(|i| (0..K_VARS).map(|j| b_mat[i][j] * x_padded[j]).sum::<F>())
        .collect();
    let w_a_evals: Vec<F> = (0..K).map(|i| az[i] - x_a_evals[i]).collect();
    let w_b_evals: Vec<F> = (0..K).map(|i| bz[i] - x_b_evals[i]).collect();

    // --- PARI Generator: sample trapdoor, build SRS ---
    let alpha = F::rand(&mut rng);
    let beta = F::rand(&mut rng);
    let delta2 = F::rand(&mut rng);
    let tau = F::rand(&mut rng);
    let g_g1: G1 = G1::rand(&mut rng);
    let h_g2: G2 = G2::rand(&mut rng);

    let domain = GeneralEvaluationDomain::<F>::new(K).expect("K-domain");
    let omega = domain.group_gen();

    let mut a_polys: Vec<DensePolynomial<F>> = Vec::with_capacity(K_VARS);
    let mut b_polys: Vec<DensePolynomial<F>> = Vec::with_capacity(K_VARS);
    for j in 0..K_VARS {
        let a_col: Vec<F> = (0..K).map(|i| a_mat[i][j]).collect();
        let b_col: Vec<F> = (0..K).map(|i| b_mat[i][j]).collect();
        a_polys.push(DensePolynomial::from_coefficients_vec(domain.ifft(&a_col)));
        b_polys.push(DensePolynomial::from_coefficients_vec(domain.ifft(&b_col)));
    }

    let delta2_inv = delta2.inverse().expect("delta2 != 0");
    let sigma_w_vec: Vec<G1> = (N_PUB..K_VARS)
        .map(|i| {
            let scalar =
                (alpha * a_polys[i].evaluate(&tau) + beta * b_polys[i].evaluate(&tau)) * delta2_inv;
            g_g1 * scalar
        })
        .collect();

    let tau_powers: Vec<F> = {
        let mut acc = F::one();
        (0..K)
            .map(|_| {
                let v = acc;
                acc *= tau;
                v
            })
            .collect()
    };

    let sigma_q_vec: Vec<G1> = tau_powers
        .iter()
        .map(|t| g_g1 * (*t * delta2_inv))
        .collect();
    let sigma_a_vec: Vec<G1> = tau_powers.iter().map(|t| g_g1 * (alpha * *t)).collect();
    let sigma_b_vec: Vec<G1> = tau_powers.iter().map(|t| g_g1 * (beta * *t)).collect();
    let sigma_q_prime_vec: Vec<G1> = tau_powers.iter().map(|t| g_g1 * *t).collect();

    let alpha_g_val: G1 = g_g1 * alpha;
    let beta_g_val: G1 = g_g1 * beta;
    let delta2_h_val: G2 = h_g2 * delta2;
    let tau_h_val: G2 = h_g2 * tau;

    // v_K(X) = X^K - 1
    let mut v_k_coeffs_vec = vec![F::zero(); K + 1];
    v_k_coeffs_vec[0] = -F::one();
    v_k_coeffs_vec[K] = F::one();

    // Lagrange shortcut inputs: x = (z[0], z[1], ..., z[N-1]),
    //                          omegas[i] = ω^{K-N+i}
    let x_vec: Vec<F> = z[..N_PUB].to_vec();
    let omegas_vec: Vec<F> = (0..N_PUB)
        .map(|i| omega.pow([(K - N_PUB + i) as u64]))
        .collect();
    let k_inv = F::from(K as u64).inverse().unwrap();

    let w_vec: Vec<F> = z[N_PUB..].to_vec();

    let z_a_value = Value::VecScalar(az);
    let z_b_value = Value::VecScalar(bz);
    let w_a_value = Value::VecScalar(w_a_evals);
    let w_b_value = Value::VecScalar(w_b_evals);
    let w_value = Value::VecScalar(w_vec);
    let x_value = Value::VecScalar(x_vec);
    let omegas_value = Value::VecScalar(omegas_vec);
    let v_k_coeffs_value = Value::VecScalar(v_k_coeffs_vec);

    let sigma_w_value = Value::VecG1(sigma_w_vec);
    let sigma_q_value = Value::VecG1(sigma_q_vec);
    let sigma_a_value = Value::VecG1(sigma_a_vec);
    let sigma_b_value = Value::VecG1(sigma_b_vec);
    let sigma_q_prime_value = Value::VecG1(sigma_q_prime_vec);

    let alpha_g_value = Value::G1(alpha_g_val);
    let beta_g_value = Value::G1(beta_g_val);
    let g_g1_value = Value::G1(g_g1);
    let delta2_h_value = Value::G2(delta2_h_val);
    let tau_h_value = Value::G2(tau_h_val);
    let h_g2_value = Value::G2(h_g2);
    let f_one_value = Value::Scalar(F::one());
    let k_inv_value = Value::Scalar(k_inv);

    let inputs = Ctx::<Vid, Value<C>>::from_iter([
        (Vid("z_a_evals".to_string()), z_a_value),
        (Vid("z_b_evals".to_string()), z_b_value),
        (Vid("w_a_evals".to_string()), w_a_value),
        (Vid("w_b_evals".to_string()), w_b_value),
        (Vid("w".to_string()), w_value),
        (Vid("x".to_string()), x_value.clone()),
        (Vid("omegas".to_string()), omegas_value.clone()),
        (Vid("sigma_w".to_string()), sigma_w_value.clone()),
        (Vid("sigma_q".to_string()), sigma_q_value.clone()),
        (Vid("sigma_a".to_string()), sigma_a_value.clone()),
        (Vid("sigma_b".to_string()), sigma_b_value.clone()),
        (
            Vid("sigma_q_prime".to_string()),
            sigma_q_prime_value.clone(),
        ),
        (Vid("alpha_g".to_string()), alpha_g_value.clone()),
        (Vid("beta_g".to_string()), beta_g_value.clone()),
        (Vid("g_g1".to_string()), g_g1_value.clone()),
        (Vid("delta2_h".to_string()), delta2_h_value.clone()),
        (Vid("tau_h".to_string()), tau_h_value.clone()),
        (Vid("h_g2".to_string()), h_g2_value.clone()),
        (Vid("v_k_coeffs".to_string()), v_k_coeffs_value.clone()),
        (Vid("f_one".to_string()), f_one_value.clone()),
        (Vid("k_inv".to_string()), k_inv_value.clone()),
    ]);

    let public_inputs = Ctx::<Vid, Value<C>>::from_iter([
        (Vid("x".to_string()), x_value),
        (Vid("omegas".to_string()), omegas_value),
        (Vid("alpha_g".to_string()), alpha_g_value),
        (Vid("beta_g".to_string()), beta_g_value),
        (Vid("g_g1".to_string()), g_g1_value),
        (Vid("delta2_h".to_string()), delta2_h_value),
        (Vid("tau_h".to_string()), tau_h_value),
        (Vid("h_g2".to_string()), h_g2_value),
        (Vid("f_one".to_string()), f_one_value),
        (Vid("k_inv".to_string()), k_inv_value),
    ]);

    (inputs, public_inputs)
}

fn nonzero<R: rand::Rng>(rng: &mut R) -> F {
    loop {
        let v = F::rand(rng);
        if !v.is_zero() {
            return v;
        }
    }
}
