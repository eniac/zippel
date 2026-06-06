//! DV-Pari (Glock SNARK) — sanity check / demo.
//!
//! Generates a tiny SR1CS instance (K=16 constraints, N=1 public input,
//! K_VARS=3 variables) in the instance-outliner layout, runs DV-Pari's
//! setup (G), prover (P), and verifier (V), and asserts verification passes.
//!
//! Key changes versus the Pari example:
//!   - SRS has no α/β toxic waste; uses τ, δ, ε instead.
//!   - Proof is (P: G1, a: F, Q: G1) — 2 G1 + 1 F.
//!   - Verifier performs scalar multiplications (no pairings).

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

const M_LOG: usize = 4;
const K: usize = 1 << M_LOG; // 16 constraints
const N_PUB: usize = 1; // public inputs (includes constant 1 at z[0])
const M_WIT: usize = 1; // "real" witness variables
// Instance-outliner layout: z = [1, x[1..N], w[0..M_WIT], aux[0..N]], aux[i] = z[i]^2
const K_VARS: usize = 2 * N_PUB + M_WIT;
const KMN: usize = K_VARS - N_PUB;

fn main() {
    println!("=== DV-Pari / Glock SNARK (K={K}, N={N_PUB}, K_VARS={K_VARS}) ===");

    let args = ZippelArgs::new(PathBuf::from("examples/glock/glock.zippel"));
    let mut handler: ZippelHandler<C> = ZippelHandler::new(args);

    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("M"), &M_LOG);
    sizes.insert(&Tid::new("N"), &N_PUB);
    sizes.insert(&Tid::new("KMN"), &KMN);
    handler.compile(&sizes);

    let (inputs, public_inputs) = build_inputs();

    let prover_sched = handler.default_schedule_prover();
    let t = Instant::now();
    let proof = handler
        .run_prover(prover_sched, inputs)
        .expect("dv_pari prover failed");
    let prove_elapsed = t.elapsed();

    let bytes = proof_size_bytes::<C>(&proof);
    println!("Prover time:  {prove_elapsed:.2?}");
    println!("Proof size:   {bytes} bytes ({} elements)", proof.len());
    for (i, v) in proof.iter().enumerate() {
        let tag = match v {
            Value::Scalar(_) => "F",
            Value::G1(_) | Value::G1Affine(_) => "G1",
            _ => "?",
        };
        println!("  proof[{i}] = {tag}");
    }

    // Re-compile a fresh handler for the verifier (same .zippel path).
    let args2 = ZippelArgs::new(PathBuf::from("examples/glock/glock.zippel"));
    let mut vhandler: ZippelHandler<C> = ZippelHandler::new(args2);
    vhandler.compile(&sizes);
    vhandler.set_public_inputs(public_inputs);

    let verifier_sched = vhandler.default_schedule_verifier();
    let t = Instant::now();
    let vresult = vhandler
        .run_verifier(verifier_sched, proof)
        .expect("dv_pari verifier failed");
    let verify_elapsed = t.elapsed();

    let result = check_verification(vresult);
    println!("Verifier time:{verify_elapsed:.2?}");
    if result.passed {
        println!("Verification: ✓ PASSED");
    } else {
        println!("Verification: ✗ FAILED");
        std::process::exit(1);
    }
}

fn build_inputs() -> (Ctx<Vid, Value<C>>, Ctx<Vid, Value<C>>) {
    let mut rng = test_rng();

    // ── Witness: z = [1, x[1..N], w[0..M_WIT], aux[0..N]], aux[i] = z[i]^2 ──
    let mut z = [F::zero(); K_VARS];
    z[0] = F::one();
    for v in z[1..N_PUB].iter_mut() {
        *v = nonzero(&mut rng);
    }
    for v in z[N_PUB..N_PUB + M_WIT].iter_mut() {
        *v = nonzero(&mut rng);
    }
    for i in 0..N_PUB {
        z[N_PUB + M_WIT + i] = z[i] * z[i];
    }

    // ── Matrices: instance-outliner layout ──────────────────────────────────
    let original_k = K - N_PUB;
    let mut a_mat = vec![vec![F::zero(); K_VARS]; K];
    let mut b_mat = vec![vec![F::zero(); K_VARS]; K];

    for j in 0..original_k {
        let mut acc = F::zero();
        let cols: Vec<usize> = (N_PUB..K_VARS.min(N_PUB + 2)).collect();
        for &c in &cols {
            let coeff = F::rand(&mut rng);
            a_mat[j][c] = coeff;
            acc += coeff * z[c];
        }
        let c = N_PUB + (j % KMN);
        b_mat[j][c] = (acc * acc) * z[c].inverse().unwrap();
    }
    for i in 0..N_PUB {
        a_mat[original_k + i][i] = F::one();
        b_mat[original_k + i][N_PUB + M_WIT + i] = F::one();
    }

    let az: Vec<F> = (0..K)
        .map(|i| (0..K_VARS).map(|j| a_mat[i][j] * z[j]).sum::<F>())
        .collect();
    let bz: Vec<F> = (0..K)
        .map(|i| (0..K_VARS).map(|j| b_mat[i][j] * z[j]).sum::<F>())
        .collect();
    for i in 0..K {
        assert_eq!(az[i] * az[i], bz[i], "SR1CS violated at constraint {i}");
    }

    // ── DV-Pari SRS: sample toxic waste (τ, δ, ε) ──────────────────────────
    let tau = F::rand(&mut rng);
    let delta = F::rand(&mut rng);
    let eps = F::rand(&mut rng);
    let g_g1: G1 = G1::rand(&mut rng);

    let domain = GeneralEvaluationDomain::<F>::new(K).expect("domain");

    // Column polynomials a_i(X), b_i(X) via IFFT of A's and B's columns.
    let mut a_polys: Vec<DensePolynomial<F>> = Vec::with_capacity(K_VARS);
    let mut b_polys: Vec<DensePolynomial<F>> = Vec::with_capacity(K_VARS);
    for j in 0..K_VARS {
        let a_col: Vec<F> = (0..K).map(|i| a_mat[i][j]).collect();
        let b_col: Vec<F> = (0..K).map(|i| b_mat[i][j]).collect();
        a_polys.push(DensePolynomial::from_coefficients_vec(domain.ifft(&a_col)));
        b_polys.push(DensePolynomial::from_coefficients_vec(domain.ifft(&b_col)));
    }

    // τ powers: τ^0, τ^1, ..., τ^{K−1}
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
    // τ^K (needed for z_K(τ) = τ^K − 1)
    let tau_k = tau_powers[K - 1] * tau;
    let z_k_at_tau = tau_k - F::one();

    // σ_M[i] = (a_i(τ) + b_i(τ)·δ)·ε · G   for private witness columns i ∈ [N_PUB, K_VARS)
    let sigma_m_vec: Vec<G1> = (N_PUB..K_VARS)
        .map(|i| {
            let s = (a_polys[i].evaluate(&tau) + b_polys[i].evaluate(&tau) * delta) * eps;
            g_g1 * s
        })
        .collect();

    // σ_M_pub[i] = (a_i(τ) + b_i(τ)·δ)·ε · G   for public columns i ∈ [0, N_PUB)
    // Passed as a public parameter so the verifier can add the public commitment.
    let sigma_m_pub_vec: Vec<G1> = (0..N_PUB)
        .map(|i| {
            let s = (a_polys[i].evaluate(&tau) + b_polys[i].evaluate(&tau) * delta) * eps;
            g_g1 * s
        })
        .collect();

    // σ_Q[j] = z_K(τ)·τ^j·δ·ε · G
    let sigma_q_vec: Vec<G1> = tau_powers
        .iter()
        .map(|t| g_g1 * (z_k_at_tau * *t * delta * eps))
        .collect();

    // σ_Ka[j] = τ^j · G
    let sigma_ka_vec: Vec<G1> = tau_powers.iter().map(|t| g_g1 * *t).collect();

    // σ_Kr[j] = τ^j · δ · G  (need up to 2K elements; extend tau_powers)
    let sigma_kr_vec: Vec<G1> = {
        let mut acc = F::one();
        (0..K + K)
            .map(|_| {
                let v = acc;
                acc *= tau;
                g_g1 * (v * delta)
            })
            .collect()
    };

    // v_K(X) = X^K − 1
    let mut v_k_coeffs_vec = vec![F::zero(); K + 1];
    v_k_coeffs_vec[0] = -F::one();
    v_k_coeffs_vec[K] = F::one();

    // Public inputs: just z[0..N_PUB]
    let x_vec: Vec<F> = z[..N_PUB].to_vec();
    let w_vec: Vec<F> = z[N_PUB..].to_vec();

    let inputs = Ctx::<Vid, Value<C>>::from_iter([
        (Vid("z_a_evals".into()), Value::VecScalar(az)),
        (Vid("z_b_evals".into()), Value::VecScalar(bz)),
        (Vid("w".into()), Value::VecScalar(w_vec)),
        (Vid("x".into()), Value::VecScalar(x_vec.clone())),
        (Vid("sigma_m".into()), Value::VecG1(sigma_m_vec)),
        (
            Vid("sigma_m_pub".into()),
            Value::VecG1(sigma_m_pub_vec.clone()),
        ),
        (Vid("sigma_q".into()), Value::VecG1(sigma_q_vec)),
        (Vid("sigma_ka".into()), Value::VecG1(sigma_ka_vec)),
        (Vid("sigma_kr".into()), Value::VecG1(sigma_kr_vec)),
        (Vid("v_k_coeffs".into()), Value::VecScalar(v_k_coeffs_vec)),
        (Vid("tau".into()), Value::Scalar(tau)),
        (Vid("delta".into()), Value::Scalar(delta)),
        (Vid("eps".into()), Value::Scalar(eps)),
        (Vid("g_g1".into()), Value::G1(g_g1)),
        (Vid("f_one".into()), Value::Scalar(F::one())),
    ]);

    let public_inputs = Ctx::<Vid, Value<C>>::from_iter([
        (Vid("x".into()), Value::VecScalar(x_vec)),
        (Vid("sigma_m_pub".into()), Value::VecG1(sigma_m_pub_vec)),
        (Vid("tau".into()), Value::Scalar(tau)),
        (Vid("delta".into()), Value::Scalar(delta)),
        (Vid("eps".into()), Value::Scalar(eps)),
        (Vid("g_g1".into()), Value::G1(g_g1)),
        (Vid("f_one".into()), Value::Scalar(F::one())),
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
