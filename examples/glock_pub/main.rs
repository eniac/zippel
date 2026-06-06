//! Publicly-Verifiable Pari (non-DV Glock SNARK) — sanity check.
//!
//! Same SR1CS instance as examples/glock, but verification uses a pairing
//! check instead of DV scalar multiplications. The SRS omits the ε factor.

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
const K: usize = 1 << M_LOG;
const N_PUB: usize = 1;
const M_WIT: usize = 1;
const K_VARS: usize = 2 * N_PUB + M_WIT;
const KMN: usize = K_VARS - N_PUB;

fn main() {
    println!("=== PV-Pari / Glock-pub SNARK (K={K}, N={N_PUB}, K_VARS={K_VARS}) ===");

    let args = ZippelArgs::new(PathBuf::from("examples/glock_pub/glock_pub.zippel"));
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
        .expect("pv_pari prover failed");
    let prove_elapsed = t.elapsed();

    let bytes = proof_size_bytes::<C>(&proof);
    println!("Prover time:  {prove_elapsed:.2?}");
    println!("Proof size:   {bytes} bytes ({} elements)", proof.len());
    for (i, v) in proof.iter().enumerate() {
        let tag = match v {
            Value::Scalar(_) => "F",
            Value::G1(_) | Value::G1Affine(_) => "G1",
            Value::G2(_) | Value::G2Affine(_) => "G2",
            _ => "?",
        };
        println!("  proof[{i}] = {tag}");
    }

    let args2 = ZippelArgs::new(PathBuf::from("examples/glock_pub/glock_pub.zippel"));
    let mut vhandler: ZippelHandler<C> = ZippelHandler::new(args2);
    vhandler.compile(&sizes);
    vhandler.set_public_inputs(public_inputs);

    let verifier_sched = vhandler.default_schedule_verifier();
    let t = Instant::now();
    let vresult = vhandler
        .run_verifier(verifier_sched, proof)
        .expect("pv_pari verifier failed");
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

    let mut z = vec![F::zero(); K_VARS];
    z[0] = F::one();
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

    // ── SRS: sample τ, δ (no ε — publicly verifiable uses pairings) ──────────
    let tau   = F::rand(&mut rng);
    let delta = F::rand(&mut rng);
    let g_g1: G1 = G1::rand(&mut rng);
    let h_g2: G2 = G2::rand(&mut rng);

    let domain = GeneralEvaluationDomain::<F>::new(K).expect("domain");

    let mut a_polys: Vec<DensePolynomial<F>> = Vec::with_capacity(K_VARS);
    let mut b_polys: Vec<DensePolynomial<F>> = Vec::with_capacity(K_VARS);
    for j in 0..K_VARS {
        let a_col: Vec<F> = (0..K).map(|i| a_mat[i][j]).collect();
        let b_col: Vec<F> = (0..K).map(|i| b_mat[i][j]).collect();
        a_polys.push(DensePolynomial::from_coefficients_vec(domain.ifft(&a_col)));
        b_polys.push(DensePolynomial::from_coefficients_vec(domain.ifft(&b_col)));
    }

    let tau_powers: Vec<F> = {
        let mut acc = F::one();
        (0..K).map(|_| { let v = acc; acc *= tau; v }).collect()
    };
    let tau_k = tau_powers[K - 1] * tau;
    let z_k_at_tau = tau_k - F::one();

    // σ_M: private witness columns (no ε)
    let sigma_m_vec: Vec<G1> = (N_PUB..K_VARS)
        .map(|i| {
            let s = a_polys[i].evaluate(&tau) + b_polys[i].evaluate(&tau) * delta;
            g_g1 * s
        })
        .collect();

    // σ_M_pub: public input columns (no ε)
    let sigma_m_pub_vec: Vec<G1> = (0..N_PUB)
        .map(|i| {
            let s = a_polys[i].evaluate(&tau) + b_polys[i].evaluate(&tau) * delta;
            g_g1 * s
        })
        .collect();

    // σ_Q: z_K(τ)·τ^j·δ·G  (no ε)
    let sigma_q_vec: Vec<G1> = tau_powers
        .iter()
        .map(|t| g_g1 * (z_k_at_tau * *t * delta))
        .collect();

    // σ_Ka: τ^i·G
    let sigma_ka_vec: Vec<G1> = tau_powers.iter().map(|t| g_g1 * *t).collect();

    // σ_Kr: τ^j·δ·G  (2K elements)
    let sigma_kr_vec: Vec<G1> = {
        let mut acc = F::one();
        (0..K + K)
            .map(|_| { let v = acc; acc *= tau; g_g1 * (v * delta) })
            .collect()
    };

    let mut v_k_coeffs_vec = vec![F::zero(); K + 1];
    v_k_coeffs_vec[0] = -F::one();
    v_k_coeffs_vec[K] = F::one();

    // Verifier key: δG (G1), τH (G2), H (G2)
    let delta_g_val: G1 = g_g1 * delta;
    let tau_h_val: G2   = h_g2 * tau;

    let x_vec: Vec<F> = z[..N_PUB].to_vec();
    let w_vec: Vec<F> = z[N_PUB..].to_vec();

    let inputs = Ctx::<Vid, Value<C>>::from_iter([
        (Vid("z_a_evals".into()), Value::VecScalar(az)),
        (Vid("z_b_evals".into()), Value::VecScalar(bz)),
        (Vid("w".into()), Value::VecScalar(w_vec)),
        (Vid("x".into()), Value::VecScalar(x_vec.clone())),
        (Vid("sigma_m".into()), Value::VecG1(sigma_m_vec)),
        (Vid("sigma_m_pub".into()), Value::VecG1(sigma_m_pub_vec.clone())),
        (Vid("sigma_q".into()), Value::VecG1(sigma_q_vec)),
        (Vid("sigma_ka".into()), Value::VecG1(sigma_ka_vec)),
        (Vid("sigma_kr".into()), Value::VecG1(sigma_kr_vec)),
        (Vid("v_k_coeffs".into()), Value::VecScalar(v_k_coeffs_vec)),
        (Vid("delta_g".into()), Value::G1(delta_g_val)),
        (Vid("tau_h".into()), Value::G2(tau_h_val)),
        (Vid("h_g2".into()), Value::G2(h_g2)),
        (Vid("g_g1".into()), Value::G1(g_g1)),
        (Vid("f_one".into()), Value::Scalar(F::one())),
    ]);

    let public_inputs = Ctx::<Vid, Value<C>>::from_iter([
        (Vid("x".into()), Value::VecScalar(x_vec)),
        (Vid("sigma_m_pub".into()), Value::VecG1(sigma_m_pub_vec)),
        (Vid("delta_g".into()), Value::G1(delta_g_val)),
        (Vid("tau_h".into()), Value::G2(tau_h_val)),
        (Vid("h_g2".into()), Value::G2(h_g2)),
        (Vid("g_g1".into()), Value::G1(g_g1)),
        (Vid("f_one".into()), Value::Scalar(F::one())),
    ]);

    (inputs, public_inputs)
}

fn nonzero<R: rand::Rng>(rng: &mut R) -> F {
    loop {
        let v = F::rand(rng);
        if !v.is_zero() { return v; }
    }
}
