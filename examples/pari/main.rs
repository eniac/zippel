//! PARI (Square R1CS SNARK) — small sanity check.
//!
//! Generates a tiny SR1CS instance (k=16 constraints, N=1 instance input,
//! `k_vars=3` variables) in the upstream "instance outliner" layout, runs
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
use lang::id::Vid;
use share::Ctx;

use crate::common;
use crate::common::size;

type C = ArkBls12_381;
type F = <C as ArkConfig>::F;
type G1 = <C as ArkConfig>::G1;
type G2 = <C as ArkConfig>::G2;

// Total variables under the instance-outliner layout:
//   z = [1, x[1..N], w[0..m_wit], aux[0..N]]   with aux[i] = z[i]^2.

/// Build a satisfying SR1CS instance in the upstream instance-outliner
/// layout (matching `pari.zippel`'s Lagrange shortcut requirement).
fn make_inputs(sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<C>> {
    let m_log = size(sizes, "M");
    let k = 1 << m_log;
    let n_pub = size(sizes, "N");
    let m_wit = size(sizes, "KMN") - size(sizes, "N");
    let k_vars = size(sizes, "N") + size(sizes, "KMN");
    let kmn = size(sizes, "KMN");

    let mut rng = test_rng();

    // --- z = [1, x[1..N], w[0..m_wit], aux[0..N]],  aux[i] = z[i]^2 ---
    let mut z = vec![F::zero(); k_vars];
    z[0] = F::one();
    // With `n_pub = 1` this loop is empty, but it stays here so the layout
    // generalizes if n_pub is bumped.
    for z_i in z.iter_mut().take(n_pub).skip(1) {
        *z_i = nonzero(&mut rng);
    }
    for z_j in z.iter_mut().skip(n_pub).take(m_wit) {
        *z_j = nonzero(&mut rng);
    }
    for i in 0..n_pub {
        z[n_pub + m_wit + i] = z[i] * z[i];
    }

    // --- Build matrices in outliner layout ---
    //   A: rows 0..k-N have nonzero entries only on witness columns
    //      [n_pub, k_vars). Rows k-N..k are e_i (one-hot at instance i).
    //   B: rows 0..k-N derived to satisfy (Az)² = Bz, with nonzero only
    //      on witness columns. Rows k-N..k hit the aux witness column
    //      that holds z[i]².
    let original_k = k - n_pub;
    let mut a_mat = vec![vec![F::zero(); k_vars]; k];
    let mut b_mat = vec![vec![F::zero(); k_vars]; k];

    for j in 0..original_k {
        let mut a_row_acc = F::zero();
        // Sparse row: a couple of random nonzero coefficients on the
        // first witness columns, just enough to exercise the code path.
        let cols: Vec<usize> = (n_pub..k_vars.min(n_pub + 2)).collect();
        for &c in &cols {
            let coeff = F::rand(&mut rng);
            a_mat[j][c] = coeff;
            a_row_acc += coeff * z[c];
        }
        // Place (Az)² in a witness column so (Bz)[j] = (Az)[j]².
        let c = n_pub + (j % kmn);
        b_mat[j][c] = (a_row_acc * a_row_acc) * z[c].inverse().unwrap();
    }
    for i in 0..n_pub {
        a_mat[original_k + i][i] = F::one();
        b_mat[original_k + i][n_pub + m_wit + i] = F::one();
    }

    // Sanity: (Az)² = Bz at every constraint.
    let az: Vec<F> = (0..k)
        .map(|i| (0..k_vars).map(|j| a_mat[i][j] * z[j]).sum::<F>())
        .collect();
    let bz: Vec<F> = (0..k)
        .map(|i| (0..k_vars).map(|j| b_mat[i][j] * z[j]).sum::<F>())
        .collect();
    for i in 0..k {
        assert_eq!(az[i] * az[i], bz[i], "SR1CS check failed in setup");
    }

    // ŵ_M = ẑ_M − x̂_M on the constraint domain.
    let mut x_padded = vec![F::zero(); k_vars];
    x_padded[..n_pub].copy_from_slice(&z[..n_pub]);
    let x_a_evals: Vec<F> = (0..k)
        .map(|i| (0..k_vars).map(|j| a_mat[i][j] * x_padded[j]).sum::<F>())
        .collect();
    let x_b_evals: Vec<F> = (0..k)
        .map(|i| (0..k_vars).map(|j| b_mat[i][j] * x_padded[j]).sum::<F>())
        .collect();
    let w_a_evals: Vec<F> = (0..k).map(|i| az[i] - x_a_evals[i]).collect();
    let w_b_evals: Vec<F> = (0..k).map(|i| bz[i] - x_b_evals[i]).collect();

    // --- PARI Generator: sample trapdoor, build SRS ---
    let alpha = F::rand(&mut rng);
    let beta = F::rand(&mut rng);
    let delta2 = F::rand(&mut rng);
    let tau = F::rand(&mut rng);
    let g_g1: G1 = G1::rand(&mut rng);
    let h_g2: G2 = G2::rand(&mut rng);

    let domain = GeneralEvaluationDomain::<F>::new(k).expect("k-domain");
    let omega = domain.group_gen();

    let mut a_polys: Vec<DensePolynomial<F>> = Vec::with_capacity(k_vars);
    let mut b_polys: Vec<DensePolynomial<F>> = Vec::with_capacity(k_vars);
    for j in 0..k_vars {
        let a_col: Vec<F> = (0..k).map(|i| a_mat[i][j]).collect();
        let b_col: Vec<F> = (0..k).map(|i| b_mat[i][j]).collect();
        a_polys.push(DensePolynomial::from_coefficients_vec(domain.ifft(&a_col)));
        b_polys.push(DensePolynomial::from_coefficients_vec(domain.ifft(&b_col)));
    }

    let delta2_inv = delta2.inverse().expect("delta2 != 0");
    let sigma_w_vec: Vec<G1> = (n_pub..k_vars)
        .map(|i| {
            let scalar =
                (alpha * a_polys[i].evaluate(&tau) + beta * b_polys[i].evaluate(&tau)) * delta2_inv;
            g_g1 * scalar
        })
        .collect();

    let tau_powers: Vec<F> = {
        let mut acc = F::one();
        (0..k)
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

    // Lagrange shortcut inputs: x = (z[0], z[1], ..., z[N-1]),
    //                          omegas[i] = ω^{k-N+i}
    let x_vec: Vec<F> = z[..n_pub].to_vec();
    let omegas_vec: Vec<F> = (0..n_pub)
        .map(|i| omega.pow([(k - n_pub + i) as u64]))
        .collect();
    let k_inv = F::from(k as u64).inverse().unwrap();

    let w_vec: Vec<F> = z[n_pub..].to_vec();

    let z_a_value = Value::vec_scalar(az);
    let z_b_value = Value::vec_scalar(bz);
    let w_a_value = Value::vec_scalar(w_a_evals);
    let w_b_value = Value::vec_scalar(w_b_evals);
    let w_value = Value::vec_scalar(w_vec);
    let x_value = Value::vec_scalar(x_vec);
    let omegas_value = Value::vec_scalar(omegas_vec);

    let sigma_w_value = Value::vec_g1(sigma_w_vec);
    let sigma_q_value = Value::vec_g1(sigma_q_vec);
    let sigma_a_value = Value::vec_g1(sigma_a_vec);
    let sigma_b_value = Value::vec_g1(sigma_b_vec);
    let sigma_q_prime_value = Value::vec_g1(sigma_q_prime_vec);

    let alpha_g_value = Value::g1(alpha_g_val);
    let beta_g_value = Value::g1(beta_g_val);
    let g_g1_value = Value::g1(g_g1);
    let delta2_h_value = Value::g2(delta2_h_val);
    let tau_h_value = Value::g2(tau_h_val);
    let h_g2_value = Value::g2(h_g2);
    let k_inv_value = Value::Scalar(k_inv);

    Ctx::<Vid, Value<C>>::from_iter([
        (Vid("z_a_evals".to_string()), z_a_value),
        (Vid("z_b_evals".to_string()), z_b_value),
        (Vid("w_a_evals".to_string()), w_a_value),
        (Vid("w_b_evals".to_string()), w_b_value),
        (Vid("w".to_string()), w_value),
        (Vid("x".to_string()), x_value),
        (Vid("omegas".to_string()), omegas_value),
        (Vid("sigma_w".to_string()), sigma_w_value),
        (Vid("sigma_q".to_string()), sigma_q_value),
        (Vid("sigma_a".to_string()), sigma_a_value),
        (Vid("sigma_b".to_string()), sigma_b_value),
        (Vid("sigma_q_prime".to_string()), sigma_q_prime_value),
        (Vid("alpha_g".to_string()), alpha_g_value),
        (Vid("beta_g".to_string()), beta_g_value),
        (Vid("g_g1".to_string()), g_g1_value),
        (Vid("delta2_h".to_string()), delta2_h_value),
        (Vid("tau_h".to_string()), tau_h_value),
        (Vid("h_g2".to_string()), h_g2_value),
        (Vid("k_inv".to_string()), k_inv_value),
    ])
}

fn nonzero<R: rand::Rng>(rng: &mut R) -> F {
    loop {
        let v = F::rand(rng);
        if !v.is_zero() {
            return v;
        }
    }
}

pub fn spec() -> common::ExampleSpec<ArkBls12_381> {
    common::ExampleSpec {
        source: "examples/pari/pari.zippel",
        defaults: &[("M", 3), ("N", 2), ("KMN", 3)],
        validate: Some(|sizes, analysis| {
            common::check_power_of_two(sizes, "M")?;
            if !analysis
                && (size(sizes, "N") == 0
                    || size(sizes, "KMN") < size(sizes, "N")
                    || size(sizes, "N") >= 1usize << size(sizes, "M"))
            {
                return Err(
                    "N must be >= 1 and < 2^M; KMN must be >= N for the outliner layout".into(),
                );
            }
            Ok(())
        }),
        make_inputs,
        analyses: &[common::Analysis::Completeness, common::Analysis::Zk],
    }
}
