//! PARI comparison: zippel-compiled PARI vs. the native PARI port of
//! alireza-shirzad/garuda-pari (`pari_native`). Both sides prove the
//! same Square R1CS statement on BLS12-381:
//!
//! ```text
//! (A · z) ∘ (A · z) = B · z   on the constraint domain K
//! ```
//!
//! Statement-building: we construct a random K-constraint SR1CS
//! instance with the upstream "instance outliner" matrix layout —
//! the last n constraints are the e_i rows that make the native
//! verifier's O(n) Lagrange-shortcut valid. Both sides see the same
//! matrices and the same witness.
//!
//! Parity decisions:
//!   - Zippel side feeds `z_a_evals`, `z_b_evals`, `x_a_evals`,
//!     `x_b_evals` as inputs (no sparse MVM inside the protocol — same
//!     simplification the user requested when implementing PARI in
//!     `examples/pari`). The native side reaches the same vectors
//!     internally; both pay the same sparse-MVM cost outside the
//!     "prove" timer.
//!   - Native verifier uses the upstream O(n) Lagrange shortcut; the
//!     zippel verifier interpolates `x_a_evals` over K (O(K log K)).
//!     This is the real zippel-side limitation, not a measurement
//!     artifact.

use crate::Timing;

pub const DEFAULT_M_LOG: usize = 4; // K = 2^M_LOG = 16
pub const DEFAULT_N_PUB: usize = 1;
pub const DEFAULT_K_VARS: usize = 8;

// ---------------------------------------------------------------------------
// Shared instance generation
// ---------------------------------------------------------------------------

/// SR1CS instance shared by both sides.
pub struct Instance<F> {
    pub k: usize,            // num_constraints = 2^M_LOG
    pub instance_len: usize, // n (includes the constant-1 at position 0)
    pub num_vars: usize,     // k_vars = n + witness + n_aux
    /// Variable assignment `z = (x ∥ w ∥ aux)`, length `num_vars`.
    pub z: Vec<F>,
    pub a_mat: Vec<Vec<(F, usize)>>,
    pub b_mat: Vec<Vec<(F, usize)>>,
    /// Precomputed evaluation vectors A·z, B·z, A·(x∥0), B·(x∥0) on K.
    pub z_a_evals: Vec<F>,
    pub z_b_evals: Vec<F>,
    pub x_a_evals: Vec<F>,
    pub x_b_evals: Vec<F>,
}

pub mod inst_gen {
    use super::Instance;
    use ark_ff::{Field, UniformRand, Zero};
    use rand::Rng;

    /// Build a satisfying SR1CS instance in the upstream "instance
    /// outliner" layout, so the native verifier's Lagrange shortcut is
    /// valid:
    ///
    /// - z = [1, x[1..n], w[0..m], aux[0..n]] where aux[i] = z[i]^2.
    ///   Total `num_vars = 2n + m` for `m` "real" witness variables.
    /// - A has zero columns at the instance positions on constraints
    ///   `[0, K-n)` (so x̂_A vanishes on those domain points), and
    ///   `A[K-n+i] = e_i` on constraints `[K-n, K)`.
    /// - B has zero columns at the instance positions everywhere, and
    ///   `B[K-n+i][n+m+i] = 1` so that (Bz)[K-n+i] = aux[i] = z[i]^2.
    /// - Original constraints (j ∈ 0..K-n): random A row over witness
    ///   columns; B row places `(Az)[j]^2 / z[c]` in a chosen witness
    ///   column c, so (Bz)[j] = (Az)[j]^2.
    pub fn build_random<F: Field, R: Rng>(
        m_log: usize,
        n_pub: usize,
        m_witness: usize,
        rng: &mut R,
    ) -> Instance<F> {
        assert!(n_pub >= 1, "need n_pub ≥ 1 (the constant-1 row)");
        let k = 1usize << m_log;
        assert!(
            k >= n_pub + 1,
            "need K ≥ n_pub + 1 (room for K-n original constraints)"
        );

        let num_vars = 2 * n_pub + m_witness;
        let original_k = k - n_pub;

        // --- Build z: 1, public, real witness, aux (= squares of x) ---
        let mut z = vec![F::zero(); num_vars];
        z[0] = F::one();
        for i in 1..n_pub {
            z[i] = nonzero(rng);
        }
        for j in n_pub..n_pub + m_witness {
            z[j] = nonzero(rng);
        }
        for i in 0..n_pub {
            z[n_pub + m_witness + i] = z[i] * z[i];
        }

        // --- Build matrices ---
        let mut a_mat: Vec<Vec<(F, usize)>> = vec![Vec::new(); k];
        let mut b_mat: Vec<Vec<(F, usize)>> = vec![Vec::new(); k];

        // Original constraints: random A over witness columns, B derived.
        let witness_cols: Vec<usize> = (n_pub..num_vars).collect();
        for j in 0..original_k {
            // Pick a few random witness columns to populate A's row.
            let row_density = 3.min(witness_cols.len());
            let mut a_row_acc = F::zero();
            for c in &witness_cols[..row_density] {
                let coeff = F::rand(rng);
                a_mat[j].push((coeff, *c));
                a_row_acc += coeff * z[*c];
            }
            let target = a_row_acc * a_row_acc;
            // Place `target / z[c]` in column c so (Bz)[j] = target.
            let c = witness_cols[j % witness_cols.len()];
            b_mat[j].push((target * z[c].inverse().unwrap(), c));
        }

        // Instance-outlining constraints: A[K-n+i] = e_i, B[K-n+i] = e_{n+m+i}.
        for i in 0..n_pub {
            a_mat[original_k + i].push((F::one(), i));
            b_mat[original_k + i].push((F::one(), n_pub + m_witness + i));
        }

        // Sanity: (Az)^2 = Bz at every constraint.
        let mut z_a_evals = vec![F::zero(); k];
        let mut z_b_evals = vec![F::zero(); k];
        for j in 0..k {
            z_a_evals[j] = eval_row(&a_mat[j], &z);
            z_b_evals[j] = eval_row(&b_mat[j], &z);
            debug_assert_eq!(z_a_evals[j] * z_a_evals[j], z_b_evals[j]);
        }

        // x_padded = (x ∥ 0)
        let mut x_padded = vec![F::zero(); num_vars];
        x_padded[..n_pub].copy_from_slice(&z[..n_pub]);
        let mut x_a_evals = vec![F::zero(); k];
        let mut x_b_evals = vec![F::zero(); k];
        for j in 0..k {
            x_a_evals[j] = eval_row(&a_mat[j], &x_padded);
            x_b_evals[j] = eval_row(&b_mat[j], &x_padded);
        }

        Instance {
            k,
            instance_len: n_pub,
            num_vars,
            z,
            a_mat,
            b_mat,
            z_a_evals,
            z_b_evals,
            x_a_evals,
            x_b_evals,
        }
    }

    fn nonzero<F: Field, R: Rng>(rng: &mut R) -> F {
        loop {
            let v = F::rand(rng);
            if !v.is_zero() {
                return v;
            }
        }
    }

    fn eval_row<F: Field>(row: &[(F, usize)], z: &[F]) -> F {
        let mut acc = F::zero();
        for &(c, j) in row {
            acc += c * z[j];
        }
        acc
    }
}

// ---------------------------------------------------------------------------
// Zippel side: refactor of examples/pari/main.rs into the bench harness.
// ---------------------------------------------------------------------------

pub mod zippel_side {
    use super::*;
    use ark_ec::CurveGroup;
    use ark_ff::{Field, One, UniformRand, Zero};
    use ark_poly::{
        DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain, Polynomial,
        univariate::DensePolynomial,
    };
    use backend::{ArkBls12_381, ArkConfig, Value};
    use lang::id::{Tid, Vid};
    use share::Ctx;
    use std::path::PathBuf;
    use std::time::Instant;
    use zippel::{ZippelArgs, ZippelHandler, check_verification};

    type C = ArkBls12_381;
    type F = <C as ArkConfig>::F;
    type G1 = <C as ArkConfig>::G1;
    type G2 = <C as ArkConfig>::G2;

    pub struct Setup {
        handler: ZippelHandler<C>,
        m_log: usize,
        k: usize,
        n_pub: usize,
        kmn: usize, // = num_vars - n_pub
        num_vars: usize,
    }

    impl Setup {
        pub fn new(m_log: usize, n_pub: usize, num_vars: usize) -> Self {
            let k = 1usize << m_log;
            let kmn = num_vars - n_pub;
            let args = ZippelArgs::new(PathBuf::from("examples/pari/pari.zippel"));
            let mut handler: ZippelHandler<C> = ZippelHandler::new(args);
            let mut sizes = Ctx::new();
            sizes.insert(&Tid::new("M"), &m_log);
            sizes.insert(&Tid::new("N"), &n_pub);
            sizes.insert(&Tid::new("KMN"), &kmn);
            handler.compile(&sizes);
            Setup {
                handler,
                m_log,
                k,
                n_pub,
                kmn,
                num_vars,
            }
        }

        pub fn time_protocol(&mut self, inst: &super::Instance<F>) -> Timing {
            assert_eq!(inst.k, self.k);
            assert_eq!(inst.instance_len, self.n_pub);
            assert_eq!(inst.num_vars, self.num_vars);

            let mut rng = ark_std::test_rng();

            // --- PARI Generator: SRS construction (matches examples/pari/main.rs) ---
            let alpha = F::rand(&mut rng);
            let beta = F::rand(&mut rng);
            let delta2 = F::rand(&mut rng);
            let tau = F::rand(&mut rng);
            let g_g1: G1 = G1::rand(&mut rng);
            let h_g2: G2 = G2::rand(&mut rng);

            let domain = GeneralEvaluationDomain::<F>::new(self.k).expect("K-domain");

            // Interpolate columns of A and B over K to get a_i(X), b_i(X).
            let mut a_polys: Vec<DensePolynomial<F>> = Vec::with_capacity(self.num_vars);
            let mut b_polys: Vec<DensePolynomial<F>> = Vec::with_capacity(self.num_vars);
            for j in 0..self.num_vars {
                let mut a_col = vec![F::zero(); self.k];
                let mut b_col = vec![F::zero(); self.k];
                for i in 0..self.k {
                    for &(c, idx) in &inst.a_mat[i] {
                        if idx == j {
                            a_col[i] += c;
                        }
                    }
                    for &(c, idx) in &inst.b_mat[i] {
                        if idx == j {
                            b_col[i] += c;
                        }
                    }
                }
                a_polys.push(DensePolynomial::from_coefficients_vec(domain.ifft(&a_col)));
                b_polys.push(DensePolynomial::from_coefficients_vec(domain.ifft(&b_col)));
            }

            let delta2_inv = delta2.inverse().expect("delta2 != 0");
            let sigma_w_vec: Vec<G1> = (self.n_pub..self.num_vars)
                .map(|i| {
                    let scalar = (alpha * a_polys[i].evaluate(&tau)
                        + beta * b_polys[i].evaluate(&tau))
                        * delta2_inv;
                    g_g1 * scalar
                })
                .collect();

            let tau_powers: Vec<F> = {
                let mut acc = F::one();
                (0..self.k)
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

            let mut v_k_coeffs_vec = vec![F::zero(); self.k + 1];
            v_k_coeffs_vec[0] = -F::one();
            v_k_coeffs_vec[self.k] = F::one();

            // Lagrange-shortcut inputs: only N scalars for public input,
            // plus N precomputed omegas[i] = ω^{K-N+i}, plus k_inv.
            let omega = domain.group_gen();
            let x_vec: Vec<F> = inst.z[..self.n_pub].to_vec();
            let omegas_vec: Vec<F> = (0..self.n_pub)
                .map(|i| omega.pow([(self.k - self.n_pub + i) as u64]))
                .collect();
            let k_inv = F::from(self.k as u64).inverse().unwrap();

            // Prover-side precomputed w_*_evals = z_*_evals − x_*_evals on K.
            let w_a_evals: Vec<F> = (0..self.k)
                .map(|i| inst.z_a_evals[i] - inst.x_a_evals[i])
                .collect();
            let w_b_evals: Vec<F> = (0..self.k)
                .map(|i| inst.z_b_evals[i] - inst.x_b_evals[i])
                .collect();

            let w_vec: Vec<F> = inst.z[self.n_pub..].to_vec();

            // --- Pack into the zippel inputs Ctx ---
            let inputs = Ctx::<Vid, Value<C>>::from_iter([
                (
                    Vid("z_a_evals".to_string()),
                    Value::VecScalar(inst.z_a_evals.clone()),
                ),
                (
                    Vid("z_b_evals".to_string()),
                    Value::VecScalar(inst.z_b_evals.clone()),
                ),
                (Vid("w_a_evals".to_string()), Value::VecScalar(w_a_evals)),
                (Vid("w_b_evals".to_string()), Value::VecScalar(w_b_evals)),
                (Vid("w".to_string()), Value::VecScalar(w_vec)),
                (Vid("x".to_string()), Value::VecScalar(x_vec.clone())),
                (
                    Vid("omegas".to_string()),
                    Value::VecScalar(omegas_vec.clone()),
                ),
                (Vid("sigma_w".to_string()), Value::VecG1(sigma_w_vec)),
                (Vid("sigma_q".to_string()), Value::VecG1(sigma_q_vec)),
                (Vid("sigma_a".to_string()), Value::VecG1(sigma_a_vec)),
                (Vid("sigma_b".to_string()), Value::VecG1(sigma_b_vec)),
                (
                    Vid("sigma_q_prime".to_string()),
                    Value::VecG1(sigma_q_prime_vec),
                ),
                (Vid("alpha_g".to_string()), Value::G1(alpha_g_val)),
                (Vid("beta_g".to_string()), Value::G1(beta_g_val)),
                (Vid("g_g1".to_string()), Value::G1(g_g1)),
                (Vid("delta2_h".to_string()), Value::G2(delta2_h_val)),
                (Vid("tau_h".to_string()), Value::G2(tau_h_val)),
                (Vid("h_g2".to_string()), Value::G2(h_g2)),
                (
                    Vid("v_k_coeffs".to_string()),
                    Value::VecScalar(v_k_coeffs_vec),
                ),
                (Vid("f_one".to_string()), Value::Scalar(F::one())),
                (Vid("k_inv".to_string()), Value::Scalar(k_inv)),
            ]);

            // Public inputs (verifier side). With sigma_*, v_k_coeffs
            // marked `private` in the .zippel, the verifier only sees
            // the O(N)-sized Lagrange-shortcut data + the constant-size
            // verifier keys.
            let public_inputs = Ctx::<Vid, Value<C>>::from_iter([
                (Vid("x".to_string()), Value::VecScalar(x_vec)),
                (Vid("omegas".to_string()), Value::VecScalar(omegas_vec)),
                (Vid("alpha_g".to_string()), Value::G1(alpha_g_val)),
                (Vid("beta_g".to_string()), Value::G1(beta_g_val)),
                (Vid("g_g1".to_string()), Value::G1(g_g1)),
                (Vid("delta2_h".to_string()), Value::G2(delta2_h_val)),
                (Vid("tau_h".to_string()), Value::G2(tau_h_val)),
                (Vid("h_g2".to_string()), Value::G2(h_g2)),
                (Vid("f_one".to_string()), Value::Scalar(F::one())),
                (Vid("k_inv".to_string()), Value::Scalar(k_inv)),
            ]);

            // --- Time prove ---
            let prover_scheduled = self.handler.default_schedule_prover();
            let t = Instant::now();
            let proof = self
                .handler
                .run_prover(prover_scheduled, inputs)
                .expect("zippel pari prover failed");
            let prove = t.elapsed();

            // --- Time verify ---
            self.handler.set_public_inputs(public_inputs);
            let verifier_scheduled = self.handler.default_schedule_verifier();
            let t = Instant::now();
            let verifier_result = self
                .handler
                .run_verifier(verifier_scheduled, proof)
                .expect("zippel pari verifier failed");
            let verify = t.elapsed();
            let result = check_verification(verifier_result);
            assert!(result.passed, "zippel PARI verification FAILED");

            Timing { prove, verify }
        }

        pub fn m_log(&self) -> usize {
            self.m_log
        }
        pub fn k(&self) -> usize {
            self.k
        }
    }
}

// ---------------------------------------------------------------------------
// Native side: wraps `pari_native` keygen/prove/verify.
// ---------------------------------------------------------------------------

pub mod native_side {
    use super::*;
    use crate::pari_native::{Proof, ProvingKey, VerifyingKey, keygen, prove, verify};
    use ark_bls12_381::Bls12_381;
    use ark_ec::pairing::Pairing;
    use ark_serialize::CanonicalSerialize;
    use std::time::Instant;

    type E = Bls12_381;
    type F = <E as Pairing>::ScalarField;

    pub struct Setup {
        pk: ProvingKey<E>,
        vk: VerifyingKey<E>,
    }

    impl Setup {
        pub fn new(inst: &super::Instance<F>) -> Self {
            let mut rng = ark_std::test_rng();
            let (pk, vk) = keygen::<E, _>(
                &inst.a_mat,
                &inst.b_mat,
                inst.num_vars,
                inst.instance_len,
                &mut rng,
            );
            Setup { pk, vk }
        }

        pub fn time_protocol(&self, inst: &super::Instance<F>) -> Timing {
            let instance_assignment = &inst.z[..inst.instance_len];
            let witness_assignment = &inst.z[inst.instance_len..];

            let t = Instant::now();
            let proof: Proof<E> = prove(
                &self.pk,
                &inst.a_mat,
                &inst.b_mat,
                instance_assignment,
                witness_assignment,
            );
            let prove_t = t.elapsed();

            // Verifier receives public_input as everything except the
            // constant 1 at z[0] — matching upstream's stripping convention.
            let public_input: Vec<F> = instance_assignment[1..].to_vec();

            let t = Instant::now();
            let ok = verify(&proof, &self.vk, &public_input);
            let verify_t = t.elapsed();
            assert!(ok, "native PARI verification FAILED");

            Timing {
                prove: prove_t,
                verify: verify_t,
            }
        }

        pub fn proof_size(&self, inst: &super::Instance<F>) -> usize {
            let proof: Proof<E> = prove(
                &self.pk,
                &inst.a_mat,
                &inst.b_mat,
                &inst.z[..inst.instance_len],
                &inst.z[inst.instance_len..],
            );
            proof.compressed_size()
        }
    }
}
