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
//!   - Native side runs the SR1CS-direct entry points (`Pari::
//!     keygen_from_sr1cs` / `Pari::prove_from_sr1cs`) so both sides see
//!     the EXACT same matrices, witness, and instance_len. No
//!     `ConstraintSynthesizer`, no R1CS→SR1CS adapter (which would
//!     expand the constraint count and add aux variables), no extra
//!     instance vars beyond the n_pub the zippel side declares.
//!   - Zippel side feeds `z_a_evals`, `z_b_evals`, `w_a_evals`,
//!     `w_b_evals` precomputed (no sparse MVM inside the protocol);
//!     native side runs those 4 sparse MVMs INSIDE its prove timer. This
//!     is the one asymmetry left — at K = 2^20 with row_density = 3 the
//!     MVM cost is O(K) = ~1M field multiplies per matrix, small next
//!     to the 4 IFFTs + quotient division + 5 MSMs that dominate.
//!   - Native verifier uses the upstream O(n) Lagrange shortcut; the
//!     zippel verifier interpolates `x_a_evals` over K (O(K log K)).
//!     This is the real zippel-side limitation, not a measurement
//!     artifact. With instance_len = n_pub (= 1 by default) the native
//!     shortcut is O(1) and dominated by the 4-element MSM + 3-pair
//!     final check.

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
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
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

    // Cached SRS artifact. Deterministic given `(test_rng seed, inst,
    // m_log, n_pub, num_vars)`. The bench reuses the same Instance
    // across the full thread sweep, so caching by `m_log` alone is safe
    // as long as inst_gen stays seeded with `ark_std::test_rng()` and
    // (n_pub, k_vars) stay fixed.
    #[derive(CanonicalSerialize, CanonicalDeserialize)]
    struct PariSrs {
        sigma_w: Vec<G1>,
        sigma_q: Vec<G1>,
        sigma_a: Vec<G1>,
        sigma_b: Vec<G1>,
        sigma_q_prime: Vec<G1>,
        alpha_g: G1,
        beta_g: G1,
        g_g1: G1,
        delta2_h: G2,
        tau_h: G2,
        h_g2: G2,
        omegas: Vec<F>,
        k_inv: F,
        v_k_coeffs: Vec<F>,
    }

    impl PariSrs {
        fn build(m_log: usize, n_pub: usize, num_vars: usize, inst: &super::Instance<F>) -> Self {
            let k = 1usize << m_log;
            let mut rng = ark_std::test_rng();
            let alpha = F::rand(&mut rng);
            let beta = F::rand(&mut rng);
            let delta2 = F::rand(&mut rng);
            let tau = F::rand(&mut rng);
            let g_g1: G1 = G1::rand(&mut rng);
            let h_g2: G2 = G2::rand(&mut rng);

            let domain = GeneralEvaluationDomain::<F>::new(k).expect("K-domain");

            let mut a_polys: Vec<DensePolynomial<F>> = Vec::with_capacity(num_vars);
            let mut b_polys: Vec<DensePolynomial<F>> = Vec::with_capacity(num_vars);
            for j in 0..num_vars {
                let mut a_col = vec![F::zero(); k];
                let mut b_col = vec![F::zero(); k];
                for i in 0..k {
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
            let sigma_w: Vec<G1> = (n_pub..num_vars)
                .map(|i| {
                    let scalar = (alpha * a_polys[i].evaluate(&tau)
                        + beta * b_polys[i].evaluate(&tau))
                        * delta2_inv;
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
            let sigma_q: Vec<G1> = tau_powers
                .iter()
                .map(|t| g_g1 * (*t * delta2_inv))
                .collect();
            let sigma_a: Vec<G1> = tau_powers.iter().map(|t| g_g1 * (alpha * *t)).collect();
            let sigma_b: Vec<G1> = tau_powers.iter().map(|t| g_g1 * (beta * *t)).collect();
            let sigma_q_prime: Vec<G1> = tau_powers.iter().map(|t| g_g1 * *t).collect();

            let alpha_g: G1 = g_g1 * alpha;
            let beta_g: G1 = g_g1 * beta;
            let delta2_h: G2 = h_g2 * delta2;
            let tau_h: G2 = h_g2 * tau;

            let mut v_k_coeffs = vec![F::zero(); k + 1];
            v_k_coeffs[0] = -F::one();
            v_k_coeffs[k] = F::one();

            let omega = domain.group_gen();
            let omegas: Vec<F> = (0..n_pub)
                .map(|i| omega.pow([(k - n_pub + i) as u64]))
                .collect();
            let k_inv = F::from(k as u64).inverse().unwrap();

            PariSrs {
                sigma_w,
                sigma_q,
                sigma_a,
                sigma_b,
                sigma_q_prime,
                alpha_g,
                beta_g,
                g_g1,
                delta2_h,
                tau_h,
                h_g2,
                omegas,
                k_inv,
                v_k_coeffs,
            }
        }
    }

    pub struct Setup {
        handler: ZippelHandler<C>,
        m_log: usize,
        k: usize,
        n_pub: usize,
        kmn: usize, // = num_vars - n_pub
        num_vars: usize,
        srs: PariSrs,
    }

    impl Setup {
        pub fn new(m_log: usize, n_pub: usize, inst: &super::Instance<F>) -> Self {
            let k = 1usize << m_log;
            let num_vars = inst.num_vars;
            let kmn = num_vars - n_pub;
            let args = ZippelArgs::new(PathBuf::from("examples/pari/pari.zippel"));
            let mut handler: ZippelHandler<C> = ZippelHandler::new(args);
            let mut sizes = Ctx::new();
            sizes.insert(&Tid::new("M"), &m_log);
            sizes.insert(&Tid::new("N"), &n_pub);
            sizes.insert(&Tid::new("KMN"), &kmn);
            handler.compile(&sizes);

            let srs = crate::cache::load_or_build_canonical("pari_zippel_srs", m_log, || {
                PariSrs::build(m_log, n_pub, num_vars, inst)
            });

            Setup {
                handler,
                m_log,
                k,
                n_pub,
                kmn,
                num_vars,
                srs,
            }
        }

        pub fn time_protocol(&mut self, inst: &super::Instance<F>) -> Timing {
            assert_eq!(inst.k, self.k);
            assert_eq!(inst.instance_len, self.n_pub);
            assert_eq!(inst.num_vars, self.num_vars);

            // Cheap per-call data derived from inst (element-wise
            // subtractions + slice clones). The expensive SRS bits live
            // in `self.srs`, built once in `Setup::new`.
            let x_vec: Vec<F> = inst.z[..self.n_pub].to_vec();
            let w_vec: Vec<F> = inst.z[self.n_pub..].to_vec();
            let w_a_evals: Vec<F> = (0..self.k)
                .map(|i| inst.z_a_evals[i] - inst.x_a_evals[i])
                .collect();
            let w_b_evals: Vec<F> = (0..self.k)
                .map(|i| inst.z_b_evals[i] - inst.x_b_evals[i])
                .collect();

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
                    Value::VecScalar(self.srs.omegas.clone()),
                ),
                (
                    Vid("sigma_w".to_string()),
                    Value::VecG1(self.srs.sigma_w.clone()),
                ),
                (
                    Vid("sigma_q".to_string()),
                    Value::VecG1(self.srs.sigma_q.clone()),
                ),
                (
                    Vid("sigma_a".to_string()),
                    Value::VecG1(self.srs.sigma_a.clone()),
                ),
                (
                    Vid("sigma_b".to_string()),
                    Value::VecG1(self.srs.sigma_b.clone()),
                ),
                (
                    Vid("sigma_q_prime".to_string()),
                    Value::VecG1(self.srs.sigma_q_prime.clone()),
                ),
                (Vid("alpha_g".to_string()), Value::G1(self.srs.alpha_g)),
                (Vid("beta_g".to_string()), Value::G1(self.srs.beta_g)),
                (Vid("g_g1".to_string()), Value::G1(self.srs.g_g1)),
                (Vid("delta2_h".to_string()), Value::G2(self.srs.delta2_h)),
                (Vid("tau_h".to_string()), Value::G2(self.srs.tau_h)),
                (Vid("h_g2".to_string()), Value::G2(self.srs.h_g2)),
                (
                    Vid("v_k_coeffs".to_string()),
                    Value::VecScalar(self.srs.v_k_coeffs.clone()),
                ),
                (Vid("f_one".to_string()), Value::Scalar(F::one())),
                (Vid("k_inv".to_string()), Value::Scalar(self.srs.k_inv)),
            ]);

            let public_inputs = Ctx::<Vid, Value<C>>::from_iter([
                (Vid("x".to_string()), Value::VecScalar(x_vec)),
                (
                    Vid("omegas".to_string()),
                    Value::VecScalar(self.srs.omegas.clone()),
                ),
                (Vid("alpha_g".to_string()), Value::G1(self.srs.alpha_g)),
                (Vid("beta_g".to_string()), Value::G1(self.srs.beta_g)),
                (Vid("g_g1".to_string()), Value::G1(self.srs.g_g1)),
                (Vid("delta2_h".to_string()), Value::G2(self.srs.delta2_h)),
                (Vid("tau_h".to_string()), Value::G2(self.srs.tau_h)),
                (Vid("h_g2".to_string()), Value::G2(self.srs.h_g2)),
                (Vid("f_one".to_string()), Value::Scalar(F::one())),
                (Vid("k_inv".to_string()), Value::Scalar(self.srs.k_inv)),
            ]);

            // --- Time prove (mean of PROVER_SAMPLES samples) ---
            let prover_scheduled = self.handler.default_schedule_prover();
            let mut prove_sum = std::time::Duration::ZERO;
            let mut last_proof = None;
            for _ in 0..*crate::PROVER_SAMPLES {
                let sched = prover_scheduled.clone();
                let inputs_c = inputs.clone();
                let t = Instant::now();
                let proof = self
                    .handler
                    .run_prover(sched, inputs_c)
                    .expect("zippel pari prover failed");
                prove_sum += t.elapsed();
                last_proof = Some(proof);
            }
            let prove = prove_sum / *crate::PROVER_SAMPLES;
            let proof = last_proof.expect("PROVER_SAMPLES > 0");

            // --- Time verify (mean of VERIFY_SAMPLES samples) ---
            self.handler.set_public_inputs(public_inputs);
            let verifier_scheduled = self.handler.default_schedule_verifier();
            let mut verify_sum = std::time::Duration::ZERO;
            let mut last_result = None;
            for _ in 0..crate::VERIFY_SAMPLES {
                let sched = verifier_scheduled.clone();
                let proof_c = proof.clone();
                let t = Instant::now();
                let verifier_result = self
                    .handler
                    .run_verifier(sched, proof_c)
                    .expect("zippel pari verifier failed");
                verify_sum += t.elapsed();
                last_result = Some(verifier_result);
            }
            let verify = verify_sum / crate::VERIFY_SAMPLES;
            let result = check_verification(last_result.expect("VERIFY_SAMPLES > 0"));
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
    //! Native PARI baseline: the upstream `pari` crate, vendored in-tree
    //! at `benchmarks/src/pari_upstream/`. Driven via the SR1CS-direct
    //! entry points (`Pari::keygen_from_sr1cs` / `Pari::prove_from_sr1cs`)
    //! so both sides prove the EXACT same SR1CS statement built by
    //! `super::inst_gen::build_random` — same K, same matrices, same z,
    //! same instance_len. No `ConstraintSynthesizer`, no `Sr1csAdapter`
    //! R1CS→SR1CS expansion, and (since instance_len = n_pub instead of
    //! K+1) the verifier's O(n) Lagrange shortcut runs over the small
    //! instance dimension just like the zippel verifier does.
    use super::{Instance, Timing};
    use crate::pari_upstream::{
        Pari,
        data_structures::{ProvingKey, VerifyingKey},
    };
    use ark_bls12_381::Bls12_381;
    use ark_ec::pairing::Pairing;
    use ark_serialize::CanonicalSerialize;
    use ark_std::rand::{SeedableRng, rngs::StdRng};
    use std::time::Instant;

    type E = Bls12_381;
    type F = <E as Pairing>::ScalarField;

    pub struct Setup {
        instance_assignment: Vec<F>,
        witness_assignment: Vec<F>,
        public_inputs: Vec<F>,
        a_mat: Vec<Vec<(F, usize)>>,
        b_mat: Vec<Vec<(F, usize)>>,
        pk: ProvingKey<E>,
        vk: VerifyingKey<E>,
    }

    impl Setup {
        pub fn new(inst: &Instance<F>) -> Self {
            let instance_assignment = inst.z[..inst.instance_len].to_vec();
            let witness_assignment = inst.z[inst.instance_len..].to_vec();
            // Verifier's public input is `instance_assignment[1..]` (the
            // constant-1 at position 0 is implicit) — matches upstream.
            let public_inputs = instance_assignment[1..].to_vec();
            // Cache (pk, vk) — these depend only on the matrices and the
            // seeded rng. log_size = log_2(k).
            let log_size = inst.k.trailing_zeros() as usize;
            let (pk, vk) = crate::cache::load_or_build_canonical::<(
                crate::pari_upstream::data_structures::ProvingKey<E>,
                crate::pari_upstream::data_structures::VerifyingKey<E>,
            )>(
                "pari_keys",
                log_size,
                || {
                    let mut rng = StdRng::seed_from_u64(0xBEEF_u64);
                    Pari::<E>::keygen_from_sr1cs(
                        &inst.a_mat,
                        &inst.b_mat,
                        inst.instance_len,
                        inst.num_vars,
                        &mut rng,
                    )
                },
            );
            Setup {
                instance_assignment,
                witness_assignment,
                public_inputs,
                a_mat: inst.a_mat.clone(),
                b_mat: inst.b_mat.clone(),
                pk,
                vk,
            }
        }

        pub fn time_protocol(&self, _inst: &Instance<F>) -> Timing {
            let mut prove_sum = std::time::Duration::ZERO;
            let mut last_proof = None;
            for _ in 0..*crate::PROVER_SAMPLES {
                let t = Instant::now();
                let proof = Pari::<E>::prove_from_sr1cs(
                    &self.a_mat,
                    &self.b_mat,
                    &self.instance_assignment,
                    &self.witness_assignment,
                    &self.pk,
                )
                .expect("Pari::prove_from_sr1cs failed");
                prove_sum += t.elapsed();
                last_proof = Some(proof);
            }
            let prove = prove_sum / *crate::PROVER_SAMPLES;
            let proof = last_proof.expect("PROVER_SAMPLES > 0");

            let mut verify_sum = std::time::Duration::ZERO;
            let mut last_ok = false;
            for _ in 0..crate::VERIFY_SAMPLES {
                let t = Instant::now();
                let ok = Pari::<E>::verify(&proof, &self.vk, &self.public_inputs);
                verify_sum += t.elapsed();
                last_ok = ok;
            }
            let verify = verify_sum / crate::VERIFY_SAMPLES;
            assert!(last_ok, "upstream PARI verification FAILED");

            Timing { prove, verify }
        }

        pub fn proof_size(&self, _inst: &Instance<F>) -> usize {
            let proof = Pari::<E>::prove_from_sr1cs(
                &self.a_mat,
                &self.b_mat,
                &self.instance_assignment,
                &self.witness_assignment,
                &self.pk,
            )
            .expect("Pari::prove_from_sr1cs failed");
            proof.compressed_size()
        }
    }
}
