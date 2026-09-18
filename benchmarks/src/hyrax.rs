//! Hyrax comparison: zippel-compiled Hyrax polynomial commitment vs. the
//! vendored `ark-poly-commit` Hyrax implementation — both on BLS12-381 G1.
//!
//! Statement on both sides: an `n`-variate multilinear polynomial `p` is
//! viewed as a `2^L x 2^M` matrix (`L + M = n`); the prover Pedersen-commits
//! each row, then proves `p(z_row, z_col) = y` by a sigma protocol on the
//! row-combined commitment. Prove covers commit + open, verify covers check.
//!
//! Sizes are bound via `sizes.insert("L", l)` / `sizes.insert("M", m)` at
//! compile time, so `n` must be even and in `2..=20`.

use crate::Timing;

/// Default number of variables of the committed multilinear polynomial;
/// split evenly into `L` row bits and `M` column bits.
pub const DEFAULT_N: usize = 10;

/// Zippel half: compiles `examples/hyrax/hyrax.zippel` and times its
/// generated prover and verifier.
pub mod zippel_side {
    use super::Timing;
    use ark_bls12_381::{Fr, G1Projective};
    use ark_ec::CurveGroup;
    use ark_ff::{One, Zero};
    use ark_std::UniformRand;
    use ark_std::rand::SeedableRng;
    use backend::{ArkBls12_381, Value};
    use lang::id::{Tid, Vid};
    use share::Ctx;
    use std::path::PathBuf;
    use std::time::Instant;
    use zippel::{ZippelArgs, ZippelHandler, check_verification};

    /// A compiled Hyrax instance together with the fixed, seeded inputs it is
    /// timed on.
    ///
    /// Inputs (polynomial, evaluation point, claimed value, Pedersen bases)
    /// are generated once in `new` from an `n`-derived seed so repeated
    /// `time_protocol` calls measure the same instance.
    pub struct Setup {
        handler: ZippelHandler<ArkBls12_381>,
        inputs: Ctx<Vid, Value<ArkBls12_381>>,
        compile_time: std::time::Duration,
    }

    impl Setup {
        /// Generates the seeded instance for an `n`-variate polynomial and
        /// compiles the protocol with `L = n/2`, `M = n - n/2`.
        ///
        /// The claimed evaluation `y` is computed directly as
        /// `L_vec^T * matrix * R_vec` over the equality-polynomial weights, so
        /// the proof is always honest.
        ///
        /// # Panics
        /// Panics unless `n` is even and in `2..=20` (the `eq_weights` cap),
        /// or if compiling the `.zippel` source fails.
        pub fn new(n: usize) -> Self {
            assert!(
                (2..=20).contains(&n) && n.is_multiple_of(2),
                "n must be an even number in 2..=20 (eq_weights cap)"
            );
            let l = n / 2;
            let m = n - l;
            let nrows = 1usize << l;
            let ncols = 1usize << m;
            let ntot = nrows * ncols;

            let zippel_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("examples/hyrax/hyrax.zippel");
            let zippel_path = if zippel_path.exists() {
                zippel_path
            } else {
                PathBuf::from("examples/hyrax/hyrax.zippel")
            };

            let mut seed_bytes = [0u8; 32];
            seed_bytes[..8].copy_from_slice(&(0xFEEDFACE_u64 ^ n as u64).to_le_bytes());
            let mut rng = ark_std::rand::rngs::StdRng::from_seed(seed_bytes);

            let p: Vec<Fr> = (0..ntot).map(|_| Fr::rand(&mut rng)).collect();
            let z_row: Vec<Fr> = (0..l).map(|_| Fr::rand(&mut rng)).collect();
            let z_col: Vec<Fr> = (0..m).map(|_| Fr::rand(&mut rng)).collect();

            let l_vec = eq_evals_lsb(&z_row);
            let r_vec = eq_evals_lsb(&z_col);
            let mut y = Fr::zero();
            for i in 0..nrows {
                for j in 0..ncols {
                    y += l_vec[i] * r_vec[j] * p[i * ncols + j];
                }
            }

            let g_proj: Vec<G1Projective> =
                (0..ncols).map(|_| G1Projective::rand(&mut rng)).collect();
            let g_vec_aff = G1Projective::normalize_batch(&g_proj);
            let g_base = G1Projective::rand(&mut rng);
            let h_base = G1Projective::rand(&mut rng);

            let inputs = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
                (Vid("p".to_string()), Value::VecScalar(p)),
                (Vid("z_row".to_string()), Value::VecScalar(z_row)),
                (Vid("z_col".to_string()), Value::VecScalar(z_col)),
                (Vid("y".to_string()), Value::Scalar(y)),
                (Vid("g_vec".to_string()), Value::VecG1Affine(g_vec_aff)),
                (Vid("g_base".to_string()), Value::G1(g_base)),
                (Vid("h_base".to_string()), Value::G1(h_base)),
            ]);

            // Time the zippel compiler: source → executable graph.
            // Includes parsing, type-checking, and graph construction.
            // Excludes runtime scheduling (which is per-call cheap
            // graph→TDag work the runtime does) and excludes the actual
            // prove/verify execution.
            let compile_start = Instant::now();
            let args = ZippelArgs::new(zippel_path);
            let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
            let mut sizes = Ctx::new();
            sizes.insert(&Tid::new("L"), &l);
            sizes.insert(&Tid::new("M"), &m);
            handler.compile(&sizes);
            let compile_time = compile_start.elapsed();

            Setup {
                handler,
                inputs,
                compile_time,
            }
        }

        /// Wall-time spent parsing, type checking, and building the prover and
        /// verifier graphs. Excludes scheduling and execution.
        pub fn compile_time(&self) -> std::time::Duration {
            self.compile_time
        }

        /// Runs the compiled prover and verifier on the stored instance and
        /// returns their mean wall-times.
        ///
        /// # Panics
        /// Panics if the prover or verifier graph fails to execute, or if the
        /// verifier rejects the honestly generated proof.
        pub fn time_protocol(&mut self) -> Timing {
            let mut prove_sum = std::time::Duration::ZERO;
            let mut last_proof = None;
            for _ in 0..*crate::PROVER_SAMPLES {
                let inputs_c = self.inputs.clone();
                let t = Instant::now();
                let proof = self
                    .handler
                    .run_prover(&inputs_c)
                    .expect("zippel hyrax prover failed");
                prove_sum += t.elapsed();
                last_proof = Some(proof);
            }
            let prove = prove_sum / *crate::PROVER_SAMPLES;
            let proof = last_proof.expect("PROVER_SAMPLES > 0");
            let mut verify_sum = std::time::Duration::ZERO;
            let mut last_result = None;
            for _ in 0..crate::VERIFY_SAMPLES {
                let proof_c = proof.clone();
                let t = Instant::now();
                let verifier_result = self
                    .handler
                    .run_verifier(&proof_c, &self.inputs)
                    .expect("zippel hyrax verifier failed");
                verify_sum += t.elapsed();
                last_result = Some(verifier_result);
            }
            let verify = verify_sum / crate::VERIFY_SAMPLES;
            let result = check_verification(&last_result.expect("VERIFY_SAMPLES > 0"));
            assert!(result, "zippel hyrax verification FAILED");
            Timing { prove, verify }
        }

        /// Node counts of the projected prover and verifier graphs, in that
        /// order — the size proxy reported alongside the timings.
        pub fn graph_sizes(&self) -> (usize, usize) {
            (
                self.handler.prover_graph().node_count(),
                self.handler.verifier_graph().node_count(),
            )
        }
    }

    fn eq_evals_lsb(x: &[Fr]) -> Vec<Fr> {
        let n = x.len();
        let one = Fr::one();
        let mut out = vec![one; 1 << n];
        let mut size = 1;
        for &xi in x {
            let one_m_xi = one - xi;
            for i in (0..size).rev() {
                let v = out[i];
                out[size + i] = v * xi;
                out[i] = v * one_m_xi;
            }
            size *= 2;
        }
        out
    }
}

/// Native Hyrax baseline. Vendored from `ark-poly-commit-0.6.0::hyrax`
/// (see `crate::hyrax_upstream`) with the matrix-vector multiplication
/// in `open` rewritten to use flat row-major storage and a SAXPY
/// accumulation — upstream's `Matrix<F>` stores rows as separately
/// allocated `Vec<F>`s and `Matrix::row_mul` allocates a fresh 16KB
/// column-gather Vec per output element (8MB churn at log_size=18) plus
/// nested `par_iter` overhead. Crypto primitives and Fiat-Shamir
/// transcript bytes are unchanged. Timed regions still match the zippel
/// side: prove = commit + open (row Pedersens + σ-protocol),
/// verify = check.
pub mod native_side {
    use super::Timing;
    use ark_bls12_381::{Fr, G1Affine};
    use ark_crypto_primitives::sponge::{
        CryptographicSponge,
        poseidon::{PoseidonConfig, PoseidonSponge},
    };
    use ark_ff::{PrimeField, UniformRand};
    use ark_poly::{DenseMultilinearExtension, MultilinearExtension, Polynomial};
    use std::time::Instant;

    use crate::hyrax_upstream::{self, CommitterKey, VerifierKey};

    /// Vendored-Hyrax keys plus the fixed polynomial, evaluation point, and
    /// claimed value that `time_protocol` is measured on.
    pub struct Setup {
        _num_vars: usize,
        ck: CommitterKey,
        vk: VerifierKey,
        poly: DenseMultilinearExtension<Fr>,
        point: Vec<Fr>,
        value: Fr,
    }

    impl Setup {
        /// Loads or builds the Hyrax universal parameters for `n` variables
        /// from the artifact cache, trims them into a committer/verifier key
        /// pair, and samples the polynomial, point, and value.
        ///
        /// All of this stays out of the timed region; the caller runs it inside
        /// the setup thread pool.
        ///
        /// # Panics
        /// Panics if the cached parameters cannot be read or written.
        pub fn new(n: usize) -> Self {
            // Cache UniversalParams. Byte format matches upstream's
            // derived CanonicalSerialize (same field order: com_key, h),
            // so caches written by either implementation interoperate.
            let pp = crate::cache::load_or_build_canonical::<
                ark_poly_commit::hyrax::HyraxUniversalParams<G1Affine>,
            >("hyrax_universal_params", n, || {
                let mut rng = ark_std::test_rng();
                hyrax_upstream::setup(n, &mut rng)
            });
            let (ck, vk) = hyrax_upstream::trim(&pp);

            // Poly/point/value generation runs in `setup_pool` (called
            // here, not in time_protocol). At log_size=20 the rand poly
            // is 2^20 field elements and `evaluate` is O(2^n) — keeping
            // this in the bench pool single-threaded at threads=1 was
            // wasting ~60ms per sweep iteration.
            let mut rng = ark_std::test_rng();
            let poly = DenseMultilinearExtension::<Fr>::rand(n, &mut rng);
            let point: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
            let value = poly.evaluate(&point);

            Setup {
                _num_vars: n,
                ck,
                vk,
                poly,
                point,
                value,
            }
        }

        /// Times the vendored `commit` + `open` as the prover and `check` as
        /// the verifier, using a fresh Poseidon sponge per run so each sample
        /// starts from the same transcript state.
        ///
        /// # Panics
        /// Panics if the vendored verifier rejects the honestly generated
        /// proof.
        pub fn time_protocol(&self) -> Timing {
            let point = &self.point;
            let _ = self.value;

            let mut prove_sum = std::time::Duration::ZERO;
            let mut last_outputs = None;
            for _ in 0..*crate::PROVER_SAMPLES {
                let t = Instant::now();
                let (com, state) = hyrax_upstream::commit(&self.ck, &self.poly);
                let mut sponge = test_sponge::<Fr>();
                let proof = hyrax_upstream::open(&self.ck, &com, point, &mut sponge, &state);
                prove_sum += t.elapsed();
                last_outputs = Some((com, proof));
            }
            let prove = prove_sum / *crate::PROVER_SAMPLES;
            let (com, proof) = last_outputs.expect("PROVER_SAMPLES > 0");

            let mut verify_sum = std::time::Duration::ZERO;
            let mut last_ok = false;
            for _ in 0..crate::VERIFY_SAMPLES {
                let mut sponge_v = test_sponge::<Fr>();
                let t = Instant::now();
                let ok = hyrax_upstream::check(&self.vk, &com, point, &proof, &mut sponge_v);
                verify_sum += t.elapsed();
                last_ok = ok;
            }
            let verify = verify_sum / crate::VERIFY_SAMPLES;
            assert!(last_ok, "vendored Hyrax verification FAILED");

            Timing { prove, verify }
        }
    }

    // Verbatim from ark-poly-commit-0.5.0 bench-templates/src/lib.rs::test_sponge.
    fn test_sponge<F: PrimeField>() -> PoseidonSponge<F> {
        let full_rounds = 8;
        let partial_rounds = 31;
        let alpha = 17;
        let mds = vec![
            vec![F::one(), F::zero(), F::one()],
            vec![F::one(), F::one(), F::zero()],
            vec![F::zero(), F::one(), F::one()],
        ];
        let mut v = Vec::new();
        let mut ark_rng = ark_std::test_rng();
        for _ in 0..(full_rounds + partial_rounds) {
            let mut res = Vec::new();
            for _ in 0..3 {
                res.push(F::rand(&mut ark_rng));
            }
            v.push(res);
        }
        let config = PoseidonConfig::new(full_rounds, partial_rounds, alpha, mds, v, 2, 1);
        PoseidonSponge::new(&config)
    }
}
