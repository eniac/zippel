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

/// Zippel half: compiles `examples/hyrax_pcs/hyrax_pcs.zippel` and times its
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
    use std::collections::HashMap;
    use std::path::PathBuf;
    use zippel::{
        CompileOptions, CompiledProtocol, CompiledProver, CompiledVerifier, ParsedModule,
    };

    /// A compiled Hyrax instance together with the fixed, seeded inputs it is
    /// timed on.
    ///
    /// Inputs (polynomial, evaluation point, claimed value, Pedersen bases)
    /// are generated once in `new` from an `n`-derived seed so repeated
    /// `time_protocol` calls measure the same instance.
    pub struct Setup {
        prover: CompiledProver<ArkBls12_381>,
        verifier: CompiledVerifier<ArkBls12_381>,
        inputs: HashMap<Vid, Value<ArkBls12_381>>,
        compile_time: Vec<std::time::Duration>,
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
                .join("examples/hyrax_pcs/hyrax_pcs.zippel");
            let zippel_path = if zippel_path.exists() {
                zippel_path
            } else {
                PathBuf::from("examples/hyrax_pcs/hyrax_pcs.zippel")
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

            let inputs = crate::harness_inputs([
                (Vid("p".to_string()), Value::vec_scalar(p)),
                (Vid("z_row".to_string()), Value::vec_scalar(z_row)),
                (Vid("z_col".to_string()), Value::vec_scalar(z_col)),
                (Vid("y".to_string()), Value::Scalar(y)),
                (Vid("g_vec".to_string()), Value::vec_g1_affine(g_vec_aff)),
                (Vid("g_base".to_string()), Value::g1(g_base)),
                (Vid("h_base".to_string()), Value::g1(h_base)),
            ]);

            // Time the zippel compiler: source → executable graph.
            // Includes parsing, type-checking, and graph construction.
            // Excludes runtime scheduling (which is per-call cheap
            // graph→TDag work the runtime does) and excludes the actual
            // prove/verify execution.
            let ((prover, verifier), compile_time) = crate::sample_compile(|| {
                let module = ParsedModule::load(zippel_path.clone()).expect("parse protocol");
                let mut sizes = Ctx::new();
                sizes.insert(&Tid::new("L"), &l);
                sizes.insert(&Tid::new("M"), &m);
                let protocol: CompiledProtocol<ArkBls12_381> = module
                    .compile(&sizes, CompileOptions::default())
                    .expect("compile protocol");
                (
                    protocol.project_prover(),
                    protocol.project_verifier().expect("project verifier"),
                )
            });

            Setup {
                prover,
                verifier,
                inputs,
                compile_time,
            }
        }

        /// Wall-time spent parsing, type checking, and building the prover and
        /// verifier graphs. Excludes scheduling and execution.
        pub fn compile_time(&self) -> Vec<std::time::Duration> {
            self.compile_time.clone()
        }

        /// Runs the compiled prover and verifier on the stored instance and
        /// returns their mean wall-times.
        ///
        /// # Panics
        /// Panics if the prover or verifier graph fails to execute, or if the
        /// verifier rejects the honestly generated proof.
        pub fn time_protocol(&mut self) -> Timing {
            let (prove, prove_peak, proof) =
                crate::sample_zippel_prover(&self.prover, &self.inputs);
            let (verify, verify_peak, passed) =
                crate::sample_zippel_verifier(&self.verifier, &proof, &self.inputs);
            assert!(passed, "zippel hyrax verification FAILED");
            Timing {
                prove,
                verify,
                prove_peak,
                verify_peak,
            }
        }

        /// Node counts of the projected prover and verifier graphs, in that
        /// order — the size proxy reported alongside the timings.
        pub fn graph_sizes(&self) -> (usize, usize) {
            (
                self.prover.graph().node_count(),
                self.verifier.graph().node_count(),
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
/// (see `crate::upstream::hyrax`) with the matrix-vector multiplication
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

    use crate::upstream::hyrax::{self, CommitterKey, VerifierKey};

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
                hyrax::setup(n, &mut rng)
            });
            let (ck, vk) = hyrax::trim(&pp);

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

            let (prove, prove_peak, (com, proof)) = crate::sample(|| {
                let (com, state) = hyrax::commit(&self.ck, &self.poly);
                let mut sponge = test_sponge::<Fr>();
                let proof = hyrax::open(&self.ck, &com, point, &mut sponge, &state);
                (com, proof)
            });
            let (verify, verify_peak, passed) = crate::sample(|| {
                let mut sponge_v = test_sponge::<Fr>();
                hyrax::check(&self.vk, &com, point, &proof, &mut sponge_v)
            });
            assert!(passed, "vendored Hyrax verification FAILED");

            Timing {
                prove,
                verify,
                prove_peak,
                verify_peak,
            }
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

// ---------------------------------------------------------------------------
// Cross-verification: at the same challenges, each verifier accepts the other's
// proof. The native takes its sponge, so it is given the challenge sequence.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod cross_tests {
    use crate::cross::{Challenges, Direction};
    use crate::upstream::hyrax::{self as hyrax, Proof};
    use ark_bls12_381::{Fr, G1Affine};
    use ark_ec::CurveGroup;
    use ark_ff::{One, UniformRand};
    use ark_poly::{DenseMultilinearExtension, MultilinearExtension, Polynomial};
    use ark_poly_commit::hyrax::HyraxCommitment;
    use backend::{ArkBls12_381, Value};

    type V = Value<ArkBls12_381>;

    fn g1(v: &V) -> G1Affine {
        match v {
            Value::G1(g) => g.into_affine(),
            Value::G1Affine(g) => **g,
            _ => panic!("expected G1, got {v}"),
        }
    }
    fn g1s(v: &V) -> Vec<G1Affine> {
        match v {
            Value::Vec(vs) => vs.iter().map(g1).collect(),
            Value::VecG1(gs) => gs.iter().map(|g| g.into_affine()).collect(),
            Value::VecG1Affine(gs) => gs.to_vec(),
            _ => panic!("expected G1s, got {v}"),
        }
    }
    fn scalar(v: &V) -> Fr {
        match v {
            Value::Scalar(f) => *f,
            _ => panic!("expected a scalar, got {v}"),
        }
    }
    fn frs(v: &V) -> Vec<Fr> {
        match v {
            Value::VecScalar(f) => f.to_vec(),
            _ => panic!("expected scalars, got {v}"),
        }
    }

    /// The native commitment and proof as Zippel's messages: the row commitments,
    /// tau, delta and beta, then z, z_delta and z_beta.
    fn as_zippel(com: &hyrax::Commitment, p: &Proof) -> Vec<V> {
        vec![
            Value::vec_g1_affine(com.row_coms.clone()),
            Value::g1_affine(p.com_eval),
            Value::g1_affine(p.com_d),
            Value::g1_affine(p.com_b),
            Value::vec_scalar(p.z.clone()),
            Value::Scalar(p.z_d),
            Value::Scalar(p.z_b),
        ]
    }

    fn as_native(m: &[V]) -> (hyrax::Commitment, Proof) {
        assert_eq!(m.len(), 7, "Zippel's message count");
        let com = HyraxCommitment {
            row_coms: g1s(&m[0]),
        };
        let proof = Proof {
            com_eval: g1(&m[1]),
            com_d: g1(&m[2]),
            com_b: g1(&m[3]),
            z: frs(&m[4]),
            z_d: scalar(&m[5]),
            z_b: scalar(&m[6]),
        };
        (com, proof)
    }

    #[test]
    fn native_prove_then_zippel_verify() {
        cross_verify(Direction::NativeToZippel);
    }

    #[test]
    fn zippel_prove_then_native_verify() {
        cross_verify(Direction::ZippelToNative);
    }

    fn cross_verify(direction: Direction) {
        let mut rng = ark_std::test_rng();
        for n in [2usize, 4, 6] {
            let half = n / 2;
            let dim = 1 << half;
            let pp = hyrax::setup(n, &mut rng);
            let poly = DenseMultilinearExtension::<Fr>::rand(n, &mut rng);
            let point: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
            // Native row `r`, column `c` holds evaluation `c·dim + r`: rows are the
            // low variables, columns the high ones.
            let evals = poly.to_evaluations();
            let p: Vec<Fr> = (0..dim * dim)
                .map(|i| evals[(i % dim) * dim + i / dim])
                .collect();

            let (prover, verifier) =
                crate::cross::compile::<ArkBls12_381>("hyrax_pcs", &[("L", half), ("M", half)]);
            let inputs = crate::harness_inputs([
                ("p", Value::vec_scalar(p)),
                ("z_row", Value::vec_scalar(point[..half].to_vec())),
                ("z_col", Value::vec_scalar(point[half..].to_vec())),
                ("y", Value::Scalar(poly.evaluate(&point))),
                ("g_vec", Value::vec_g1_affine(pp.com_key[..dim].to_vec())),
                ("g_base", Value::g1_affine(pp.com_key[0])),
                ("h_base", Value::g1_affine(pp.h)),
            ]);

            match direction {
                Direction::NativeToZippel => {
                    let (com, state) = hyrax::commit(&pp, &poly);
                    let native = hyrax::open(&pp, &com, &point, &mut Challenges::default(), &state);
                    let native = as_zippel(&com, &native);
                    assert!(
                        verifier
                            .verify_with(
                                native.clone(),
                                crate::lend(&inputs),
                                &mut Challenges::default()
                            )
                            .unwrap(),
                        "n = {n}: Zippel rejects the native proof"
                    );
                    let mut wrong = native;
                    wrong[6] = Value::Scalar(scalar(&wrong[6]) + Fr::one());
                    assert!(
                        !verifier
                            .verify_with(wrong, crate::lend(&inputs), &mut Challenges::default())
                            .unwrap(),
                        "n = {n}: Zippel accepts a wrong z_beta"
                    );
                }
                Direction::ZippelToNative => {
                    let ours = prover
                        .prove_with(crate::lend(&inputs), &mut Challenges::default())
                        .unwrap();
                    let (com, proof) = as_native(&ours);
                    assert!(
                        hyrax::check(&pp, &com, &point, &proof, &mut Challenges::default()),
                        "n = {n}: the native verifier rejects Zippel's proof"
                    );
                }
            }
        }
    }
}
