//! KZH-2 multilinear PCS comparison: zippel-compiled `examples/kzh/kzh.zippel`
//! vs. irondict's KZH-k at k = 2 (ported to arkworks 0.6 in
//! `src/kzh_upstream/`), both on BLS12-381.
//!
//! Statement on both sides: the prover knows a multilinear f with 2^N
//! evaluations; it commits and proves f(x0, y0) = z0 at a public point.
//!
//! Parity decisions:
//!   - One SRS, polynomial, point and value per size, built by the native
//!     port's own setup in `shared` and fed to both sides.
//!   - "prove" is commit + open on both sides (as for pst13). Native open
//!     also returns f(x0, y0); zippel takes z0 as an instance input.
//!   - Dimensions follow irondict: NX = ceil(N/2) row variables (bound by
//!     x0 = point[0..NX]), NY = floor(N/2) column variables.
//!   - Both verifiers do one multi-pairing of size 1 + 2^NX, two MSMs
//!     (<eq(x0), D> and <T2, H2>) and one 2^NY-term evaluation of T2 at y0.
//!
//! `log_size` = N.

use crate::Timing;

pub mod shared {
    use crate::kzh_upstream::UniversalParams;
    use ark_bls12_381::{Bls12_381, Fr};
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
    use ark_std::UniformRand;
    use ark_std::rand::{SeedableRng, rngs::StdRng};

    #[derive(CanonicalSerialize, CanonicalDeserialize)]
    pub struct Shared {
        pub n: usize,
        pub srs: UniversalParams<Bls12_381>,
        pub f: Vec<Fr>,
        pub point: Vec<Fr>,
        pub value: Fr,
    }

    /// Seeded, cached as `artifacts/kzh_shared_log<n>.bin`.
    ///
    /// # Panics
    /// Panics if `n < 2`, or if reading/writing the cached artifact fails.
    pub fn build(n: usize) -> Shared {
        assert!(n >= 2, "KZH-2 needs at least 2 variables");
        crate::cache::load_or_build_canonical("kzh_shared", n, || {
            let mut rng = StdRng::seed_from_u64(0x4b5a48 ^ n as u64);
            let srs = UniversalParams::<Bls12_381>::gen_srs_for_testing(&mut rng, 2, n);
            let f: Vec<Fr> = (0..1usize << n).map(|_| Fr::rand(&mut rng)).collect();
            let point: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
            let (pp, _) = srs.trim();
            let (_, value) = crate::kzh_upstream::open(&pp, &f, &point);
            Shared {
                n,
                srs,
                f,
                point,
                value,
            }
        })
    }
}

pub mod zippel_side {
    use super::*;
    use ark_ec::AffineRepr;
    use backend::{ArkBls12_381, PreparedG2Vec, Value};
    use lang::id::{Tid, Vid};
    use share::Ctx;
    use std::path::PathBuf;
    use zippel::{Inputs, ZippelArgs, ZippelHandler, check_verification};

    pub struct Setup {
        handler: ZippelHandler<ArkBls12_381>,
        inputs: Inputs<ArkBls12_381>,
        compile_time: Vec<std::time::Duration>,
    }

    impl Setup {
        pub fn new(sh: &shared::Shared) -> Self {
            let (nx, ny) = (sh.srs.dimensions[0], sh.srs.dimensions[1]);

            let (handler, compile_time) = crate::sample_compile(|| {
                let mut handler: ZippelHandler<ArkBls12_381> =
                    ZippelHandler::new(ZippelArgs::new(PathBuf::from("examples/kzh/kzh.zippel")));
                let mut sizes = Ctx::new();
                sizes.insert(&Tid::new("NX"), &nx);
                sizes.insert(&Tid::new("NY"), &ny);
                handler.compile_for_execution(&sizes);
                handler
            });

            let inputs = Inputs::from_iter(
                [
                    ("f", Value::vec_scalar(sh.f.clone())),
                    ("x0", Value::vec_scalar(sh.point[..nx].to_vec())),
                    ("y0", Value::vec_scalar(sh.point[nx..].to_vec())),
                    ("z0", Value::Scalar(sh.value)),
                    ("h1", Value::vec_g1_affine(sh.srs.h_tensors[0].clone())),
                    ("h2", Value::vec_g1_affine(sh.srs.h_tensors[1].clone())),
                    // Prepared once here, as native's verifier key stores V1.
                    (
                        "v1",
                        Value::VecG2Prepared(PreparedG2Vec::new(sh.srs.v_mat[0].clone())),
                    ),
                    ("v_gen", Value::G2(sh.srs.v.into_group())),
                    ("g_gen", Value::G1(sh.srs.g.into_group())),
                ]
                .into_iter()
                .map(|(k, v)| (Vid(k.to_string()), v)),
            );

            Setup {
                handler,
                inputs,
                compile_time,
            }
        }

        pub fn compile_time(&self) -> Vec<std::time::Duration> {
            self.compile_time.clone()
        }

        /// (prover graph node count, verifier graph node count).
        pub fn graph_sizes(&self) -> (usize, usize) {
            (
                self.handler.prover_graph().node_count(),
                self.handler.verifier_graph().node_count(),
            )
        }

        /// # Panics
        /// Panics if either graph fails to execute or the verifier rejects.
        pub fn time_protocol(&mut self) -> Timing {
            let (prove, prove_peak, proof) = crate::sample(|| {
                self.handler
                    .run_prover(&self.inputs)
                    .expect("run_prover failed")
            });
            let (verify, verify_peak, result) = crate::sample(|| {
                self.handler
                    .run_verifier(&proof, &self.inputs)
                    .expect("run_verifier failed")
            });
            assert!(
                check_verification(&result),
                "zippel KZH-2 verification FAILED"
            );
            Timing {
                prove,
                verify,
                prove_peak,
                verify_peak,
            }
        }
    }
}

pub mod native_side {
    use super::*;
    use crate::kzh_upstream::{self as kzh, ProverParam, VerifierParam};
    use ark_bls12_381::{Bls12_381, Fr};

    pub struct Setup {
        pp: ProverParam<Bls12_381>,
        vp: VerifierParam<Bls12_381>,
        f: Vec<Fr>,
        point: Vec<Fr>,
        value: Fr,
    }

    impl Setup {
        pub fn new(sh: &shared::Shared) -> Self {
            let (pp, vp) = sh.srs.trim();
            Setup {
                pp,
                vp,
                f: sh.f.clone(),
                point: sh.point.clone(),
                value: sh.value,
            }
        }

        /// # Panics
        /// Panics if the native verifier rejects the honest proof.
        pub fn time_protocol(&self) -> Timing {
            let (prove, prove_peak, (com, proof, value)) = crate::sample(|| {
                let com = kzh::commit(&self.pp, &self.f);
                let (proof, value) = kzh::open(&self.pp, &self.f, &self.point);
                (com, proof, value)
            });
            assert_eq!(value, self.value);
            let (verify, verify_peak, ok) =
                crate::sample(|| kzh::verify(&self.vp, &com, &self.point, &self.value, &proof));
            assert!(ok, "native KZH-2 verification FAILED");
            Timing {
                prove,
                verify,
                prove_peak,
                verify_peak,
            }
        }
    }
}
