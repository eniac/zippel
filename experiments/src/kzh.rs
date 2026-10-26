//! KZH-2 multilinear PCS comparison: zippel-compiled `examples/kzh/kzh.zippel`
//! vs. irondict's KZH-k at k = 2 (ported to arkworks 0.6 in
//! `src/upstream/kzh/`), both on BLS12-381.
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
    use crate::upstream::kzh::UniversalParams;
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
            let (_, value) = crate::upstream::kzh::open(&pp, &f, &point);
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
    use backend::{ArkBls12_381, Value};
    use lang::id::{Tid, Vid};
    use share::Ctx;
    use std::collections::HashMap;
    use std::path::PathBuf;
    use zippel::{
        CompileOptions, CompiledProtocol, CompiledProver, CompiledVerifier, ParsedModule,
    };

    pub struct Setup {
        prover: CompiledProver<ArkBls12_381>,
        verifier: CompiledVerifier<ArkBls12_381>,
        inputs: HashMap<Vid, Value<ArkBls12_381>>,
        compile_time: Vec<std::time::Duration>,
    }

    impl Setup {
        pub fn new(sh: &shared::Shared) -> Self {
            let (nx, ny) = (sh.srs.dimensions[0], sh.srs.dimensions[1]);

            let ((prover, verifier), compile_time) = crate::sample_compile(|| {
                let module = ParsedModule::load(
                    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                        .join("..")
                        .join("examples/kzh/kzh.zippel"),
                )
                .expect("parse protocol");
                let mut sizes = Ctx::new();
                sizes.insert(&Tid::new("NX"), &nx);
                sizes.insert(&Tid::new("NY"), &ny);
                let protocol: CompiledProtocol<ArkBls12_381> = module
                    .compile(&sizes, CompileOptions::default())
                    .expect("compile protocol");
                (
                    protocol.project_prover(),
                    protocol.project_verifier().expect("project verifier"),
                )
            });

            let inputs = crate::harness_inputs(
                [
                    ("f", Value::vec_scalar(sh.f.clone())),
                    ("x0", Value::vec_scalar(sh.point[..nx].to_vec())),
                    ("y0", Value::vec_scalar(sh.point[nx..].to_vec())),
                    ("z0", Value::Scalar(sh.value)),
                    ("h1", Value::vec_g1_affine(sh.srs.h_tensors[0].clone())),
                    ("h2", Value::vec_g1_affine(sh.srs.h_tensors[1].clone())),
                    // A verifier key: a pairing backend prepares it once here, as
                    // native's verifier key stores V1.
                    ("v1", Value::vec_g2_key(sh.srs.v_mat[0].clone())),
                    ("v_gen", Value::g2(sh.srs.v.into_group())),
                    ("g_gen", Value::g1(sh.srs.g.into_group())),
                ]
                .into_iter()
                .map(|(k, v)| (Vid(k.to_string()), v)),
            );

            Setup {
                prover,
                verifier,
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
                self.prover.graph().node_count(),
                self.verifier.graph().node_count(),
            )
        }

        /// # Panics
        /// Panics if either graph fails to execute or the verifier rejects.
        pub fn time_protocol(&mut self) -> Timing {
            let (prove, prove_peak, proof) =
                crate::sample_zippel_prover(&self.prover, &self.inputs);
            let (verify, verify_peak, passed) =
                crate::sample_zippel_verifier(&self.verifier, &proof, &self.inputs);
            assert!(passed, "zippel KZH-2 verification FAILED");
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
    use crate::upstream::kzh::{self as kzh, ProverParam, VerifierParam};
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
            let (verify, verify_peak, passed) =
                crate::sample(|| kzh::verify(&self.vp, &com, &self.point, &self.value, &proof));
            assert!(passed, "native KZH-2 verification FAILED");
            Timing {
                prove,
                verify,
                prove_peak,
                verify_peak,
            }
        }
    }
}

#[cfg(test)]
mod cross_tests {
    use super::shared;
    use crate::cross::Direction;
    use crate::upstream::kzh::{self as kzh, OpeningProof};
    use ark_bls12_381::{Bls12_381, Fr, G1Affine};
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::One;
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
            Value::VecG1(gs) => gs.iter().map(|g| g.into_affine()).collect(),
            Value::VecG1Affine(gs) => gs.to_vec(),
            _ => panic!("expected G1 vector, got {v}"),
        }
    }

    fn frs(v: &V) -> Vec<Fr> {
        match v {
            Value::VecScalar(fs) => fs.to_vec(),
            _ => panic!("expected scalars, got {v}"),
        }
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
        // Include both square and rectangular evaluation tables.
        for n in [2usize, 3, 4, 5, 6] {
            let sh = shared::build(n);
            let (nx, ny) = (sh.srs.dimensions[0], sh.srs.dimensions[1]);
            let (pp, vp) = sh.srs.trim();
            let (prover, verifier) =
                crate::cross::compile::<ArkBls12_381>("kzh", &[("NX", nx), ("NY", ny)]);
            let inputs = crate::harness_inputs([
                ("f", Value::vec_scalar(sh.f.clone())),
                ("x0", Value::vec_scalar(sh.point[..nx].to_vec())),
                ("y0", Value::vec_scalar(sh.point[nx..].to_vec())),
                ("z0", Value::Scalar(sh.value)),
                ("h1", Value::vec_g1_affine(sh.srs.h_tensors[0].clone())),
                ("h2", Value::vec_g1_affine(sh.srs.h_tensors[1].clone())),
                ("v1", Value::vec_g2_affine(sh.srs.v_mat[0].clone())),
                ("v_gen", Value::g2(sh.srs.v.into_group())),
                ("g_gen", Value::g1(sh.srs.g.into_group())),
            ]);

            match direction {
                Direction::NativeToZippel => {
                    let com = kzh::commit(&pp, &sh.f);
                    let (proof, value) = kzh::open(&pp, &sh.f, &sh.point);
                    assert_eq!(value, sh.value);
                    assert!(kzh::verify(&vp, &com, &sh.point, &value, &proof));
                    let native = vec![
                        Value::g1_affine(com),
                        Value::vec_g1_affine(proof.d[0].clone()),
                        Value::vec_scalar(proof.f),
                    ];
                    assert!(
                        verifier
                            .verify(native.clone(), crate::lend(&inputs))
                            .unwrap(),
                        "n = {n}: Zippel rejects the native proof"
                    );
                    let mut wrong = native;
                    let mut f = frs(&wrong[2]);
                    f[0] += Fr::one();
                    wrong[2] = Value::vec_scalar(f);
                    assert!(
                        !verifier.verify(wrong, crate::lend(&inputs)).unwrap(),
                        "n = {n}: Zippel accepts a wrong partial evaluation"
                    );
                }
                Direction::ZippelToNative => {
                    let ours = prover.prove(crate::lend(&inputs)).unwrap();
                    assert_eq!(ours.len(), 3, "n = {n}: Zippel's message count");
                    let com = g1(&ours[0]);
                    let mut proof = OpeningProof::<Bls12_381> {
                        d: vec![g1s(&ours[1])],
                        f: frs(&ours[2]),
                    };
                    assert!(
                        kzh::verify(&vp, &com, &sh.point, &sh.value, &proof),
                        "n = {n}: the native verifier rejects Zippel's proof"
                    );
                    proof.f[0] += Fr::one();
                    assert!(
                        !kzh::verify(&vp, &com, &sh.point, &sh.value, &proof),
                        "n = {n}: the native verifier accepts a wrong partial evaluation"
                    );
                }
            }
        }
    }
}
