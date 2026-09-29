//! Dory PCS comparison: zippel-compiled `examples/dory_pcs/dory_pcs.zippel`
//! vs. a16z's `dory-pcs` transparent mode (ported to arkworks 0.6 in
//! `src/dory_upstream/`), both on BLS12-381.
//!
//! Statement on both sides: the prover knows a multilinear f with 2^(2K)
//! coefficients (a 2^K × 2^K matrix); it commits and proves f(point) = y.
//!
//! Parity decisions:
//!   - One setup (Γ1, Γ2, H1, H2 and the verifier's χ/Δ pairings),
//!     polynomial, point and value per size, built by the native port in
//!     `shared` and fed to both sides.
//!   - "prove" is commit + evaluation proof on both sides.
//!   - Native keeps the setup vectors prepared for pairing (the `cache`
//!     feature jolt enables); zippel gets Γ2 as a prepared input.
//!   - Fiat-Shamir: native hashes with Blake2b; zippel uses its own sponge and
//!     also absorbs the commitment, which upstream leaves out of the transcript.
//!
//! `log_size` = 2K (number of variables).

use crate::Timing;

pub mod shared {
    use crate::dory_upstream::{self as dory, ProverSetup, VerifierSetup};
    use ark_bls12_381::Fr;
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
    use ark_std::UniformRand;
    use ark_std::rand::{SeedableRng, rngs::StdRng};

    #[derive(CanonicalSerialize, CanonicalDeserialize)]
    pub struct Shared {
        pub k: usize,
        pub setup: ProverSetup,
        pub vsetup: VerifierSetup,
        pub coeffs: Vec<Fr>,
        pub point: Vec<Fr>,
        pub y: Fr,
    }

    /// Seeded, cached as `artifacts/dory_shared_log<n>.bin`.
    ///
    /// # Panics
    /// Panics if `n` is odd or zero, or if the cached artifact cannot be read
    /// or written.
    pub fn build(n: usize) -> Shared {
        assert!(
            n >= 2 && n.is_multiple_of(2),
            "Dory benchmark runs square matrices: n = 2K"
        );
        crate::cache::load_or_build_canonical("dory_shared", n, || {
            let k = n / 2;
            let mut rng = StdRng::seed_from_u64(0xD0_4A ^ n as u64);
            let setup = ProverSetup::new(&mut rng, n);
            let vsetup = setup.to_verifier_setup();
            let coeffs: Vec<Fr> = (0..1usize << n).map(|_| Fr::rand(&mut rng)).collect();
            let point: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
            let y = dory::evaluate(&coeffs, &point);
            Shared {
                k,
                setup,
                vsetup,
                coeffs,
                point,
                y,
            }
        })
    }
}

pub mod zippel_side {
    use super::*;
    use ark_ec::CurveGroup;
    use backend::{ArkBls12_381, PreparedG2Vec, Value};
    use lang::id::{Tid, Vid};
    use share::Ctx;
    use std::path::PathBuf;
    use std::time::Instant;
    use zippel::{ZippelArgs, ZippelHandler, check_verification};

    pub struct Setup {
        handler: ZippelHandler<ArkBls12_381>,
        inputs: Ctx<Vid, Value<ArkBls12_381>>,
        compile_time: std::time::Duration,
    }

    impl Setup {
        pub fn new(sh: &shared::Shared) -> Self {
            Self::with_proto(sh, PathBuf::from("examples/dory_pcs/dory_pcs.zippel"))
        }

        /// Same inputs, a different proto source (the cross-check test runs a
        /// copy that echoes the challenges).
        pub fn with_proto(sh: &shared::Shared, proto: PathBuf) -> Self {
            let k = sh.k;
            let compile_start = Instant::now();
            let mut handler: ZippelHandler<ArkBls12_381> =
                ZippelHandler::new(ZippelArgs::new(proto));
            let mut sizes = Ctx::new();
            sizes.insert(&Tid::new("K"), &k);
            handler.compile(&sizes);
            let compile_time = compile_start.elapsed();

            let (s, v) = (&sh.setup, &sh.vsetup);
            let nv = 1usize << k;
            let inputs = Ctx::from_iter(
                [
                    ("m", Value::VecScalar(sh.coeffs.clone())),
                    // upstream point = columns (sigma) then rows (nu)
                    ("col_pt", Value::VecScalar(sh.point[..k].to_vec())),
                    ("row_pt", Value::VecScalar(sh.point[k..].to_vec())),
                    ("y", Value::Scalar(sh.y)),
                    (
                        "g1_vec",
                        Value::VecG1Affine(ark_bls12_381::G1Projective::normalize_batch(
                            &s.g1_vec[..nv],
                        )),
                    ),
                    // Prepared once here, as native's prepared-setup cache holds Γ2.
                    (
                        "g2_vec",
                        Value::VecG2Prepared(PreparedG2Vec::new(
                            ark_bls12_381::G2Projective::normalize_batch(&s.g2_vec[..nv]),
                        )),
                    ),
                    ("g1_0", Value::G1(v.g1_0)),
                    ("g2_0", Value::G2(v.g2_0)),
                    ("h1", Value::G1(v.h1)),
                    ("h2", Value::G2(v.h2)),
                    ("ht", Value::GT(v.ht)),
                    ("chi", Value::VecGT(v.chi[..=k].to_vec())),
                    ("delta_1l", Value::VecGT(v.delta_1l[..=k].to_vec())),
                    ("delta_1r", Value::VecGT(v.delta_1r[..=k].to_vec())),
                    ("delta_2r", Value::VecGT(v.delta_2r[..=k].to_vec())),
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

        /// One prover run; the proof is the list of prover messages in order.
        ///
        /// # Panics
        /// Panics if the prover graph fails to execute.
        pub fn prove_once(&mut self) -> Vec<Value<ArkBls12_381>> {
            self.handler
                .run_prover(&self.inputs)
                .expect("run_prover failed")
        }

        pub fn compile_time(&self) -> std::time::Duration {
            self.compile_time
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
            let (prove, prove_peak, proof) = crate::sample(*crate::PROVER_SAMPLES, || {
                self.handler
                    .run_prover(&self.inputs)
                    .expect("run_prover failed")
            });
            let (verify, verify_peak, result) = crate::sample(crate::VERIFY_SAMPLES, || {
                self.handler
                    .run_verifier(&proof, &self.inputs)
                    .expect("run_verifier failed")
            });
            assert!(
                check_verification(&result),
                "zippel Dory verification FAILED"
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
    use crate::dory_upstream::{self as dory, Blake2bTranscript, PreparedCache};

    pub struct Setup<'a> {
        sh: &'a shared::Shared,
        cache: PreparedCache,
    }

    impl<'a> Setup<'a> {
        pub fn new(sh: &'a shared::Shared) -> Self {
            Setup {
                sh,
                cache: PreparedCache::new(&sh.setup),
            }
        }

        /// # Panics
        /// Panics if the native verifier rejects the honest proof.
        pub fn time_protocol(&self) -> Timing {
            let (sh, k) = (self.sh, self.sh.k);
            let (prove, prove_peak, (com, proof)) = crate::sample(*crate::PROVER_SAMPLES, || {
                let (com, rows) = dory::commit(&sh.coeffs, k, k, &sh.setup, &self.cache);
                let mut transcript = Blake2bTranscript::new(b"dory-bench");
                let proof = dory::create_evaluation_proof(
                    &sh.coeffs,
                    &sh.point,
                    rows,
                    k,
                    k,
                    &sh.setup,
                    &self.cache,
                    &mut transcript,
                );
                (com, proof)
            });
            let (verify, verify_peak, ok) = crate::sample(crate::VERIFY_SAMPLES, || {
                let mut transcript = Blake2bTranscript::new(b"dory-bench");
                dory::verify_evaluation_proof(
                    com,
                    sh.y,
                    &sh.point,
                    &proof,
                    &sh.vsetup,
                    &mut transcript,
                )
            });
            assert!(ok, "native Dory verification FAILED");
            Timing {
                prove,
                verify,
                prove_peak,
                verify_peak,
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Cross-check: the two provers compute the same messages. The zippel proto is
// rerun with every challenge echoed as a prover message, the native prover is
// replayed under those challenges, and every message must match exactly.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod cross_tests {
    use super::{shared, zippel_side};
    use crate::dory_upstream::{self as dory, Blake2bTranscript, GT, PreparedCache};
    use ark_bls12_381::{Fr, G1Projective, G2Projective};
    use backend::{ArkBls12_381, Value};
    use std::path::PathBuf;

    fn echo_proto() -> PathBuf {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src = std::fs::read_to_string(root.join("examples/dory_pcs/dory_pcs.zippel")).unwrap();
        let mut out = String::new();
        for line in src.lines() {
            out.push_str(line);
            out.push('\n');
            let t = line.trim_start();
            for c in ["beta", "alpha", "gamma", "d"] {
                if t.starts_with(&format!("{c} <- challenge<F>;")) {
                    out.push_str(&format!("    {c}_echo <- {c};\n"));
                }
            }
        }
        let path =
            std::env::temp_dir().join(format!("dory_pcs_echo_{}.zippel", std::process::id()));
        std::fs::write(&path, out).unwrap();
        path
    }

    fn gt(v: &Value<ArkBls12_381>) -> GT {
        match v {
            Value::GT(g) => *g,
            _ => panic!("expected GT, got {v}"),
        }
    }
    fn g1(v: &Value<ArkBls12_381>) -> G1Projective {
        match v {
            Value::G1(g) => *g,
            Value::G1Affine(g) => (*g).into(),
            _ => panic!("expected G1, got {v}"),
        }
    }
    fn g2(v: &Value<ArkBls12_381>) -> G2Projective {
        match v {
            Value::G2(g) => *g,
            Value::G2Affine(g) => (*g).into(),
            _ => panic!("expected G2, got {v}"),
        }
    }
    fn fr(v: &Value<ArkBls12_381>) -> Fr {
        match v {
            Value::Scalar(f) => *f,
            _ => panic!("expected scalar, got {v}"),
        }
    }

    #[test]
    fn zippel_and_native_provers_send_identical_messages() {
        let proto = echo_proto();
        for n in [2usize, 4, 6, 8] {
            let sh = shared::build(n);
            let k = sh.k;
            let msgs = zippel_side::Setup::with_proto(&sh, proto.clone()).prove_once();
            // com, vmv (3), K × (6 + beta + 6 + alpha), gamma, final (2), d
            assert_eq!(msgs.len(), 1 + 3 + 14 * k + 1 + 2 + 1, "n = {n}");
            let mut challenges = Vec::new();
            for r in 0..k {
                let base = 4 + 14 * r;
                challenges.push(fr(&msgs[base + 6]));
                challenges.push(fr(&msgs[base + 13]));
            }
            let tail = 4 + 14 * k;
            challenges.push(fr(&msgs[tail]));
            challenges.push(fr(&msgs[tail + 3]));

            let cache = PreparedCache::new(&sh.setup);
            let (com, rows) = dory::commit(&sh.coeffs, k, k, &sh.setup, &cache);
            let mut t = Blake2bTranscript::replay(challenges);
            let p = dory::create_evaluation_proof(
                &sh.coeffs, &sh.point, rows, k, k, &sh.setup, &cache, &mut t,
            );

            assert_eq!(gt(&msgs[0]), com, "n = {n}: commitment");
            assert_eq!(gt(&msgs[1]), p.vmv_message.c, "n = {n}: vmv c");
            assert_eq!(gt(&msgs[2]), p.vmv_message.d2, "n = {n}: vmv d2");
            assert_eq!(g1(&msgs[3]), p.vmv_message.e1, "n = {n}: vmv e1");
            for r in 0..k {
                let (b, f, s) = (4 + 14 * r, &p.first_messages[r], &p.second_messages[r]);
                assert_eq!(gt(&msgs[b]), f.d1_left, "n = {n} round {r}: d1_left");
                assert_eq!(gt(&msgs[b + 1]), f.d1_right, "n = {n} round {r}: d1_right");
                assert_eq!(gt(&msgs[b + 2]), f.d2_left, "n = {n} round {r}: d2_left");
                assert_eq!(gt(&msgs[b + 3]), f.d2_right, "n = {n} round {r}: d2_right");
                assert_eq!(g1(&msgs[b + 4]), f.e1_beta, "n = {n} round {r}: e1_beta");
                assert_eq!(g2(&msgs[b + 5]), f.e2_beta, "n = {n} round {r}: e2_beta");
                assert_eq!(gt(&msgs[b + 7]), s.c_plus, "n = {n} round {r}: c_plus");
                assert_eq!(gt(&msgs[b + 8]), s.c_minus, "n = {n} round {r}: c_minus");
                assert_eq!(g1(&msgs[b + 9]), s.e1_plus, "n = {n} round {r}: e1_plus");
                assert_eq!(g1(&msgs[b + 10]), s.e1_minus, "n = {n} round {r}: e1_minus");
                assert_eq!(g2(&msgs[b + 11]), s.e2_plus, "n = {n} round {r}: e2_plus");
                assert_eq!(g2(&msgs[b + 12]), s.e2_minus, "n = {n} round {r}: e2_minus");
            }
            assert_eq!(g1(&msgs[tail + 1]), p.final_message.e1, "n = {n}: final e1");
            assert_eq!(g2(&msgs[tail + 2]), p.final_message.e2, "n = {n}: final e2");
        }
        let _ = std::fs::remove_file(proto);
    }
}
