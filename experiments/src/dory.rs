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
            let proto = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("examples/dory_pcs/dory_pcs.zippel");
            let k = sh.k;
            let ((prover, verifier), compile_time) = crate::sample_compile(|| {
                let module = ParsedModule::load(&proto).expect("parse protocol");
                let mut sizes = Ctx::new();
                sizes.insert(&Tid::new("K"), &k);
                let protocol: CompiledProtocol<ArkBls12_381> = module
                    .compile(&sizes, CompileOptions::default())
                    .expect("compile protocol");
                (
                    protocol.project_prover(),
                    protocol.project_verifier().expect("project verifier"),
                )
            });

            let (s, v) = (&sh.setup, &sh.vsetup);
            let nv = 1usize << k;
            let inputs = crate::harness_inputs(
                [
                    ("m", Value::vec_scalar(sh.coeffs.clone())),
                    // upstream point = columns (sigma) then rows (nu)
                    ("col_pt", Value::vec_scalar(sh.point[..k].to_vec())),
                    ("row_pt", Value::vec_scalar(sh.point[k..].to_vec())),
                    ("y", Value::Scalar(sh.y)),
                    (
                        "g1_vec",
                        Value::vec_g1_affine(ark_bls12_381::G1Projective::normalize_batch(
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
                    ("g1_0", Value::g1(v.g1_0)),
                    ("g2_0", Value::g2(v.g2_0)),
                    ("h1", Value::g1(v.h1)),
                    ("h2", Value::g2(v.h2)),
                    ("ht", Value::gt(v.ht)),
                    ("chi", Value::vec_gt(v.chi[..=k].to_vec())),
                    ("delta_1l", Value::vec_gt(v.delta_1l[..=k].to_vec())),
                    ("delta_1r", Value::vec_gt(v.delta_1r[..=k].to_vec())),
                    ("delta_2r", Value::vec_gt(v.delta_2r[..=k].to_vec())),
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

        /// One prover run; the proof is the list of prover messages in order.
        ///
        /// # Panics
        /// Panics if the prover graph fails to execute.
        pub fn prove_once(&mut self) -> Vec<Value<ArkBls12_381>> {
            self.prover
                .prove(crate::lend(&self.inputs))
                .expect("run_prover failed")
        }

        /// One prover run under `challenger`'s transcript.
        ///
        /// # Panics
        /// Panics if the prover graph fails to execute.
        pub fn prove_with(
            &self,
            challenger: &mut (impl zippel::runtime::Challenger<ArkBls12_381> + Send),
        ) -> Vec<Value<ArkBls12_381>> {
            self.prover
                .prove_with(crate::lend(&self.inputs), challenger)
                .expect("run_prover failed")
        }

        /// Whether the verifier accepts `proof` under `challenger`'s transcript.
        ///
        /// # Panics
        /// Panics if the verifier graph fails to execute.
        pub fn verify_with(
            &self,
            proof: Vec<Value<ArkBls12_381>>,
            challenger: &mut (impl zippel::runtime::Challenger<ArkBls12_381> + Send),
        ) -> bool {
            self.verifier
                .verify_with(proof, crate::lend(&self.inputs), challenger)
                .expect("run_verifier failed")
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
            assert!(passed, "zippel Dory verification FAILED");
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
            let (prove, prove_peak, (com, proof)) = crate::sample(|| {
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
            let (verify, verify_peak, passed) = crate::sample(|| {
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
            assert!(passed, "native Dory verification FAILED");
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
// Cross-verification: at the same challenges, each verifier accepts the other
// implementation's proof.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod cross_tests {
    use super::{shared, zippel_side};
    use crate::cross::{Challenges, Direction};
    use crate::dory_upstream::{
        self as dory, Blake2bTranscript, DoryProof, FirstReduceMessage, GT, PreparedCache,
        ScalarProductMessage, SecondReduceMessage, VMVMessage,
    };
    use ark_bls12_381::{G1Projective, G2Projective};
    use backend::{ArkBls12_381, Value};

    type V = Value<ArkBls12_381>;

    fn gt(v: &V) -> GT {
        match v {
            Value::GT(g) => **g,
            _ => panic!("expected GT, got {v}"),
        }
    }
    fn g1(v: &V) -> G1Projective {
        match v {
            Value::G1(g) => **g,
            Value::G1Affine(g) => (**g).into(),
            _ => panic!("expected G1, got {v}"),
        }
    }
    fn g2(v: &V) -> G2Projective {
        match v {
            Value::G2(g) => **g,
            Value::G2Affine(g) => (**g).into(),
            _ => panic!("expected G2, got {v}"),
        }
    }

    /// The native proof as Zippel's messages: the commitment, the VMV message,
    /// each round's 12 messages, and the final message.
    fn as_zippel(com: GT, p: &DoryProof) -> Vec<V> {
        let mut out = vec![
            Value::gt(com),
            Value::gt(p.vmv_message.c),
            Value::gt(p.vmv_message.d2),
            Value::g1(p.vmv_message.e1),
        ];
        for (f, s) in p.first_messages.iter().zip(&p.second_messages) {
            out.extend([
                Value::gt(f.d1_left),
                Value::gt(f.d1_right),
                Value::gt(f.d2_left),
                Value::gt(f.d2_right),
                Value::g1(f.e1_beta),
                Value::g2(f.e2_beta),
                Value::gt(s.c_plus),
                Value::gt(s.c_minus),
                Value::g1(s.e1_plus),
                Value::g1(s.e1_minus),
                Value::g2(s.e2_plus),
                Value::g2(s.e2_minus),
            ]);
        }
        out.extend([Value::g1(p.final_message.e1), Value::g2(p.final_message.e2)]);
        out
    }

    /// Zippel's messages as the native proof, and the commitment.
    fn as_native(m: &[V], k: usize) -> (GT, DoryProof) {
        assert_eq!(m.len(), 4 + 12 * k + 2, "Zippel's message count");
        let rounds = |r: usize| &m[4 + 12 * r..4 + 12 * (r + 1)];
        let proof = DoryProof {
            vmv_message: VMVMessage {
                c: gt(&m[1]),
                d2: gt(&m[2]),
                e1: g1(&m[3]),
            },
            first_messages: (0..k)
                .map(|r| {
                    let x = rounds(r);
                    FirstReduceMessage {
                        d1_left: gt(&x[0]),
                        d1_right: gt(&x[1]),
                        d2_left: gt(&x[2]),
                        d2_right: gt(&x[3]),
                        e1_beta: g1(&x[4]),
                        e2_beta: g2(&x[5]),
                    }
                })
                .collect(),
            second_messages: (0..k)
                .map(|r| {
                    let x = rounds(r);
                    SecondReduceMessage {
                        c_plus: gt(&x[6]),
                        c_minus: gt(&x[7]),
                        e1_plus: g1(&x[8]),
                        e1_minus: g1(&x[9]),
                        e2_plus: g2(&x[10]),
                        e2_minus: g2(&x[11]),
                    }
                })
                .collect(),
            final_message: ScalarProductMessage {
                e1: g1(&m[4 + 12 * k]),
                e2: g2(&m[5 + 12 * k]),
            },
            nu: k,
            sigma: k,
        };
        (gt(&m[0]), proof)
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
        for n in [2usize, 4, 6] {
            let sh = shared::build(n);
            let k = sh.k;
            let z = zippel_side::Setup::new(&sh);
            let cache = PreparedCache::new(&sh.setup);

            match direction {
                Direction::NativeToZippel => {
                    let (com, rows) = dory::commit(&sh.coeffs, k, k, &sh.setup, &cache);
                    let native = dory::create_evaluation_proof(
                        &sh.coeffs,
                        &sh.point,
                        rows,
                        k,
                        k,
                        &sh.setup,
                        &cache,
                        &mut Blake2bTranscript::new(b"dory-cross"),
                    );
                    let native = as_zippel(com, &native);
                    assert!(
                        z.verify_with(native.clone(), &mut Challenges::default()),
                        "n = {n}: Zippel rejects the native proof"
                    );
                    assert!(
                        !z.verify_with(native, &mut Challenges::seeded(1)),
                        "n = {n}: Zippel accepts the native proof at other challenges"
                    );
                }
                Direction::ZippelToNative => {
                    let (com, proof) = as_native(&z.prove_with(&mut Challenges::default()), k);
                    assert!(
                        dory::verify_evaluation_proof(
                            com,
                            sh.y,
                            &sh.point,
                            &proof,
                            &sh.vsetup,
                            &mut Blake2bTranscript::new(b"dory-cross"),
                        ),
                        "n = {n}: the native verifier rejects Zippel's proof"
                    );
                }
            }
        }
    }
}
