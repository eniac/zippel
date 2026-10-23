//! HyperPlonk comparison, end to end (PIOP + PCS): zippel-compiled
//! `examples/hyperplonk_snark/hyperplonk_snark.zippel` vs. Espresso's
//! HyperPlonk (ported to arkworks 0.6 in `src/hyperplonk_upstream/`), both on
//! BLS12-381 with multilinear KZG.
//!
//! Statement on both sides: a vanilla-Plonk circuit of 2^N gates (three
//! witness columns, five selectors, four public inputs), proved with the
//! gate-identity zerocheck, the permutation check, and one batched opening of
//! all 22 evaluation claims.
//!
//! Parity decisions:
//!   - One SRS and one circuit per size (Espresso's `MockCircuit`: random
//!     satisfying gates, identity wiring), preprocessed by the native port in
//!     `shared` and fed to both sides. Preprocessing (selector and
//!     permutation commitments) is outside the timed region on both sides.
//!   - "prove" starts from the witness columns and includes the witness
//!     commitments; "verify" takes the proof and the verifying key.
//!   - Fiat-Shamir: native uses its Merlin transcript; zippel uses its own
//!     sponge and also absorbs the verifying key, which upstream leaves out.
//!
//! `log_size` = N (number of variables, 2^N gates).

use crate::Timing;

pub mod shared {
    use crate::hyperplonk_upstream::{
        CustomizedGates, HyperPlonkProvingKey, HyperPlonkVerifyingKey, MockCircuit,
        MultilinearUniversalParams, preprocess,
    };
    use ark_bls12_381::{Bls12_381, Fr};
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
    use ark_std::rand::{SeedableRng, rngs::StdRng};

    #[derive(CanonicalSerialize, CanonicalDeserialize)]
    struct Stored {
        srs: MultilinearUniversalParams<Bls12_381>,
        public_inputs: Vec<Fr>,
        witnesses: Vec<Vec<Fr>>,
        permutation: Vec<Fr>,
        selectors: Vec<Vec<Fr>>,
    }

    pub struct Shared {
        pub nv: usize,
        pub public_inputs: Vec<Fr>,
        pub witnesses: Vec<Vec<Fr>>,
        pub pk: HyperPlonkProvingKey<Bls12_381>,
        pub vk: HyperPlonkVerifyingKey<Bls12_381>,
    }

    /// Seeded; the SRS and circuit are cached as
    /// `artifacts/hyperplonk_shared_log<nv>.bin`, and preprocessing reruns.
    ///
    /// # Panics
    /// Panics if `nv < 2`, or if the cache or preprocessing fails.
    pub fn build(nv: usize) -> Shared {
        assert!(nv >= 2, "HyperPlonk benchmark needs at least 4 gates");
        let gate = CustomizedGates::vanilla_plonk_gate();
        let stored = crate::cache::load_or_build_canonical("hyperplonk_shared", nv, || {
            let mut rng = StdRng::seed_from_u64(0x4B_504C ^ nv as u64);
            let srs = MultilinearUniversalParams::gen_srs_for_testing(&mut rng, nv);
            let c = MockCircuit::<Fr>::new(1 << nv, &gate, &mut rng);
            Stored {
                srs,
                public_inputs: c.public_inputs,
                witnesses: c.witnesses,
                permutation: c.index.permutation,
                selectors: c.index.selectors,
            }
        });
        let index = crate::hyperplonk_upstream::snark::HyperPlonkIndex {
            params: crate::hyperplonk_upstream::snark::HyperPlonkParams {
                num_constraints: 1 << nv,
                num_pub_input: stored.public_inputs.len(),
                gate_func: gate,
            },
            permutation: stored.permutation,
            selectors: stored.selectors,
        };
        let (pk, vk) = preprocess(&index, &stored.srs).expect("preprocess");
        Shared {
            nv,
            public_inputs: stored.public_inputs,
            witnesses: stored.witnesses,
            pk,
            vk,
        }
    }
}

pub mod zippel_side {
    use super::*;
    use ark_bls12_381::G2Affine;
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
            let proto = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("examples/hyperplonk_snark/hyperplonk_snark.zippel");
            let nv = sh.nv;
            let ((prover, verifier), compile_time) = crate::sample_compile(|| {
                let module = ParsedModule::load(&proto).expect("parse protocol");
                let mut sizes = Ctx::new();
                sizes.insert(&Tid::new("S"), &nv);
                let protocol: CompiledProtocol<ArkBls12_381> = module
                    .compile(&sizes, CompileOptions::default())
                    .expect("compile protocol");
                (
                    protocol.project_prover(),
                    protocol.project_verifier().expect("project verifier"),
                )
            });

            let (pk, vk) = (&sh.pk, &sh.vk);
            let col = |v: &Vec<_>| Value::vec_scalar(v.clone());
            let ck: Vec<_> = pk
                .pcs_param
                .powers_of_g
                .iter()
                .flat_map(|l| l.evals.iter().copied())
                .collect();
            assert_eq!(ck.len(), 2 * (1 << nv) - 1);
            let mut named = vec![
                ("w0", col(&sh.witnesses[0])),
                ("w1", col(&sh.witnesses[1])),
                ("w2", col(&sh.witnesses[2])),
                (
                    "sel_comms",
                    Value::vec_g1_affine(vk.selector_commitments.iter().map(|c| c.0).collect()),
                ),
                (
                    "perm_comms",
                    Value::vec_g1_affine(vk.perm_commitments.iter().map(|c| c.0).collect()),
                ),
                ("pub_input", col(&sh.public_inputs)),
                ("ck", Value::vec_g1_affine(ck)),
                ("g", Value::g1(vk.pcs_param.g.into())),
                ("h", Value::g2(vk.pcs_param.h.into())),
                (
                    "h_mask",
                    Value::vec_g2(
                        vk.pcs_param
                            .h_mask
                            .iter()
                            .map(|&a: &G2Affine| a.into())
                            .collect(),
                    ),
                ),
            ];
            for (i, name) in ["q0", "q1", "q2", "q3", "q4"].into_iter().enumerate() {
                named.push((name, col(&pk.selector_oracles[i].evaluations)));
            }
            for (i, name) in ["s0", "s1", "s2"].into_iter().enumerate() {
                named.push((name, col(&pk.permutation_oracles[i].evaluations)));
            }
            let inputs =
                crate::harness_inputs(named.into_iter().map(|(k, v)| (Vid(k.to_string()), v)));

            Setup {
                prover,
                verifier,
                inputs,
                compile_time,
            }
        }

        /// One prover run under `challenger`; the proof is the list of prover
        /// messages in order.
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

        /// Whether the verifier accepts `proof` under `challenger`.
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
            assert!(passed, "zippel HyperPlonk verification FAILED");
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
    use crate::hyperplonk_upstream::{IOPTranscript, prove, verify};

    pub struct Setup<'a> {
        sh: &'a shared::Shared,
    }

    impl<'a> Setup<'a> {
        pub const fn new(sh: &'a shared::Shared) -> Self {
            Setup { sh }
        }

        /// # Panics
        /// Panics if the native prover fails or the verifier rejects.
        pub fn time_protocol(&self) -> Timing {
            let sh = self.sh;
            let (prove, prove_peak, proof) = crate::sample(|| {
                prove(
                    &sh.pk,
                    &sh.public_inputs,
                    &sh.witnesses,
                    &mut IOPTranscript::new(b"hyperplonk"),
                )
                .expect("native HyperPlonk prove")
            });
            let (verify, verify_peak, passed) = crate::sample(|| {
                verify(
                    &sh.vk,
                    &sh.public_inputs,
                    &proof,
                    &mut IOPTranscript::new(b"hyperplonk"),
                )
                .unwrap_or(false)
            });
            assert!(passed, "native HyperPlonk verification FAILED");
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
    use crate::hyperplonk_upstream::pcs::{BatchProof, Commitment, MultilinearKzgProof};
    use crate::hyperplonk_upstream::piop::ProductCheckProof;
    use crate::hyperplonk_upstream::{HyperPlonkProof, IOPTranscript, prove, verify};
    use crate::sumcheck_upstream::poly_iop::structs::{IOPProof, IOPProverMessage};
    use ark_bls12_381::{Bls12_381, Fr, G1Affine};
    use ark_ec::CurveGroup;
    use backend::{ArkBls12_381, Value};

    type V = Value<ArkBls12_381>;

    fn g1(v: &V) -> G1Affine {
        match v {
            Value::G1(g) => g.into_affine(),
            Value::G1Affine(g) => **g,
            _ => panic!("expected G1, got {v}"),
        }
    }
    fn frs(v: &V) -> Vec<Fr> {
        match v {
            Value::VecScalar(f) => f.to_vec(),
            _ => panic!("expected scalars, got {v}"),
        }
    }

    fn rounds(p: &IOPProof<Fr>) -> impl Iterator<Item = V> + '_ {
        p.proofs
            .iter()
            .map(|m| Value::vec_scalar(m.evaluations.clone()))
    }

    /// The native proof as Zippel's messages: witness commitments, gate sumcheck
    /// rounds, frac and prod, permutation rounds, evaluations, batch rounds, and
    /// the opening.
    fn as_zippel(p: &HyperPlonkProof<Bls12_381>) -> Vec<V> {
        let pc = &p.perm_check_proof;
        let b = &p.batch_openings;
        p.witness_commits
            .iter()
            .map(|c| Value::g1_affine(c.0))
            .chain(rounds(&p.zero_check_proof))
            .chain([pc.frac_comm, pc.prod_x_comm].map(|c| Value::g1_affine(c.0)))
            .chain(rounds(&pc.zero_check_proof))
            .chain([Value::vec_scalar(b.f_i_eval_at_point_i.clone())])
            .chain(rounds(&b.sum_check_proof))
            .chain(
                b.g_prime_proof
                    .proofs
                    .iter()
                    .map(|&pi| Value::g1_affine(pi)),
            )
            .collect()
    }

    /// Zippel's messages as the native proof. A sumcheck proof's `point` is its
    /// challenges, which the native verifier reads only for the batch opening:
    /// the last `nv` challenges of the transcript.
    fn as_native(m: &[V], nv: usize, challenges: &[Fr]) -> HyperPlonkProof<Bls12_381> {
        assert_eq!(m.len(), 4 * nv + 6, "Zippel's message count");
        let sumcheck = |at: usize| IOPProof {
            point: challenges[challenges.len() - nv..].to_vec(),
            proofs: m[at..at + nv]
                .iter()
                .map(|r| IOPProverMessage {
                    evaluations: frs(r),
                })
                .collect(),
        };
        let batch_at = 3 + nv + 2 + nv + 1;
        HyperPlonkProof {
            witness_commits: m[..3].iter().map(|c| Commitment(g1(c))).collect(),
            zero_check_proof: sumcheck(3),
            perm_check_proof: ProductCheckProof {
                zero_check_proof: sumcheck(3 + nv + 2),
                frac_comm: Commitment(g1(&m[3 + nv])),
                prod_x_comm: Commitment(g1(&m[3 + nv + 1])),
            },
            batch_openings: BatchProof {
                sum_check_proof: sumcheck(batch_at),
                f_i_eval_at_point_i: frs(&m[batch_at - 1]),
                g_prime_proof: MultilinearKzgProof {
                    proofs: m[batch_at + nv..].iter().map(g1).collect(),
                },
            },
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
        for nv in [2usize, 3, 4, 5] {
            let sh = shared::build(nv);
            let z = zippel_side::Setup::new(&sh);

            match direction {
                Direction::NativeToZippel => {
                    let native = prove(
                        &sh.pk,
                        &sh.public_inputs,
                        &sh.witnesses,
                        &mut IOPTranscript::new(b"hyperplonk"),
                    )
                    .expect("native prove");
                    let native = as_zippel(&native);
                    assert!(
                        z.verify_with(native.clone(), &mut Challenges::default()),
                        "nv = {nv}: Zippel rejects the native proof"
                    );
                    assert!(
                        !z.verify_with(native, &mut Challenges::seeded(1)),
                        "nv = {nv}: Zippel accepts the native proof at other challenges"
                    );
                }
                Direction::ZippelToNative => {
                    let ours = z.prove_with(&mut Challenges::default());
                    // The challenges Zippel drew: the same sequence, 5·nv + 10 long.
                    let mut seq = Challenges::default();
                    let challenges: Vec<Fr> = (0..5 * nv + 10).map(|_| seq.next_scalar()).collect();
                    let proof = as_native(&ours, nv, &challenges);
                    assert!(
                        verify(
                            &sh.vk,
                            &sh.public_inputs,
                            &proof,
                            &mut IOPTranscript::new(b"hyperplonk")
                        )
                        .unwrap_or(false),
                        "nv = {nv}: the native verifier rejects Zippel's proof"
                    );
                }
            }
        }
    }
}
