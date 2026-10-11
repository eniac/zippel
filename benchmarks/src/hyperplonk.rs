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
    use std::sync::Arc;
    use zippel::{ZippelArgs, ZippelHandler, check_verification};

    pub struct Setup {
        handler: ZippelHandler<ArkBls12_381>,
        inputs: HashMap<Vid, Arc<Value<ArkBls12_381>>>,
        compile_time: Vec<std::time::Duration>,
    }

    impl Setup {
        pub fn new(sh: &shared::Shared) -> Self {
            Self::with_proto(
                sh,
                PathBuf::from("examples/hyperplonk_snark/hyperplonk_snark.zippel"),
            )
        }

        /// Same inputs, a different proto source (the cross-check test runs a
        /// copy that echoes the challenges).
        pub fn with_proto(sh: &shared::Shared, proto: PathBuf) -> Self {
            let nv = sh.nv;
            let (handler, compile_time) = crate::sample_compile(|| {
                let mut handler: ZippelHandler<ArkBls12_381> =
                    ZippelHandler::new(ZippelArgs::new(proto.clone()));
                let mut sizes = Ctx::new();
                sizes.insert(&Tid::new("S"), &nv);
                handler.compile_for_execution(&sizes);
                handler
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
                ("g", Value::G1(vk.pcs_param.g.into())),
                ("h", Value::G2(vk.pcs_param.h.into())),
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
                .run_prover(crate::lend(&self.inputs))
                .expect("run_prover failed")
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
            let (prove, prove_peak, proof) =
                crate::sample_zippel_prover(&mut self.handler, &self.inputs);
            let (verify, verify_peak, result) =
                crate::sample_zippel_verifier(&mut self.handler, &proof, &self.inputs);
            assert!(
                check_verification(&result),
                "zippel HyperPlonk verification FAILED"
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
            let (verify, verify_peak, ok) = crate::sample(|| {
                verify(
                    &sh.vk,
                    &sh.public_inputs,
                    &proof,
                    &mut IOPTranscript::new(b"hyperplonk"),
                )
                .unwrap_or(false)
            });
            assert!(ok, "native HyperPlonk verification FAILED");
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
    use crate::hyperplonk_upstream::{IOPTranscript, prove};
    use ark_bls12_381::{Fr, G1Projective};
    use backend::{ArkBls12_381, Value};
    use std::path::PathBuf;

    /// The proto with `<name>_echo <- <name>;` after every challenge.
    fn echo_proto() -> PathBuf {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
        let src =
            std::fs::read_to_string(root.join("examples/hyperplonk_snark/hyperplonk_snark.zippel"))
                .unwrap();
        let mut out = String::new();
        for line in src.lines() {
            out.push_str(line);
            out.push('\n');
            if let Some(name) = line.trim().strip_suffix(" <- challenge<F>;") {
                out.push_str(&format!("    {name}_echo <- {name};\n"));
            }
        }
        let path = std::env::temp_dir().join(format!(
            "hyperplonk_snark_echo_{}.zippel",
            std::process::id()
        ));
        std::fs::write(&path, out).unwrap();
        path
    }

    fn g1(v: &Value<ArkBls12_381>) -> G1Projective {
        match v {
            Value::G1(g) => *g,
            Value::G1Affine(g) => (*g).into(),
            _ => panic!("expected G1, got {v}"),
        }
    }
    fn frs(v: &Value<ArkBls12_381>) -> Vec<Fr> {
        match v {
            Value::VecScalar(f) => f.to_vec(),
            _ => panic!("expected scalars, got {v}"),
        }
    }

    #[test]
    fn zippel_and_native_provers_send_identical_messages() {
        let proto = echo_proto();
        for nv in [2usize, 3, 4, 5] {
            let sh = shared::build(nv);
            let msgs = zippel_side::Setup::with_proto(&sh, proto.clone()).prove_once();
            // Echoed challenges are the only scalar messages.
            let (challenges, sent): (Vec<_>, Vec<_>) =
                msgs.iter().partition(|m| matches!(m, Value::Scalar(_)));
            let challenges: Vec<Fr> = challenges
                .into_iter()
                .map(|m| match m {
                    Value::Scalar(f) => *f,
                    _ => unreachable!(),
                })
                .collect();
            assert_eq!(challenges.len(), 5 * nv + 10, "nv = {nv}: challenges");
            assert_eq!(sent.len(), 4 * nv + 6, "nv = {nv}: messages");

            let p = prove(
                &sh.pk,
                &sh.public_inputs,
                &sh.witnesses,
                &mut IOPTranscript::new(b"hyperplonk").replay(challenges),
            )
            .unwrap();

            let mut it = sent.into_iter();
            for (i, c) in p.witness_commits.iter().enumerate() {
                assert_eq!(
                    g1(it.next().unwrap()),
                    G1Projective::from(c.0),
                    "nv = {nv}: witness commit {i}"
                );
            }
            for (r, m) in p.zero_check_proof.proofs.iter().enumerate() {
                assert_eq!(
                    frs(it.next().unwrap()),
                    m.evaluations,
                    "nv = {nv}: gate round {r}"
                );
            }
            let pc = &p.perm_check_proof;
            assert_eq!(
                g1(it.next().unwrap()),
                G1Projective::from(pc.frac_comm.0),
                "nv = {nv}: frac"
            );
            assert_eq!(
                g1(it.next().unwrap()),
                G1Projective::from(pc.prod_x_comm.0),
                "nv = {nv}: prod"
            );
            for (r, m) in pc.zero_check_proof.proofs.iter().enumerate() {
                assert_eq!(
                    frs(it.next().unwrap()),
                    m.evaluations,
                    "nv = {nv}: perm round {r}"
                );
            }
            let b = &p.batch_openings;
            assert_eq!(
                frs(it.next().unwrap()),
                b.f_i_eval_at_point_i,
                "nv = {nv}: evals"
            );
            for (r, m) in b.sum_check_proof.proofs.iter().enumerate() {
                assert_eq!(
                    frs(it.next().unwrap()),
                    m.evaluations,
                    "nv = {nv}: batch round {r}"
                );
            }
            for (i, pi) in b.g_prime_proof.proofs.iter().enumerate() {
                assert_eq!(
                    g1(it.next().unwrap()),
                    G1Projective::from(*pi),
                    "nv = {nv}: opening {i}"
                );
            }
            assert!(it.next().is_none());
        }
        let _ = std::fs::remove_file(proto);
    }
}
