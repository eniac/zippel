//! IPA comparison: zippel-compiled Bulletproofs IPA vs. a vendored port
//! of alex-ozdemir's `Bp2aryStep` (github.com/alex-ozdemir/bulletproofs,
//! src/reductions/bp_2ary_step.rs) — the textbook BCC/BBB+18 Protocol 2.
//! Both sides on Secp256k1, both implementing the same protocol.
//!
//! Statement: prover knows a, b such that P = <g, a> + <h, b> + Q*<a,b>,
//! with two committed vectors a, b over independent base vectors g, h
//! plus one binding point Q. Each recursive round folds the vectors in
//! half and emits L, R via 4 cross MSMs (g_hi⊗a_lo, h_lo⊗b_hi,
//! g_lo⊗a_hi, h_hi⊗b_lo); the verifier here folds bases the same way
//! (naive O(n log n) verify, matching the upstream Bp2aryStep::verify).
//!
//! Vector size N = 2^S; sweep by varying S.
//!
//! Computing P is treated as setup-per-call (untimed) — analogous to
//! zippel's `p_initial_commitment` being supplied as input outside the
//! timed protocol.

use crate::Timing;

/// Zippel half: compiles `examples/ipa/ipa.zippel` and times its generated
/// prover and verifier on Secp256k1.
pub mod zippel_side {
    use super::*;
    use ark_ec::{CurveGroup, VariableBaseMSM};
    use ark_secp256k1::{Affine as SecpAffine, Fr as SecpFr, Projective as SecpProjective};
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
    use ark_std::UniformRand;
    use backend::{ArkSecp256k1, Value};
    use lang::id::{Tid, Vid};
    use share::Ctx;
    use std::collections::HashMap;
    use std::path::PathBuf;
    use zippel::{ZippelArgs, ZippelHandler, check_verification};

    // Cached IPA inputs. Bases (g_vec, h_vec, u_aux_base) are Pedersen
    // setup. (a_vec, b_vec, sum_vec) would normally be the per-call
    // witness, but the bench measures asymptotic prove/verify cost which
    // is data-independent — so we use a deterministic seed and cache
    // them too. p_initial and ip_val_claimed are derived from the cached
    // (bases, witness) via 2 MSMs + 1 inner product; cache them as well
    // so subsequent loads skip the ~2× 2^20 MSM work on the prover-input
    // path.
    #[derive(CanonicalSerialize, CanonicalDeserialize)]
    struct IpaInputs {
        u_aux_base: SecpProjective,
        g_vec: Vec<SecpProjective>,
        h_vec: Vec<SecpProjective>,
        a_vec: Vec<SecpFr>,
        b_vec: Vec<SecpFr>,
        sum_vec: Vec<SecpFr>,
        ip_val_claimed: SecpFr,
        p_initial: SecpProjective,
    }

    impl IpaInputs {
        fn build(n: usize) -> Self {
            let mut rng = ark_std::test_rng();
            let u_aux_base = SecpProjective::rand(&mut rng);
            let g_vec: Vec<SecpProjective> =
                (0..n).map(|_| SecpProjective::rand(&mut rng)).collect();
            let h_vec: Vec<SecpProjective> =
                (0..n).map(|_| SecpProjective::rand(&mut rng)).collect();
            let a_vec: Vec<SecpFr> = (0..n).map(|_| SecpFr::rand(&mut rng)).collect();
            let b_vec: Vec<SecpFr> = (0..n).map(|_| SecpFr::rand(&mut rng)).collect();
            let sum_vec: Vec<SecpFr> = (0..n).map(|_| SecpFr::rand(&mut rng)).collect();

            let ip_val_claimed: SecpFr = a_vec.iter().zip(b_vec.iter()).map(|(a, b)| *a * *b).sum();

            let g_affine: Vec<SecpAffine> = SecpProjective::normalize_batch(&g_vec);
            let h_affine: Vec<SecpAffine> = SecpProjective::normalize_batch(&h_vec);
            let p_initial = SecpProjective::msm(&g_affine, &a_vec).expect("msm g·a")
                + SecpProjective::msm(&h_affine, &b_vec).expect("msm h·b");

            IpaInputs {
                u_aux_base,
                g_vec,
                h_vec,
                a_vec,
                b_vec,
                sum_vec,
                ip_val_claimed,
                p_initial,
            }
        }
    }

    /// A compiled IPA instance plus the cached bases and witness it is timed
    /// on.
    ///
    /// Everything instance-specific lives in `inputs`, which is deterministic
    /// in `S` and therefore cached on disk — the benchmark measures asymptotic
    /// cost, which is data-independent.
    pub struct Setup {
        handler: ZippelHandler<ArkSecp256k1>,
        _n: usize,
        inputs: IpaInputs,
        compile_time: Vec<std::time::Duration>,
    }

    impl Setup {
        /// Compiles the IPA protocol with the size parameter `S` bound to
        /// `s_const` (vector length `N = 2^S`) and loads or builds the cached
        /// bases, witness, and derived commitment.
        ///
        /// # Panics
        /// Panics if compilation fails, if the cache artifact cannot be read
        /// or written, or if an MSM over the generated bases fails.
        pub fn new(s_const: usize) -> Self {
            let n = 1usize << s_const;
            let zippel_file = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("examples/ipa/ipa.zippel");
            let (handler, compile_time) = crate::sample_compile(|| {
                let args = ZippelArgs::new(zippel_file.clone());
                let mut handler: ZippelHandler<ArkSecp256k1> = ZippelHandler::new(args);
                let mut sizes = Ctx::new();
                sizes.insert(&Tid::new("S"), &s_const);
                handler.compile_for_execution(&sizes);
                handler
            });

            let inputs =
                crate::cache::load_or_build_canonical("ipa_zippel_inputs", s_const, || {
                    IpaInputs::build(n)
                });

            Setup {
                handler,
                _n: n,
                inputs,
                compile_time,
            }
        }

        /// Wall-time spent compiling the `.zippel` source into prover and
        /// verifier graphs. Excludes input generation and cache I/O.
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

        /// Runs the compiled prover and verifier on the cached instance.
        ///
        /// # Panics
        /// Panics if the prover or verifier graph fails to execute, or if the
        /// verifier rejects the honestly generated proof.
        pub fn time_protocol(&mut self) -> Timing {
            let inputs = HashMap::<Vid, Value<ArkSecp256k1>>::from_iter([
                (
                    Vid("g_vec".to_string()),
                    Value::vec_g1(self.inputs.g_vec.clone()),
                ),
                (
                    Vid("h_vec".to_string()),
                    Value::vec_g1(self.inputs.h_vec.clone()),
                ),
                (
                    Vid("p_initial_commitment".to_string()),
                    Value::G1(self.inputs.p_initial),
                ),
                (
                    Vid("ip_val_claimed".to_string()),
                    Value::Scalar(self.inputs.ip_val_claimed),
                ),
                (
                    Vid("u_aux_base".to_string()),
                    Value::G1(self.inputs.u_aux_base),
                ),
                (
                    Vid("a_vec_witness".to_string()),
                    Value::vec_scalar(self.inputs.a_vec.clone()),
                ),
                (
                    Vid("b_vec_witness".to_string()),
                    Value::vec_scalar(self.inputs.b_vec.clone()),
                ),
                (
                    Vid("sum_vec".to_string()),
                    Value::vec_scalar(self.inputs.sum_vec.clone()),
                ),
            ]);
            let (prove, prove_peak, proof) =
                crate::sample_zippel_prover(&mut self.handler, &inputs);
            let (verify, verify_peak, result) =
                crate::sample_zippel_verifier(&mut self.handler, &proof, &inputs);
            assert!(
                check_verification(&result),
                "zippel IPA verification FAILED"
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

/// Native baseline: a vendored port of alex-ozdemir's `Bp2aryStep`, the
/// textbook BCC/BBB+18 Protocol 2, over Secp256k1 with a `merlin`
/// Fiat-Shamir transcript.
///
/// The verifier folds the bases itself each round (naive `O(n log n)`),
/// matching upstream rather than using the delayed-scalars optimization.
pub mod native_side {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
    use ark_ff::{Field, PrimeField};
    use ark_secp256k1::{Affine as SecpAffine, Fr, Projective};
    use ark_serialize::CanonicalSerialize;
    use ark_std::UniformRand;
    use merlin::Transcript;
    use rayon::prelude::*;
    use std::borrow::Cow;

    /// The Pedersen bases `g_vec`, `h_vec` and the binding point `q` for one
    /// instance size, together with the vector length `n = 2^S`.
    pub struct Setup {
        n: usize,
        g_vec: Vec<SecpAffine>,
        h_vec: Vec<SecpAffine>,
        q: Projective,
    }

    impl Setup {
        /// Loads or builds the `(g_vec, h_vec, q)` SRS for `N = 2^s_const`
        /// from the artifact cache.
        ///
        /// # Panics
        /// Panics if the cache artifact cannot be read or written.
        pub fn new(s_const: usize) -> Self {
            let n = 1usize << s_const;
            // Cache the SRS (g_vec, h_vec, q). At s=20, this is 2 ×
            // 2^20 secp256k1 affine points (~96 MB), built via 2 ×
            // 2^20 Projective::rand + normalize_batch.
            let (g_vec, h_vec, q) = crate::cache::load_or_build_canonical::<(
                Vec<SecpAffine>,
                Vec<SecpAffine>,
                Projective,
            )>("ipa_srs", s_const, || {
                let mut rng = ark_std::test_rng();
                let g_proj: Vec<Projective> = (0..n).map(|_| Projective::rand(&mut rng)).collect();
                let h_proj: Vec<Projective> = (0..n).map(|_| Projective::rand(&mut rng)).collect();
                let g_vec = Projective::normalize_batch(&g_proj);
                let h_vec = Projective::normalize_batch(&h_proj);
                let q = Projective::rand(&mut rng);
                (g_vec, h_vec, q)
            });
            Setup { n, g_vec, h_vec, q }
        }

        /// Samples a witness pair `(a, b)`, computes the untimed initial
        /// commitment `P = <g,a> + <h,b>`, then times the recursive folding
        /// prover and the base-folding verifier.
        ///
        /// # Panics
        /// Panics if an MSM fails, if a Fiat-Shamir challenge is zero (it must
        /// be invertible), or if the final folded check does not hold.
        pub fn time_protocol(&self) -> Timing {
            let mut rng = ark_std::test_rng();
            let a_vec: Vec<Fr> = (0..self.n).map(|_| Fr::rand(&mut rng)).collect();
            let b_vec: Vec<Fr> = (0..self.n).map(|_| Fr::rand(&mut rng)).collect();
            let ip_val_claimed = ip_fr(&a_vec, &b_vec);

            // Q-free p_initial = <g,a> + <h,b>, supplied as input (untimed)
            // — mirrors zippel's p_initial_commitment. The Protocol-1 →
            // Protocol-2 wrapper (binding Q to P via a Fiat-Shamir
            // challenge) happens inside the timed region on both sides,
            // matching ipa_wrapper in ipa.zippel.
            let p_initial = Projective::msm(&self.g_vec, &a_vec).expect("msm")
                + Projective::msm(&self.h_vec, &b_vec).expect("msm");

            let g_proj_init: Vec<Projective> = self.g_vec.iter().map(|p| p.into_group()).collect();
            let h_proj_init: Vec<Projective> = self.h_vec.iter().map(|p| p.into_group()).collect();

            // ---- Prover ----
            let (prove, prove_peak, (final_a, final_b, proofs)) = crate::sample(|| {
                let mut prover_transcript = Transcript::new(b"ipa-bench");
                absorb_point(&mut prover_transcript, b"p_initial", &p_initial);
                absorb_scalar(&mut prover_transcript, b"c", &ip_val_claimed);
                let x_chal = challenge_scalar(&mut prover_transcript, b"x_chal");
                let q_raised = self.q * x_chal;
                let p_prime = p_initial + q_raised * ip_val_claimed;

                // The first round folds straight from the inputs; each later
                // round owns the halves the previous one built.
                let mut a: Cow<[Fr]> = Cow::Borrowed(&a_vec);
                let mut b: Cow<[Fr]> = Cow::Borrowed(&b_vec);
                let mut g: Cow<[Projective]> = Cow::Borrowed(&g_proj_init);
                let mut h: Cow<[Projective]> = Cow::Borrowed(&h_proj_init);
                let mut p_cur = p_prime;
                let mut proofs: Vec<(Projective, Projective)> = Vec::new();
                while a.len() > 1 {
                    let n = a.len() / 2;
                    let l = msm_proj(&g[n..], &a[..n])
                        + msm_proj(&h[..n], &b[n..])
                        + q_raised * ip_fr(&a[..n], &b[n..]);
                    let r = msm_proj(&g[..n], &a[n..])
                        + msm_proj(&h[n..], &b[..n])
                        + q_raised * ip_fr(&a[n..], &b[..n]);
                    absorb_point(&mut prover_transcript, b"L", &l);
                    absorb_point(&mut prover_transcript, b"R", &r);
                    let x = challenge_scalar(&mut prover_transcript, b"x");
                    let x_inv = x.inverse().expect("nonzero challenge");
                    p_cur = l * x.square() + r * x_inv.square() + p_cur;
                    let a_next: Vec<Fr> = a[..n]
                        .par_iter()
                        .zip(&a[n..])
                        .map(|(lo, hi)| x * lo + x_inv * hi)
                        .collect();
                    let b_next: Vec<Fr> = b[..n]
                        .par_iter()
                        .zip(&b[n..])
                        .map(|(lo, hi)| x_inv * lo + x * hi)
                        .collect();
                    let g_next: Vec<Projective> = g[..n]
                        .par_iter()
                        .zip(&g[n..])
                        .map(|(lo, hi)| *lo * x_inv + *hi * x)
                        .collect();
                    let h_next: Vec<Projective> = h[..n]
                        .par_iter()
                        .zip(&h[n..])
                        .map(|(lo, hi)| *lo * x + *hi * x_inv)
                        .collect();
                    proofs.push((l, r));
                    a = Cow::Owned(a_next);
                    b = Cow::Owned(b_next);
                    g = Cow::Owned(g_next);
                    h = Cow::Owned(h_next);
                }
                let final_a = a[0];
                let final_b = b[0];
                let _ = std::hint::black_box(p_cur);
                (final_a, final_b, proofs)
            });

            // ---- Verifier (naive: fold bases each round, matching upstream) ----
            // The first round folds straight from the bases the verifier
            // keeps; each later round owns the halves the previous one built.
            let (verify, verify_peak, ok) = crate::sample(|| {
                let mut verifier_transcript = Transcript::new(b"ipa-bench");
                let mut g: Cow<[Projective]> = Cow::Borrowed(&g_proj_init);
                let mut h: Cow<[Projective]> = Cow::Borrowed(&h_proj_init);
                absorb_point(&mut verifier_transcript, b"p_initial", &p_initial);
                absorb_scalar(&mut verifier_transcript, b"c", &ip_val_claimed);
                let x_chal = challenge_scalar(&mut verifier_transcript, b"x_chal");
                let q_raised = self.q * x_chal;
                let p_prime = p_initial + q_raised * ip_val_claimed;

                let mut p_cur = p_prime;
                for (l, r) in &proofs {
                    absorb_point(&mut verifier_transcript, b"L", l);
                    absorb_point(&mut verifier_transcript, b"R", r);
                    let x = challenge_scalar(&mut verifier_transcript, b"x");
                    let x_inv = x.inverse().expect("nonzero challenge");
                    p_cur = *l * x.square() + *r * x_inv.square() + p_cur;
                    let n = g.len() / 2;
                    g = Cow::Owned(
                        g[..n]
                            .par_iter()
                            .zip(&g[n..])
                            .map(|(lo, hi)| *lo * x_inv + *hi * x)
                            .collect(),
                    );
                    h = Cow::Owned(
                        h[..n]
                            .par_iter()
                            .zip(&h[n..])
                            .map(|(lo, hi)| *lo * x + *hi * x_inv)
                            .collect(),
                    );
                }
                let expected = g[0] * final_a + h[0] * final_b + q_raised * (final_a * final_b);
                p_cur == expected
            });

            assert!(ok, "vendored Bp2aryStep IPA verification FAILED");
            Timing {
                prove,
                verify,
                prove_peak,
                verify_peak,
            }
        }
    }

    fn msm_proj(bases: &[Projective], scalars: &[Fr]) -> Projective {
        let affine = Projective::normalize_batch(bases);
        Projective::msm(&affine, scalars).expect("msm")
    }

    fn ip_fr(a: &[Fr], b: &[Fr]) -> Fr {
        a.par_iter().zip(b).map(|(x, y)| *x * y).sum()
    }

    fn absorb_point(t: &mut Transcript, label: &'static [u8], p: &Projective) {
        let mut buf = Vec::new();
        p.into_affine()
            .serialize_compressed(&mut buf)
            .expect("serialize");
        t.append_message(label, &buf);
    }

    fn absorb_scalar(t: &mut Transcript, label: &'static [u8], s: &Fr) {
        let mut buf = Vec::new();
        s.serialize_compressed(&mut buf).expect("serialize");
        t.append_message(label, &buf);
    }

    fn challenge_scalar(t: &mut Transcript, label: &'static [u8]) -> Fr {
        let mut buf = [0u8; 64];
        t.challenge_bytes(label, &mut buf);
        Fr::from_le_bytes_mod_order(&buf)
    }
}
