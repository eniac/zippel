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
    use std::path::PathBuf;
    use zippel::{
        CompileOptions, CompiledProtocol, CompiledProver, CompiledVerifier, ParsedModule,
    };

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
        prover: CompiledProver<ArkSecp256k1>,
        verifier: CompiledVerifier<ArkSecp256k1>,
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
            let ((prover, verifier), compile_time) = crate::sample_compile(|| {
                let module = ParsedModule::load(&zippel_file).expect("parse protocol");
                let mut sizes = Ctx::new();
                sizes.insert(&Tid::new("S"), &s_const);
                let protocol: CompiledProtocol<ArkSecp256k1> = module
                    .compile(&sizes, CompileOptions::default())
                    .expect("compile protocol");
                (
                    protocol.project_prover(),
                    protocol.project_verifier().expect("project verifier"),
                )
            });

            let inputs =
                crate::cache::load_or_build_canonical("ipa_zippel_inputs", s_const, || {
                    IpaInputs::build(n)
                });

            Setup {
                prover,
                verifier,
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
                self.prover.graph().node_count(),
                self.verifier.graph().node_count(),
            )
        }

        /// Runs the compiled prover and verifier on the cached instance.
        ///
        /// # Panics
        /// Panics if the prover or verifier graph fails to execute, or if the
        /// verifier rejects the honestly generated proof.
        pub fn time_protocol(&mut self) -> Timing {
            let inputs = crate::harness_inputs([
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
                    Value::g1(self.inputs.p_initial),
                ),
                (
                    Vid("ip_val_claimed".to_string()),
                    Value::Scalar(self.inputs.ip_val_claimed),
                ),
                (
                    Vid("u_aux_base".to_string()),
                    Value::g1(self.inputs.u_aux_base),
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
            let (prove, prove_peak, proof) = crate::sample_zippel_prover(&self.prover, &inputs);
            let (verify, verify_peak, passed) =
                crate::sample_zippel_verifier(&self.verifier, &proof, &inputs);
            assert!(passed, "zippel IPA verification FAILED");

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
    use ark_ff::Field;
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
            let statement = Statement {
                g: &g_proj_init,
                h: &h_proj_init,
                q: self.q,
                p: p_initial,
                c: ip_val_claimed,
            };

            let (prove, prove_peak, proof) =
                crate::sample(|| prove(&statement, &a_vec, &b_vec, &mut IpaTranscript::new()));
            let (verify, verify_peak, passed) =
                crate::sample(|| verify(&statement, &proof, &mut IpaTranscript::new()));

            assert!(passed, "vendored Bp2aryStep IPA verification FAILED");
            Timing {
                prove,
                verify,
                prove_peak,
                verify_peak,
            }
        }
    }

    /// The IPA statement: `p = <g, a> + <h, b>` and `c = <a, b>`, with binding
    /// point `q`.
    pub(crate) struct Statement<'a> {
        pub g: &'a [Projective],
        pub h: &'a [Projective],
        pub q: Projective,
        pub p: Projective,
        pub c: Fr,
    }

    /// Each round's `(L, R)`, and the folded `a` and `b`.
    pub(crate) struct Proof {
        pub rounds: Vec<(Projective, Projective)>,
        pub a: Fr,
        pub b: Fr,
    }

    /// The merlin transcript; in test builds its challenges come from
    /// `Challenges::default()`, for cross-verification against Zippel.
    pub(crate) struct IpaTranscript {
        transcript: Transcript,
        #[cfg(test)]
        challenges: crate::cross::Challenges,
    }

    impl IpaTranscript {
        pub(crate) fn new() -> Self {
            Self {
                transcript: Transcript::new(b"ipa-bench"),
                #[cfg(test)]
                challenges: crate::cross::Challenges::default(),
            }
        }

        fn point(&mut self, label: &'static [u8], p: &Projective) {
            let mut buf = Vec::new();
            p.into_affine()
                .serialize_compressed(&mut buf)
                .expect("serialize");
            self.transcript.append_message(label, &buf);
        }

        fn scalar(&mut self, label: &'static [u8], s: &Fr) {
            let mut buf = Vec::new();
            s.serialize_compressed(&mut buf).expect("serialize");
            self.transcript.append_message(label, &buf);
        }

        #[cfg_attr(test, allow(unused_variables))]
        fn challenge(&mut self, label: &'static [u8]) -> Fr {
            #[cfg(test)]
            return self.challenges.next_scalar();
            #[cfg(not(test))]
            {
                use ark_ff::PrimeField;
                let mut buf = [0u8; 64];
                self.transcript.challenge_bytes(label, &mut buf);
                Fr::from_le_bytes_mod_order(&buf)
            }
        }
    }

    /// Protocol 1 (binding `q` to `p` with a challenge), then the recursive folding
    /// of Protocol 2.
    pub(crate) fn prove(
        st: &Statement<'_>,
        a_vec: &[Fr],
        b_vec: &[Fr],
        t: &mut IpaTranscript,
    ) -> Proof {
        t.point(b"p_initial", &st.p);
        t.scalar(b"c", &st.c);
        let x_chal = t.challenge(b"x_chal");
        let q_raised = st.q * x_chal;
        let p_prime = st.p + q_raised * st.c;

        // The first round folds straight from the inputs; each later
        // round owns the halves the previous one built.
        let mut a: Cow<[Fr]> = Cow::Borrowed(a_vec);
        let mut b: Cow<[Fr]> = Cow::Borrowed(b_vec);
        let mut g: Cow<[Projective]> = Cow::Borrowed(st.g);
        let mut h: Cow<[Projective]> = Cow::Borrowed(st.h);
        let mut p_cur = p_prime;
        let mut rounds: Vec<(Projective, Projective)> = Vec::new();
        while a.len() > 1 {
            let n = a.len() / 2;
            let l = msm_proj(&g[n..], &a[..n])
                + msm_proj(&h[..n], &b[n..])
                + q_raised * ip_fr(&a[..n], &b[n..]);
            let r = msm_proj(&g[..n], &a[n..])
                + msm_proj(&h[n..], &b[..n])
                + q_raised * ip_fr(&a[n..], &b[..n]);
            t.point(b"L", &l);
            t.point(b"R", &r);
            let x = t.challenge(b"x");
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
            rounds.push((l, r));
            a = Cow::Owned(a_next);
            b = Cow::Owned(b_next);
            g = Cow::Owned(g_next);
            h = Cow::Owned(h_next);
        }
        let _ = std::hint::black_box(p_cur);
        Proof {
            rounds,
            a: a[0],
            b: b[0],
        }
    }

    /// The naive verifier: folds the bases each round, matching upstream.
    pub(crate) fn verify(st: &Statement<'_>, proof: &Proof, t: &mut IpaTranscript) -> bool {
        // The first round folds straight from the bases the verifier
        // keeps; each later round owns the halves the previous one built.
        let mut g: Cow<[Projective]> = Cow::Borrowed(st.g);
        let mut h: Cow<[Projective]> = Cow::Borrowed(st.h);
        t.point(b"p_initial", &st.p);
        t.scalar(b"c", &st.c);
        let x_chal = t.challenge(b"x_chal");
        let q_raised = st.q * x_chal;
        let p_prime = st.p + q_raised * st.c;

        let mut p_cur = p_prime;
        for (l, r) in &proof.rounds {
            t.point(b"L", l);
            t.point(b"R", r);
            let x = t.challenge(b"x");
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
        let expected = g[0] * proof.a + h[0] * proof.b + q_raised * (proof.a * proof.b);
        p_cur == expected
    }

    fn msm_proj(bases: &[Projective], scalars: &[Fr]) -> Projective {
        let affine = Projective::normalize_batch(bases);
        Projective::msm(&affine, scalars).expect("msm")
    }

    fn ip_fr(a: &[Fr], b: &[Fr]) -> Fr {
        a.par_iter().zip(b).map(|(x, y)| *x * y).sum()
    }
}

// ---------------------------------------------------------------------------
// Cross-verification: at the same challenges, each verifier accepts the other's
// proof.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod cross_tests {
    use super::native_side::{IpaTranscript, Proof, Statement, prove, verify};
    use crate::cross::{Challenges, Direction};
    use ark_ec::{CurveGroup, VariableBaseMSM};
    use ark_ff::{One, UniformRand};
    use ark_secp256k1::{Fr, Projective};
    use backend::{ArkSecp256k1, Value};

    type V = Value<ArkSecp256k1>;

    fn g(v: &V) -> Projective {
        match v {
            Value::G1(g) => **g,
            Value::G1Affine(g) => (**g).into(),
            _ => panic!("expected a point, got {v}"),
        }
    }
    fn scalar(v: &V) -> Fr {
        match v {
            Value::Scalar(f) => *f,
            _ => panic!("expected a scalar, got {v}"),
        }
    }

    /// The native proof as Zippel's messages: each round's L and R, then a and b.
    fn as_zippel(p: &Proof) -> Vec<V> {
        p.rounds
            .iter()
            .flat_map(|(l, r)| [Value::g1(*l), Value::g1(*r)])
            .chain([Value::Scalar(p.a), Value::Scalar(p.b)])
            .collect()
    }

    fn as_native(m: &[V]) -> Proof {
        let (rounds, last) = m.split_at(m.len() - 2);
        Proof {
            rounds: rounds.chunks(2).map(|lr| (g(&lr[0]), g(&lr[1]))).collect(),
            a: scalar(&last[0]),
            b: scalar(&last[1]),
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
        let mut rng = ark_std::test_rng();
        for s in [1usize, 2, 4] {
            let n = 1 << s;
            let gs: Vec<Projective> = (0..n).map(|_| Projective::rand(&mut rng)).collect();
            let hs: Vec<Projective> = (0..n).map(|_| Projective::rand(&mut rng)).collect();
            let a: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
            let b: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
            let st = Statement {
                g: &gs,
                h: &hs,
                q: Projective::rand(&mut rng),
                p: Projective::msm(&Projective::normalize_batch(&gs), &a).unwrap()
                    + Projective::msm(&Projective::normalize_batch(&hs), &b).unwrap(),
                c: a.iter().zip(&b).map(|(x, y)| *x * y).sum(),
            };
            let (prover, verifier) = crate::cross::compile::<ArkSecp256k1>("ipa", &[("S", s)]);
            let inputs = crate::harness_inputs([
                ("g_vec", Value::vec_g1(gs.clone())),
                ("h_vec", Value::vec_g1(hs.clone())),
                ("p_initial_commitment", Value::g1(st.p)),
                ("ip_val_claimed", Value::Scalar(st.c)),
                ("u_aux_base", Value::g1(st.q)),
                ("a_vec_witness", Value::vec_scalar(a.clone())),
                ("b_vec_witness", Value::vec_scalar(b.clone())),
            ]);

            match direction {
                Direction::NativeToZippel => {
                    let native = as_zippel(&prove(&st, &a, &b, &mut IpaTranscript::new()));
                    assert!(
                        verifier
                            .verify_with(
                                native.clone(),
                                crate::lend(&inputs),
                                &mut Challenges::default()
                            )
                            .unwrap(),
                        "s = {s}: Zippel rejects the native proof"
                    );
                    let mut wrong = native;
                    let last = wrong.len() - 1;
                    wrong[last] = Value::Scalar(scalar(&wrong[last]) + Fr::one());
                    assert!(
                        !verifier
                            .verify_with(wrong, crate::lend(&inputs), &mut Challenges::default())
                            .unwrap(),
                        "s = {s}: Zippel accepts a wrong final b"
                    );
                }
                Direction::ZippelToNative => {
                    let ours = prover
                        .prove_with(crate::lend(&inputs), &mut Challenges::default())
                        .unwrap();
                    assert_eq!(ours.len(), 2 * s + 2, "s = {s}: Zippel's message count");
                    assert!(
                        verify(&st, &as_native(&ours), &mut IpaTranscript::new()),
                        "s = {s}: the native verifier rejects Zippel's proof"
                    );
                }
            }
        }
    }
}
