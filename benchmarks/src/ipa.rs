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

pub mod zippel_side {
    use super::*;
    use ark_ec::{CurveGroup, VariableBaseMSM};
    use ark_secp256k1::{Affine as SecpAffine, Fr as SecpFr, Projective as SecpProjective};
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
    use ark_std::UniformRand;
    use backend::{ATyp, ArkSecp256k1, Value};
    use lang::id::{Tid, Vid};
    use share::Ctx;
    use std::path::PathBuf;
    use std::time::Instant;
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

            let ip_val_claimed: SecpFr =
                a_vec.iter().zip(b_vec.iter()).map(|(a, b)| *a * *b).sum();

            let g_affine: Vec<SecpAffine> =
                SecpProjective::normalize_batch(&g_vec);
            let h_affine: Vec<SecpAffine> =
                SecpProjective::normalize_batch(&h_vec);
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

    pub struct Setup {
        handler: ZippelHandler<ArkSecp256k1>,
        n: usize,
        inputs: IpaInputs,
        compile_time: std::time::Duration,
    }

    impl Setup {
        pub fn new(s_const: usize) -> Self {
            let n = 1usize << s_const;
            let zippel_file = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("examples/ipa/ipa.zippel");
            let compile_start = Instant::now();
            let args = ZippelArgs::new(zippel_file);
            let mut handler: ZippelHandler<ArkSecp256k1> = ZippelHandler::new(args);
            let mut sizes = Ctx::new();
            sizes.insert(&Tid::new("S"), &s_const);
            handler.compile(&sizes);
            let compile_time = compile_start.elapsed();

            let inputs = crate::cache::load_or_build_canonical(
                "ipa_zippel_inputs",
                s_const,
                || IpaInputs::build(n),
            );

            Setup {
                handler,
                n,
                inputs,
                compile_time,
            }
        }

        pub fn compile_time(&self) -> std::time::Duration {
            self.compile_time
        }

        pub fn time_protocol(&mut self) -> Timing {
            let inputs = Ctx::<Vid, Value<ArkSecp256k1>>::from_iter([
                (
                    Vid("g_vec".to_string()),
                    Value::VecG1(self.inputs.g_vec.clone()),
                ),
                (
                    Vid("h_vec".to_string()),
                    Value::VecG1(self.inputs.h_vec.clone()),
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
                    Value::VecScalar(self.inputs.a_vec.clone()),
                ),
                (
                    Vid("b_vec_witness".to_string()),
                    Value::VecScalar(self.inputs.b_vec.clone()),
                ),
                (
                    Vid("sum_vec".to_string()),
                    Value::VecScalar(self.inputs.sum_vec.clone()),
                ),
            ]);

            let prover_scheduled = self.handler.default_schedule_prover();
            let mut prove_sum = std::time::Duration::ZERO;
            let mut last_proof = None;
            for _ in 0..*crate::PROVER_SAMPLES {
                let sched = prover_scheduled.clone();
                let inputs_c = inputs.clone();
                let t = Instant::now();
                let proof = self
                    .handler
                    .run_prover(sched, inputs_c)
                    .expect("run_prover failed");
                prove_sum += t.elapsed();
                last_proof = Some(proof);
            }
            let prove = prove_sum / *crate::PROVER_SAMPLES;
            let proof = last_proof.expect("PROVER_SAMPLES > 0");

            let verifier_scheduled = self.handler.default_schedule_verifier();
            let t = Instant::now();
            let verifier_result = self
                .handler
                .run_verifier(verifier_scheduled, proof)
                .expect("run_verifier failed");
            let verify = t.elapsed();

            let result = check_verification(verifier_result);
            assert!(result.passed, "zippel IPA verification FAILED");

            Timing { prove, verify }
        }
    }
}

pub mod native_side {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
    use ark_secp256k1::{Affine as SecpAffine, Fr, Projective};
    use ark_serialize::CanonicalSerialize;
    use ark_ff::{Field, PrimeField};
    use ark_std::UniformRand;
    use merlin::Transcript;
    use rayon::prelude::*;
    use std::time::Instant;

    pub struct Setup {
        n: usize,
        g_vec: Vec<SecpAffine>,
        h_vec: Vec<SecpAffine>,
        q: Projective,
    }

    impl Setup {
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
                let g_proj: Vec<Projective> =
                    (0..n).map(|_| Projective::rand(&mut rng)).collect();
                let h_proj: Vec<Projective> =
                    (0..n).map(|_| Projective::rand(&mut rng)).collect();
                let g_vec = Projective::normalize_batch(&g_proj);
                let h_vec = Projective::normalize_batch(&h_proj);
                let q = Projective::rand(&mut rng);
                (g_vec, h_vec, q)
            });
            Setup { n, g_vec, h_vec, q }
        }

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

            // ---- Prover (sampled PROVER_SAMPLES times) ----
            let mut prove_sum = std::time::Duration::ZERO;
            let mut last_state: Option<(Fr, Fr, Vec<(Projective, Projective)>)> = None;
            for _ in 0..*crate::PROVER_SAMPLES {
                let mut prover_transcript = Transcript::new(b"ipa-bench");
                let t = Instant::now();
                absorb_point(&mut prover_transcript, b"p_initial", &p_initial);
                absorb_scalar(&mut prover_transcript, b"c", &ip_val_claimed);
                let x_chal = challenge_scalar(&mut prover_transcript, b"x_chal");
                let q_raised = self.q * x_chal;
                let p_prime = p_initial + q_raised * ip_val_claimed;

                // Fresh per-iteration state: vectors get consumed by the
                // recursive folding loop, so clone once per sample.
                let mut a = a_vec.clone();
                let mut b = b_vec.clone();
                let mut g = g_proj_init.clone();
                let mut h = h_proj_init.clone();
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
                    a = a_next;
                    b = b_next;
                    g = g_next;
                    h = h_next;
                }
                let final_a = a[0];
                let final_b = b[0];
                std::hint::black_box(p_cur);
                prove_sum += t.elapsed();
                last_state = Some((final_a, final_b, proofs));
            }
            let prove = prove_sum / *crate::PROVER_SAMPLES;
            let (final_a, final_b, proofs) = last_state.expect("PROVER_SAMPLES > 0");

            // ---- Verifier (naive: fold bases each round, matching upstream) ----
            let mut verifier_transcript = Transcript::new(b"ipa-bench");
            let t = Instant::now();
            absorb_point(&mut verifier_transcript, b"p_initial", &p_initial);
            absorb_scalar(&mut verifier_transcript, b"c", &ip_val_claimed);
            let x_chal = challenge_scalar(&mut verifier_transcript, b"x_chal");
            let q_raised = self.q * x_chal;
            let p_prime = p_initial + q_raised * ip_val_claimed;

            let mut g = g_proj_init;
            let mut h = h_proj_init;
            let mut p_cur = p_prime;
            for (l, r) in &proofs {
                absorb_point(&mut verifier_transcript, b"L", l);
                absorb_point(&mut verifier_transcript, b"R", r);
                let x = challenge_scalar(&mut verifier_transcript, b"x");
                let x_inv = x.inverse().expect("nonzero challenge");
                p_cur = *l * x.square() + *r * x_inv.square() + p_cur;
                let n = g.len() / 2;
                g = g[..n]
                    .par_iter()
                    .zip(&g[n..])
                    .map(|(lo, hi)| *lo * x_inv + *hi * x)
                    .collect();
                h = h[..n]
                    .par_iter()
                    .zip(&h[n..])
                    .map(|(lo, hi)| *lo * x + *hi * x_inv)
                    .collect();
            }
            let expected = g[0] * final_a + h[0] * final_b + q_raised * (final_a * final_b);
            let ok = p_cur == expected;
            let verify = t.elapsed();

            assert!(ok, "vendored Bp2aryStep IPA verification FAILED");
            Timing { prove, verify }
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
