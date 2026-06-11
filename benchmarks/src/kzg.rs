//! KZG comparison: zippel-compiled KZG10 polynomial commitment vs.
//! `ark-poly-commit::kzg10::KZG10` — both on BLS12-381.
//!
//! Statement on both sides: prove that polynomial `p` of degree N-1
//! evaluates to `v` at point `z` (verifier already has a commitment to p).
//!
//! Parity decision: the zippel `.zippel` source includes
//! `commitment <- dot(poly_coeffs, srs_g1)` inside the protocol body,
//! so the "prove" timing on the native side covers `commit + open`.
//! Verify covers only `check`.
//!
//! The `.zippel` source pins `N: 2` as a type-parameter default; we
//! string-substitute it into a tempfile to sweep N (same templating
//! trick as sumcheck).

use crate::Timing;

pub const DEFAULT_N: usize = 4;

/// Diagnostic variant: same KZG protocol body, but the `where` clause
/// SRS-structure check (N-1 pairings) is dropped. The native KZG10
/// baseline trusts its setup and doesn't re-verify it per call; this
/// version makes the comparison apples-to-apples on the verifier side.
///
/// Mirrors examples/kzg/kzg.zippel's `private srs_g1` decision so that
/// the only meaningful difference is the `where` clause (which is what
/// the diagnostic is supposed to isolate). N is the type-parameter
/// default; the caller still rebinds it via `sizes.insert("N", n)`.
fn render_zippel_source_no_srs_check() -> &'static str {
    r#"proto kzg<G1: Group, G2: Group, GT: Pairing<G1, G2>, F: Scalar<G1, G2>, N: Size>
        (private poly_coeffs: [F; N], public eval_point: F, public eval_result: F, private srs_g1: [G1; N],
        public gen_g1: G1, public gen_g2: G2, public srs_g2_s: G2)
        where dot(poly_coeffs, [eval_point ^ i for i in 0..N]) == eval_result {

        let poly_x = poly(poly_coeffs);
        commitment <- dot(poly_coeffs, srs_g1);

        let quotient_poly = (poly_x - eval_result) / poly([-eval_point, 1]);

        let quotient_coeffs = coef(quotient_poly);
        let srs_g1_truncated = srs_g1[0..N-1];
        proof <- dot(quotient_coeffs, srs_g1_truncated);

        let pairing_lhs = pair(proof, (srs_g2_s) - (gen_g2 * eval_point));
        let pairing_rhs = pair(commitment - eval_result * gen_g1, gen_g2);
        verify(pairing_lhs == pairing_rhs)
}
"#
}

pub mod zippel_side {
    use super::*;
    use ark_ec::scalar_mul::ScalarMul;
    use ark_ff::One;
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
    use ark_std::UniformRand;
    use backend::{ATyp, ArkBls12_381, ArkConfig, Value};
    use lang::id::{Tid, Vid};
    use share::Ctx;
    use std::io::Write;
    use std::path::PathBuf;
    use std::time::Instant;
    use tempfile::NamedTempFile;
    use zippel::{ZippelArgs, ZippelHandler, check_verification};

    type F = <ArkBls12_381 as ArkConfig>::F;
    type G1 = <ArkBls12_381 as ArkConfig>::G1;
    type G2 = <ArkBls12_381 as ArkConfig>::G2;
    type G1Affine = <ArkBls12_381 as ArkConfig>::G1Affine;

    // Cached SRS artifact. The proto's setup quantities are deterministic
    // in `(seed, n)`, so we seed with `ark_std::test_rng()` and cache
    // keyed on `log_size`. Per-call randomness (polynomial + eval point)
    // stays in `time_protocol` — it doesn't go on disk.
    #[derive(CanonicalSerialize, CanonicalDeserialize)]
    struct KzgSrs {
        g_input: G1,
        h_input: G2,
        srs_affine: Vec<G1Affine>,
        h_val: G2,
    }

    pub struct Setup {
        handler: ZippelHandler<ArkBls12_381>,
        n: usize,
        srs: KzgSrs,
        // Only `Some` for the diagnostic `--no-srs-check` variant — the
        // normal path compiles examples/kzg/kzg.zippel directly with N
        // bound via `sizes.insert`, no per-call source rewriting.
        _source_file: Option<NamedTempFile>,
    }

    impl Setup {
        pub fn new(n: usize) -> Self {
            Self::new_with(n, false)
        }

        /// `drop_srs_check`: if true, use a `.zippel` source without the
        /// where-clause SRS structure check. Diagnostic toggle to isolate
        /// where the zippel-vs-native verifier gap comes from.
        pub fn new_with(n: usize, drop_srs_check: bool) -> Self {
            let (args, _source_file) = if drop_srs_check {
                let mut file = NamedTempFile::with_suffix(".zippel").expect("tempfile");
                file.write_all(render_zippel_source_no_srs_check().as_bytes())
                    .expect("write tempfile");
                (ZippelArgs::new(file.path().to_path_buf()), Some(file))
            } else {
                (
                    ZippelArgs::new(PathBuf::from("examples/kzg/kzg.zippel")),
                    None,
                )
            };

            let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
            let mut sizes = Ctx::new();
            sizes.insert(&Tid::new("N"), &n);
            handler.compile(&sizes);

            // Build (or load) SRS here so it runs inside the caller's
            // `setup_pool().install(...)` block — all cores on cache miss,
            // instant disk load on cache hit. Matches the native side's
            // `Kzg::setup` caching pattern.
            let log_size = n.trailing_zeros() as usize;
            let srs = crate::cache::load_or_build_canonical("kzg_zippel_srs", log_size, || {
                let mut rng = ark_std::test_rng();
                let g_input = G1::rand(&mut rng);
                let h_input = G2::rand(&mut rng);
                let tau_input = F::rand(&mut rng);
                let mut powers_of_tau: Vec<F> = Vec::with_capacity(n);
                let mut acc = F::one();
                for _ in 0..n {
                    powers_of_tau.push(acc);
                    acc *= tau_input;
                }
                let srs_affine = g_input.batch_mul(&powers_of_tau);
                let h_val = h_input * tau_input;
                KzgSrs {
                    g_input,
                    h_input,
                    srs_affine,
                    h_val,
                }
            });

            Setup {
                handler,
                n,
                srs,
                _source_file,
            }
        }

        pub fn time_protocol(&mut self) -> Timing {
            let mut rng = rand::rngs::OsRng;
            let n = self.n;

            let g = Value::G1(self.srs.g_input);
            let h = Value::G2(self.srs.h_input);
            let ss = Value::VecG1Affine(self.srs.srs_affine.clone());
            let h_val = Value::G2(self.srs.h_val);

            let p = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n));
            let z = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());

            let z_val: Value<ArkBls12_381> =
                Value::Vec((0..n).map(|i| z.clone() ^ Value::Index(i)).collect());
            let y = p.clone().dot(z_val);

            let inputs = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
                (Vid("poly_coeffs".to_string()), p),
                (Vid("gen_g1".to_string()), g),
                (Vid("gen_g2".to_string()), h),
                (Vid("eval_point".to_string()), z),
                (Vid("eval_result".to_string()), y),
                (Vid("srs_g1".to_string()), ss),
                (Vid("srs_g2_s".to_string()), h_val),
            ]);

            let prover_scheduled = self.handler.default_schedule_prover();
            let mut prove_sum = std::time::Duration::ZERO;
            let mut last_proof = None;
            for _ in 0..crate::PROVER_SAMPLES {
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
            let prove = prove_sum / crate::PROVER_SAMPLES;
            let proof = last_proof.expect("PROVER_SAMPLES > 0");

            let verifier_scheduled = self.handler.default_schedule_verifier();
            // Average over VERIFY_SAMPLES verifier runs on the same proof.
            // TDag<C> and Vec<Value<C>> both derive Clone, so we re-clone
            // per iteration; clones happen OUTSIDE the per-call timer so
            // they don't bias the mean.
            let mut verify_sum = std::time::Duration::ZERO;
            let mut last_result = None;
            for _ in 0..crate::VERIFY_SAMPLES {
                let sched = verifier_scheduled.clone();
                let proof_c = proof.clone();
                let t = Instant::now();
                let verifier_result = self
                    .handler
                    .run_verifier(sched, proof_c)
                    .expect("run_verifier failed");
                verify_sum += t.elapsed();
                last_result = Some(verifier_result);
            }
            let verify = verify_sum / crate::VERIFY_SAMPLES;

            let result = check_verification(last_result.expect("VERIFY_SAMPLES > 0"));
            assert!(result.passed, "zippel KZG verification FAILED");

            Timing { prove, verify }
        }
    }
}

pub mod native_side {
    use super::*;
    use ark_bls12_381::Bls12_381;
    use ark_ff::UniformRand;
    use ark_poly::{DenseUVPolynomial, Polynomial, univariate::DensePolynomial};
    use ark_poly_commit::kzg10::{KZG10, Powers, UniversalParams, VerifierKey};
    use std::borrow::Cow;
    use std::time::Instant;

    type Kzg =
        KZG10<Bls12_381, DensePolynomial<<Bls12_381 as ark_ec::pairing::Pairing>::ScalarField>>;
    type Fr = <Bls12_381 as ark_ec::pairing::Pairing>::ScalarField;

    pub struct Setup {
        powers: PowersOwned,
        vk: VerifierKey<Bls12_381>,
        n: usize,
    }

    /// Owned analog of `Powers<'_, E>` — `Powers` borrows its slices, but
    /// we need to keep the data alive across iterations.
    struct PowersOwned {
        powers_of_g: Vec<<Bls12_381 as ark_ec::pairing::Pairing>::G1Affine>,
        powers_of_gamma_g: Vec<<Bls12_381 as ark_ec::pairing::Pairing>::G1Affine>,
    }

    impl PowersOwned {
        fn as_powers(&self) -> Powers<'_, Bls12_381> {
            Powers {
                powers_of_g: Cow::Borrowed(&self.powers_of_g),
                powers_of_gamma_g: Cow::Borrowed(&self.powers_of_gamma_g),
            }
        }
    }

    fn build_powers(pp: &UniversalParams<Bls12_381>, supported_degree: usize) -> PowersOwned {
        let powers_of_g = pp.powers_of_g[..=supported_degree].to_vec();
        let powers_of_gamma_g = (0..=supported_degree)
            .map(|i| pp.powers_of_gamma_g[&i])
            .collect::<Vec<_>>();
        PowersOwned {
            powers_of_g,
            powers_of_gamma_g,
        }
    }

    fn build_vk(pp: &UniversalParams<Bls12_381>) -> VerifierKey<Bls12_381> {
        VerifierKey {
            g: pp.powers_of_g[0],
            gamma_g: pp.powers_of_gamma_g[&0],
            h: pp.h,
            beta_h: pp.beta_h,
            prepared_h: pp.prepared_h.clone(),
            prepared_beta_h: pp.prepared_beta_h.clone(),
        }
    }

    impl Setup {
        pub fn new(n: usize) -> Self {
            // n coefficients => degree n-1
            let degree = n - 1;
            // Cache UniversalParams (the heavy bit — 2^log_size G1 powers
            // + a few G2). build_powers + build_vk are cheap slices over
            // the cached params, so we re-derive them per call rather
            // than caching the derived (Powers, VK) too.
            let log_size = n.trailing_zeros() as usize;
            let pp = crate::cache::load_or_build_canonical(
                "kzg_universal_params",
                log_size,
                || {
                    let mut rng = ark_std::test_rng();
                    Kzg::setup(degree, false, &mut rng).expect("kzg setup")
                },
            );
            let powers = build_powers(&pp, degree);
            let vk = build_vk(&pp);
            Setup { powers, vk, n }
        }

        pub fn time_protocol(&self) -> Timing {
            let mut rng = ark_std::test_rng();
            let degree = self.n - 1;
            let poly = DensePolynomial::<Fr>::rand(degree, &mut rng);
            let point = Fr::rand(&mut rng);
            let value = poly.evaluate(&point);

            // Match zippel parity: commit + open are both inside the
            // protocol body on the zippel side, so they're both timed
            // together as "prove" here.
            //
            // commit and open are INDEPENDENT (open only needs `poly` and
            // `rand`, not the commitment), so we run them concurrently in
            // a `rayon::scope` to mirror what the zippel dataflow scheduler
            // does automatically with the `commitment <- dot(...)` and
            // `proof <- dot(...)` nodes. Without this, the upstream
            // KZG10 path serializes ≈2 MSMs + 1 poly division and looks
            // 2× slower than zippel at small thread counts. At
            // threads ≥ 8 intra-MSM parallelism saturates and the gap
            // closes on its own; this fix matters most at threads = 1–4.
            let powers = self.powers.as_powers();
            let mut prove_sum = std::time::Duration::ZERO;
            let mut last_outputs: Option<(_, _)> = None;
            for _ in 0..crate::PROVER_SAMPLES {
                let t = Instant::now();
                let (comm_out, proof_out) = {
                    use std::sync::Mutex;
                    use ark_poly_commit::PCCommitmentState;
                    let comm_out: Mutex<Option<_>> = Mutex::new(None);
                    let proof_out: Mutex<Option<_>> = Mutex::new(None);
                    let rand =
                        ark_poly_commit::kzg10::Randomness::<Fr, DensePolynomial<Fr>>::empty();
                    rayon::scope(|sc| {
                        sc.spawn(|_| {
                            let (comm, _r) =
                                Kzg::commit(&powers, &poly, None, None).expect("kzg commit");
                            *comm_out.lock().unwrap() = Some(comm);
                        });
                        sc.spawn(|_| {
                            let proof =
                                Kzg::open(&powers, &poly, point, &rand).expect("kzg open");
                            *proof_out.lock().unwrap() = Some(proof);
                        });
                    });
                    (
                        comm_out.into_inner().unwrap().unwrap(),
                        proof_out.into_inner().unwrap().unwrap(),
                    )
                };
                prove_sum += t.elapsed();
                last_outputs = Some((comm_out, proof_out));
            }
            let prove = prove_sum / crate::PROVER_SAMPLES;
            let (comm_out, proof_out) = last_outputs.expect("PROVER_SAMPLES > 0");

            // Average over VERIFY_SAMPLES verifier runs on the same proof.
            // Kzg::check borrows everything, so no clone needed in the loop.
            let mut verify_sum = std::time::Duration::ZERO;
            let mut last_ok = false;
            for _ in 0..crate::VERIFY_SAMPLES {
                let t = Instant::now();
                let ok = Kzg::check(&self.vk, &comm_out, point, value, &proof_out)
                    .expect("kzg check");
                verify_sum += t.elapsed();
                last_ok = ok;
            }
            let verify = verify_sum / crate::VERIFY_SAMPLES;

            assert!(last_ok, "ark-poly-commit KZG verification FAILED");

            Timing { prove, verify }
        }
    }
}
