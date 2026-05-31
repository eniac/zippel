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
    r#"proto kzg<G1: Group, G2: Group, GT: Pairing<G1, G2>, F: Scalar<G1, G2>, N: 2>
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
    use ark_ec::CurveGroup;
    use ark_ff::Field;
    use ark_std::UniformRand;
    use backend::{ATyp, ArkBls12_381, ArkConfig, Value};
    use lang::id::{Tid, Vid};
    use share::Ctx;
    use std::io::Write;
    use std::path::PathBuf;
    use std::time::Instant;
    use tempfile::NamedTempFile;
    use zippel::{ZippelArgs, ZippelHandler, check_verification};

    pub struct Setup {
        handler: ZippelHandler<ArkBls12_381>,
        n: usize,
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

            Setup {
                handler,
                n,
                _source_file,
            }
        }

        pub fn time_protocol(&mut self) -> Timing {
            type F = <ArkBls12_381 as ArkConfig>::F;
            type G1 = <ArkBls12_381 as ArkConfig>::G1;
            type G2 = <ArkBls12_381 as ArkConfig>::G2;

            let mut rng = rand::rngs::OsRng;
            let n = self.n;

            let g_input = G1::rand(&mut rng);
            let g = Value::G1(g_input);
            let h_input = G2::rand(&mut rng);
            let h = Value::G2(h_input);

            let p = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n));
            let z = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
            let tau_input = F::rand(&mut rng);

            // Build the SRS in projective once, then batch-normalize to
            // affine via Montgomery's trick (one inversion + 3(N-1) muls).
            // Native KZG10 produces its SRS in affine form via the same
            // np_ark_ec batch path; feeding zippel a projective vector would
            // trigger an N-inversion fallback at the MSM call site
            // (backend/src/values.rs:1552-1559). Match the input shape so
            // the comparison isn't penalizing zippel for input format.
            let srs_proj: Vec<G1> = (0..n)
                .map(|i| g_input * tau_input.pow([i as u64]))
                .collect();
            let srs_affine = <G1 as CurveGroup>::normalize_batch(&srs_proj);
            let ss = Value::VecG1Affine(srs_affine);

            let z_val: Value<ArkBls12_381> =
                Value::Vec((0..n).map(|i| z.clone() ^ Value::Index(i)).collect());
            let y = p.clone().dot(z_val);
            let h_val = Value::G2(h_input * tau_input);

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
            let t = Instant::now();
            let proof = self
                .handler
                .run_prover(prover_scheduled, inputs)
                .expect("run_prover failed");
            let prove = t.elapsed();

            let verifier_scheduled = self.handler.default_schedule_verifier();
            let t = Instant::now();
            let verifier_result = self
                .handler
                .run_verifier(verifier_scheduled, proof)
                .expect("run_verifier failed");
            let verify = t.elapsed();

            let result = check_verification(verifier_result);
            assert!(result.passed, "zippel KZG verification FAILED");

            Timing { prove, verify }
        }
    }
}

pub mod native_side {
    use super::*;
    use np_ark_bls12_381::Bls12_381;
    use np_ark_ff::UniformRand;
    use np_ark_poly::{DenseUVPolynomial, Polynomial, univariate::DensePolynomial};
    use np_ark_poly_commit::kzg10::{KZG10, Powers, UniversalParams, VerifierKey};
    use std::borrow::Cow;
    use std::time::Instant;

    type Kzg =
        KZG10<Bls12_381, DensePolynomial<<Bls12_381 as np_ark_ec::pairing::Pairing>::ScalarField>>;
    type Fr = <Bls12_381 as np_ark_ec::pairing::Pairing>::ScalarField;

    pub struct Setup {
        powers: PowersOwned,
        vk: VerifierKey<Bls12_381>,
        n: usize,
    }

    /// Owned analog of `Powers<'_, E>` — `Powers` borrows its slices, but
    /// we need to keep the data alive across iterations.
    struct PowersOwned {
        powers_of_g: Vec<<Bls12_381 as np_ark_ec::pairing::Pairing>::G1Affine>,
        powers_of_gamma_g: Vec<<Bls12_381 as np_ark_ec::pairing::Pairing>::G1Affine>,
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
            let mut rng = ark_std::test_rng();
            // n coefficients => degree n-1
            let degree = n - 1;
            let pp = Kzg::setup(degree, false, &mut rng).expect("kzg setup");
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
            let t = Instant::now();
            let (comm, rand) =
                Kzg::commit(&self.powers.as_powers(), &poly, None, None).expect("kzg commit");
            let proof = Kzg::open(&self.powers.as_powers(), &poly, point, &rand).expect("kzg open");
            let prove = t.elapsed();

            let t = Instant::now();
            let ok = Kzg::check(&self.vk, &comm, point, value, &proof).expect("kzg check");
            let verify = t.elapsed();

            assert!(ok, "ark-poly-commit KZG verification FAILED");

            Timing { prove, verify }
        }
    }
}
