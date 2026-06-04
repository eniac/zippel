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

// ---------------------------------------------------------------------------
// Byte-bridge between native (`np_ark_*`) and zippel (`ark_*`) BLS12-381
// types — same curve, different arkworks versions. Both sides canonical-
// serialize the same way (compressed form, fixed length per type), so the
// round-trip through bytes is byte-faithful.
//
// Used by the cross-verification tests at the bottom of this file.
// ---------------------------------------------------------------------------
#[cfg(test)]
pub(crate) mod bridge {
    use ark_bls12_381::{
        Fr as ZipFr, G1Affine as ZipG1Aff, G1Projective as ZipG1Proj, G2Affine as ZipG2Aff,
        G2Projective as ZipG2Proj,
    };
    use ark_ec::{AffineRepr as _, CurveGroup as _};
    use ark_serialize::{CanonicalDeserialize as ZipDeser, CanonicalSerialize as ZipSer};
    use np_ark_bls12_381::Bls12_381 as NpE;
    use np_ark_ec::pairing::Pairing as NpPairing;
    use np_ark_serialize::{CanonicalDeserialize as NpDeser, CanonicalSerialize as NpSer};

    pub type NpFr = <NpE as NpPairing>::ScalarField;
    pub type NpG1Aff = <NpE as NpPairing>::G1Affine;
    pub type NpG2Aff = <NpE as NpPairing>::G2Affine;

    pub fn np_fr_to_zip(x: &NpFr) -> ZipFr {
        let mut bytes = Vec::with_capacity(32);
        NpSer::serialize_compressed(x, &mut bytes).expect("ser np fr");
        ZipDeser::deserialize_compressed(&bytes[..]).expect("deser zip fr")
    }

    pub fn np_g1_aff_to_zip_proj(p: &NpG1Aff) -> ZipG1Proj {
        let mut bytes = Vec::with_capacity(48);
        NpSer::serialize_compressed(p, &mut bytes).expect("ser np g1");
        let aff: ZipG1Aff = ZipDeser::deserialize_compressed(&bytes[..]).expect("deser zip g1");
        aff.into_group()
    }

    pub fn np_g1_aff_to_zip_aff(p: &NpG1Aff) -> ZipG1Aff {
        let mut bytes = Vec::with_capacity(48);
        NpSer::serialize_compressed(p, &mut bytes).expect("ser np g1");
        ZipDeser::deserialize_compressed(&bytes[..]).expect("deser zip g1")
    }

    pub fn np_g2_aff_to_zip_proj(p: &NpG2Aff) -> ZipG2Proj {
        let mut bytes = Vec::with_capacity(96);
        NpSer::serialize_compressed(p, &mut bytes).expect("ser np g2");
        let aff: ZipG2Aff = ZipDeser::deserialize_compressed(&bytes[..]).expect("deser zip g2");
        aff.into_group()
    }

    pub fn zip_g1_proj_to_np_aff(p: &ZipG1Proj) -> NpG1Aff {
        let aff = p.into_affine();
        let mut bytes = Vec::with_capacity(48);
        ZipSer::serialize_compressed(&aff, &mut bytes).expect("ser zip g1");
        NpDeser::deserialize_compressed(&bytes[..]).expect("deser np g1")
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

// ---------------------------------------------------------------------------
// Cross-verification tests: confirm that zippel and native compute the same
// KZG protocol bit-for-bit, by having each side verify the other's proof
// against shared SRS + inputs. If either test fails, the benchmark is not
// measuring the same protocol on both sides and the comparison is invalid.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod cross_tests {
    use super::bridge::{
        NpFr, NpG1Aff, np_fr_to_zip, np_g1_aff_to_zip_aff, np_g1_aff_to_zip_proj,
        np_g2_aff_to_zip_proj, zip_g1_proj_to_np_aff,
    };
    use ark_bls12_381::Fr as ZipFr;
    use ark_ec::CurveGroup as _;
    use backend::{ArkBls12_381, ArkConfig, Value};
    use lang::id::{Tid, Vid};
    use np_ark_bls12_381::Bls12_381 as NpE;
    use np_ark_ec::pairing::Pairing as NpPairing;
    use np_ark_ff::UniformRand;
    use np_ark_poly::{DenseUVPolynomial, Polynomial, univariate::DensePolynomial};
    use np_ark_poly_commit::kzg10::{
        Commitment, KZG10, Powers, Proof, UniversalParams, VerifierKey,
    };
    use share::Ctx;
    use std::borrow::Cow;
    use std::path::PathBuf;
    use zippel::{ZippelArgs, ZippelHandler, check_verification};

    type Kzg = KZG10<NpE, DensePolynomial<NpFr>>;
    type NpG1 = <NpE as NpPairing>::G1;
    type ZipG1Proj = <ArkBls12_381 as ArkConfig>::G1;
    type ZipG1Aff = ark_bls12_381::G1Affine;

    /// Shared world: identical SRS + poly + eval point used by both tests.
    /// We seed the RNG deterministically so test runs are reproducible.
    struct World {
        pp: UniversalParams<NpE>,
        poly: DensePolynomial<NpFr>,
        point: NpFr,
        value: NpFr,
        n: usize,
    }

    fn build_world(n: usize) -> World {
        use ark_std::rand::SeedableRng;
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(0xC0FFEE_u64 ^ n as u64);
        let degree = n - 1;
        let pp = Kzg::setup(degree, false, &mut rng).expect("kzg setup");
        let poly = DensePolynomial::<NpFr>::rand(degree, &mut rng);
        let point = NpFr::rand(&mut rng);
        let value = poly.evaluate(&point);
        World {
            pp,
            poly,
            point,
            value,
            n,
        }
    }

    fn build_powers_owned(pp: &UniversalParams<NpE>, degree: usize) -> (Vec<NpG1Aff>, Vec<NpG1Aff>) {
        let powers_of_g = pp.powers_of_g[..=degree].to_vec();
        let powers_of_gamma_g = (0..=degree)
            .map(|i| pp.powers_of_gamma_g[&i])
            .collect::<Vec<_>>();
        (powers_of_g, powers_of_gamma_g)
    }

    fn build_vk(pp: &UniversalParams<NpE>) -> VerifierKey<NpE> {
        VerifierKey {
            g: pp.powers_of_g[0],
            gamma_g: pp.powers_of_gamma_g[&0],
            h: pp.h,
            beta_h: pp.beta_h,
            prepared_h: pp.prepared_h.clone(),
            prepared_beta_h: pp.prepared_beta_h.clone(),
        }
    }

    /// Build the zippel-side input context from the shared world, with all
    /// curve/field values bridged from `np_ark_*` to `ark_*`.
    fn zip_inputs_from_world(world: &World) -> Ctx<Vid, Value<ArkBls12_381>> {
        let poly_coeffs_zip: Vec<ZipFr> = world.poly.coeffs.iter().map(np_fr_to_zip).collect();
        let eval_point_zip = np_fr_to_zip(&world.point);
        let eval_result_zip = np_fr_to_zip(&world.value);
        let srs_g1_zip: Vec<ZipG1Aff> = world.pp.powers_of_g[..world.n]
            .iter()
            .map(np_g1_aff_to_zip_aff)
            .collect();
        let gen_g1_zip = np_g1_aff_to_zip_proj(&world.pp.powers_of_g[0]);
        let gen_g2_zip = np_g2_aff_to_zip_proj(&world.pp.h);
        let srs_g2_s_zip = np_g2_aff_to_zip_proj(&world.pp.beta_h);

        Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
            (
                Vid("poly_coeffs".to_string()),
                Value::VecScalar(poly_coeffs_zip),
            ),
            (Vid("gen_g1".to_string()), Value::G1(gen_g1_zip)),
            (Vid("gen_g2".to_string()), Value::G2(gen_g2_zip)),
            (Vid("eval_point".to_string()), Value::Scalar(eval_point_zip)),
            (Vid("eval_result".to_string()), Value::Scalar(eval_result_zip)),
            (Vid("srs_g1".to_string()), Value::VecG1Affine(srs_g1_zip)),
            (Vid("srs_g2_s".to_string()), Value::G2(srs_g2_s_zip)),
        ])
    }

    fn zippel_handler(n: usize) -> ZippelHandler<ArkBls12_381> {
        // benchmarks/ runs its tests from its own crate dir, so the .zippel
        // path needs to walk up to the workspace root.
        let zippel_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join("examples/kzg/kzg.zippel");
        let args = ZippelArgs::new(zippel_path);
        let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("N"), &n);
        handler.compile(&sizes);
        handler
    }

    /// Sweep used by both cross-tests. Capped at N=16 (well below 20) so
    /// test wall-clock stays under a minute per direction.
    const SWEEP: &[usize] = &[2, 4, 8, 16];

    /// Test 1: native side produces commit + opening proof; zippel side
    /// runs its verifier against the bridged proof. Additionally asserts
    /// that zippel's own commit and proof are byte-identical to native's
    /// (after bridging) — the strongest "we compute the same thing" check.
    #[test]
    fn native_prove_then_zippel_verify() {
        for &n in SWEEP {
            run_native_prove_zippel_verify(n);
        }
    }

    fn run_native_prove_zippel_verify(n: usize) {
        let world = build_world(n);

        // ---- Native: commit + open ---------------------------------------
        let (powers_of_g, powers_of_gamma_g) = build_powers_owned(&world.pp, n - 1);
        let powers = Powers::<NpE> {
            powers_of_g: Cow::Borrowed(&powers_of_g),
            powers_of_gamma_g: Cow::Borrowed(&powers_of_gamma_g),
        };
        let (comm_n, rand) =
            Kzg::commit(&powers, &world.poly, None, None).expect("native commit");
        let proof_n = Kzg::open(&powers, &world.poly, world.point, &rand).expect("native open");

        // ---- Zippel: run_prover to capture state; also use its proof for
        //      the byte-equality sanity check below -----------------------
        let mut handler = zippel_handler(n);
        let zip_inputs = zip_inputs_from_world(&world);
        let prover_sched = handler.default_schedule_prover();
        let zip_proof: Vec<Value<ArkBls12_381>> = handler
            .run_prover(prover_sched, zip_inputs)
            .expect("zippel run_prover");

        // Zippel transcript is [commitment, proof] in `<-` order.
        assert_eq!(zip_proof.len(), 2, "expected 2 transcript items");
        let zip_comm = match &zip_proof[0] {
            Value::G1(g) => *g,
            other => panic!("expected G1 commitment, got {:?}", format!("{:?}", std::mem::discriminant(other))),
        };
        let zip_proof_g = match &zip_proof[1] {
            Value::G1(g) => *g,
            other => panic!("expected G1 proof, got {:?}", format!("{:?}", std::mem::discriminant(other))),
        };

        // ---- Byte-equality assertion: zippel's commit + proof MUST equal
        //      native's (after bridging) -----------------------------------
        let zip_comm_as_np = zip_g1_proj_to_np_aff(&zip_comm);
        let zip_proof_as_np = zip_g1_proj_to_np_aff(&zip_proof_g);
        assert_eq!(
            zip_comm_as_np, comm_n.0,
            "N={n}: zippel commit != native commit (bridged) — protocols diverge!"
        );
        assert_eq!(
            zip_proof_as_np, proof_n.w,
            "N={n}: zippel proof != native proof (bridged) — protocols diverge!"
        );

        // ---- Cross-verify: feed NATIVE-produced (commit, proof) into the
        //      zippel verifier graph as the transcript. The zippel verifier
        //      should accept since (by the byte-eq above) it computes the
        //      same pairing equation against bit-identical inputs. --------
        let cross_proof: Vec<Value<ArkBls12_381>> = vec![
            Value::G1(np_g1_aff_to_zip_proj(&comm_n.0)),
            Value::G1(np_g1_aff_to_zip_proj(&proof_n.w)),
        ];
        let verifier_sched = handler.default_schedule_verifier();
        let verifier_result = handler
            .run_verifier(verifier_sched, cross_proof)
            .expect("zippel run_verifier on cross-proof");
        let result = check_verification(verifier_result);
        assert!(
            result.passed,
            "N={n}: CROSS-VERIFY FAILED: zippel verifier rejected native-produced proof"
        );
    }

    /// Test 2: zippel side produces commit + opening proof (via run_prover);
    /// native side runs its verifier (`Kzg::check`) against the bridged
    /// (commitment, proof). Confirms the OTHER direction is also bit-exact.
    #[test]
    fn zippel_prove_then_native_verify() {
        for &n in SWEEP {
            run_zippel_prove_native_verify(n);
        }
    }

    fn run_zippel_prove_native_verify(n: usize) {
        let world = build_world(n);

        // ---- Zippel: run_prover to produce commit + open ------------------
        let mut handler = zippel_handler(n);
        let zip_inputs = zip_inputs_from_world(&world);
        let prover_sched = handler.default_schedule_prover();
        let zip_proof: Vec<Value<ArkBls12_381>> = handler
            .run_prover(prover_sched, zip_inputs)
            .expect("zippel run_prover");

        assert_eq!(zip_proof.len(), 2, "expected 2 transcript items");
        let zip_comm = match &zip_proof[0] {
            Value::G1(g) => *g,
            other => panic!("expected G1 commitment, got {:?}", format!("{:?}", std::mem::discriminant(other))),
        };
        let zip_proof_g = match &zip_proof[1] {
            Value::G1(g) => *g,
            other => panic!("expected G1 proof, got {:?}", format!("{:?}", std::mem::discriminant(other))),
        };

        // ---- Bridge zippel's (commitment, proof) into native types --------
        let comm_np = Commitment::<NpE>(zip_g1_proj_to_np_aff(&zip_comm));
        let proof_np = Proof::<NpE> {
            w: zip_g1_proj_to_np_aff(&zip_proof_g),
            random_v: None,
        };

        // ---- Native: verify the zippel-produced proof ---------------------
        let vk = build_vk(&world.pp);
        let ok = Kzg::check(&vk, &comm_np, world.point, world.value, &proof_np)
            .expect("native Kzg::check call");
        assert!(
            ok,
            "N={n}: CROSS-VERIFY FAILED: native verifier rejected zippel-produced proof"
        );
    }
}
