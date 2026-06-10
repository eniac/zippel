//! Sumcheck comparison: zippel-compiled sumcheck vs. Espresso hyperplonk's
//! `subroutines::poly_iop::sum_check`.
//!
//! Both sides run the same protocol shape — sum over {0,1}^num_vars of
//! base(x)^max_degree where base is a random dense MLE — and report
//! pure prover and verifier wall-time (no input construction, no compile).
//!
//! Sizes are bound via `sizes.insert("NUM_VARS_CONST", n)` /
//! `sizes.insert("MAX_DEGREE_CONST", d)` at compile time. The .zippel's
//! recursive helper uses `V: 2..NUM_VARS_CONST` so V's upper bound
//! follows NUM_VARS_CONST automatically.

use crate::Timing;
use backend::OptimizationStats;

pub const DEFAULT_NUM_VARS: usize = 10;
pub const DEFAULT_MAX_DEGREE: usize = 10;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ZippelCorrectnessObservation {
    /// Deterministic digest of the Zippel-side benchmark input description.
    pub input_digest: String,
    /// Digest of the canonical Zippel proof value stream returned by the prover.
    pub proof_digest: String,
    /// Digest of verifier outputs plus the derived pass/fail observation.
    pub verifier_result_digest: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeCorrectnessObservation {
    /// Deterministic digest of the native HyperPlonk-side benchmark input description.
    pub input_digest: String,
    /// Digest of the native sumcheck subclaim point and expected evaluation.
    pub subclaim_digest: String,
}

#[derive(Debug, Clone)]
pub struct TimedProtocolRun<O> {
    pub timing: Timing,
    pub observation: O,
    pub optimizer: Option<OptimizationStats>,
}

pub type ZippelTimedRun = TimedProtocolRun<ZippelCorrectnessObservation>;
pub type NativeTimedRun = TimedProtocolRun<NativeCorrectnessObservation>;

pub mod zippel_side {
    use super::*;
    use ark_ff::Zero;
    use ark_poly::DenseMultilinearExtension;
    use ark_std::UniformRand;
    use backend::poly_variant::PolyVariant;
    use backend::{ArkBls12_381, ArkConfig, Value, VirtualPolynomial, value_to_bytes};
    use lang::id::{Tid, Vid};
    use rand::{SeedableRng, rngs::StdRng};
    use sha2::{Digest, Sha256};
    use share::Ctx;
    use std::path::{Path, PathBuf};
    use std::time::Instant;
    use zippel::{ZippelArgs, ZippelHandler, check_verification};

    pub struct Setup {
        handler: ZippelHandler<ArkBls12_381>,
        num_vars: usize,
        max_degree: usize,
    }

    impl Setup {
        pub fn new(num_vars: usize, max_degree: usize) -> Self {
            Self::new_with_source(
                num_vars,
                max_degree,
                Path::new("examples/sumcheck/sumcheck.zippel"),
            )
        }

        pub fn new_with_source(
            num_vars: usize,
            max_degree: usize,
            source_path: impl AsRef<Path>,
        ) -> Self {
            let args = ZippelArgs::new(PathBuf::from(source_path.as_ref()));
            Self::new_with_args(num_vars, max_degree, args)
        }

        pub fn new_with_source_identity(
            num_vars: usize,
            max_degree: usize,
            source_path: impl AsRef<Path>,
            domain_separator_session: impl AsRef<str>,
        ) -> Self {
            let args = ZippelArgs::new_with_domain_session(
                PathBuf::from(source_path.as_ref()),
                domain_separator_session.as_ref().to_string(),
            );
            Self::new_with_args(num_vars, max_degree, args)
        }

        fn new_with_args(num_vars: usize, max_degree: usize, args: ZippelArgs) -> Self {
            let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
            let mut sizes = Ctx::new();
            sizes.insert(&Tid::new("NUM_VARS_CONST"), &num_vars);
            sizes.insert(&Tid::new("MAX_DEGREE_CONST"), &max_degree);
            handler.compile(&sizes);

            Setup {
                handler,
                num_vars,
                max_degree,
            }
        }

        pub fn time_protocol(&mut self) -> Timing {
            self.run_protocol_with_rng(&mut rand::rngs::OsRng).timing
        }

        pub fn time_protocol_with_seed(&mut self, seed: u64) -> Timing {
            self.run_protocol_with_seed(seed).timing
        }

        pub fn run_protocol_with_seed(&mut self, seed: u64) -> ZippelTimedRun {
            let mut rng = StdRng::seed_from_u64(seed);
            self.run_protocol_with_rng(&mut rng)
        }

        fn run_protocol_with_rng<R: rand::Rng + ?Sized>(&mut self, rng: &mut R) -> ZippelTimedRun {
            type F = <ArkBls12_381 as ArkConfig>::F;
            let nv = self.num_vars;
            let md = self.max_degree;
            let eval_count = 1usize << nv;
            let base_evals: Vec<F> = (0..eval_count).map(|_| F::rand(rng)).collect();
            let claimed_sum: F = base_evals
                .iter()
                .map(|x| (0..md).fold(F::from(1u64), |acc, _| acc * *x))
                .fold(F::zero(), |acc, v| acc + v);
            let input_digest = input_digest(nv, md, &claimed_sum, &base_evals);
            let base = VirtualPolynomial::from_poly(PolyVariant::DenseMle(
                DenseMultilinearExtension::from_evaluations_vec(nv, base_evals),
            ));
            let mut full_poly = base.clone();
            for _ in 1..md {
                full_poly = full_poly.poly_mul(&base).expect("poly_mul");
            }
            let inputs = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
                (Vid("claimed_sum".to_string()), Value::Scalar(claimed_sum)),
                (Vid("poly".to_string()), Value::Poly(full_poly)),
            ]);

            let optimizer_before = backend::optimization_stats_snapshot();

            let prover_scheduled = self.handler.default_schedule_prover();
            let t = Instant::now();
            let proof = self
                .handler
                .run_prover(prover_scheduled, inputs)
                .expect("run_prover failed");
            let prove = t.elapsed();
            let proof_digest = value_stream_digest("zippel.sumcheck.proof.v1", &proof);

            let verifier_scheduled = self.handler.default_schedule_verifier();
            let t = Instant::now();
            let verifier_result = self
                .handler
                .run_verifier(verifier_scheduled, proof)
                .expect("run_verifier failed");
            let verify = t.elapsed();
            let optimizer = backend::optimization_stats_snapshot().delta_since(optimizer_before);

            let result = check_verification(verifier_result.clone());
            let verifier_result_digest = verifier_result_digest(
                "zippel.sumcheck.verifier_result.v1",
                &verifier_result,
                result.passed,
            );
            assert!(result.passed, "zippel sumcheck verification FAILED");

            ZippelTimedRun {
                timing: Timing { prove, verify },
                observation: ZippelCorrectnessObservation {
                    input_digest,
                    proof_digest,
                    verifier_result_digest,
                },
                optimizer: Some(optimizer),
            }
        }
    }

    fn input_digest(
        num_vars: usize,
        max_degree: usize,
        claimed_sum: &<ArkBls12_381 as ArkConfig>::F,
        base_evals: &[<ArkBls12_381 as ArkConfig>::F],
    ) -> String {
        let mut hasher = tagged_hasher("zippel.sumcheck.input.v1");
        update_usize(&mut hasher, "num_vars", num_vars);
        update_usize(&mut hasher, "max_degree", max_degree);
        update_usize(&mut hasher, "base_eval_count", base_evals.len());
        update_value(&mut hasher, &Value::<ArkBls12_381>::Scalar(*claimed_sum));
        for value in base_evals {
            update_value(&mut hasher, &Value::<ArkBls12_381>::Scalar(*value));
        }
        finish_digest(hasher)
    }

    fn value_stream_digest(domain: &str, values: &[Value<ArkBls12_381>]) -> String {
        let mut hasher = tagged_hasher(domain);
        update_usize(&mut hasher, "value_count", values.len());
        for (index, value) in values.iter().enumerate() {
            update_usize(&mut hasher, "value_index", index);
            update_value(&mut hasher, value);
        }
        finish_digest(hasher)
    }

    fn verifier_result_digest(
        domain: &str,
        values: &[Value<ArkBls12_381>],
        passed: bool,
    ) -> String {
        let mut hasher = tagged_hasher(domain);
        hasher.update(b"passed");
        hasher.update([u8::from(passed)]);
        update_usize(&mut hasher, "value_count", values.len());
        for (index, value) in values.iter().enumerate() {
            update_usize(&mut hasher, "value_index", index);
            update_value(&mut hasher, value);
        }
        finish_digest(hasher)
    }

    fn tagged_hasher(domain: &str) -> Sha256 {
        let mut hasher = Sha256::new();
        hasher.update(domain.as_bytes());
        hasher.update([0]);
        hasher
    }

    fn update_usize(hasher: &mut Sha256, label: &str, value: usize) {
        hasher.update(label.as_bytes());
        hasher.update([0]);
        hasher.update((value as u64).to_le_bytes());
    }

    fn update_value(hasher: &mut Sha256, value: &Value<ArkBls12_381>) {
        let bytes = value_to_bytes(value).expect("Zippel value serialization for digest failed");
        update_usize(hasher, "value_len", bytes.len());
        hasher.update(&bytes);
    }

    fn finish_digest(hasher: Sha256) -> String {
        format!("sha256:{:x}", hasher.finalize())
    }
}

pub mod native_side {
    use super::*;
    use arithmetic::VirtualPolynomial;
    use bp_ark_serialize::CanonicalSerialize;
    use hp_ark_bls12_381::Fr;
    use hp_ark_ff::{One, UniformRand, Zero};
    use hp_ark_poly::DenseMultilinearExtension;
    use rand::{SeedableRng, rngs::StdRng};
    use sha2::{Digest, Sha256};
    use std::sync::Arc;
    use std::time::Instant;
    use subroutines::{PolyIOP, SumCheck};

    pub struct Setup {
        num_vars: usize,
        max_degree: usize,
    }

    impl Setup {
        pub fn new(num_vars: usize, max_degree: usize) -> Self {
            Setup {
                num_vars,
                max_degree,
            }
        }

        pub fn time_protocol(&self) -> Timing {
            self.run_protocol_with_rng(&mut hp_ark_std::test_rng())
                .timing
        }

        pub fn time_protocol_with_seed(&self, seed: u64) -> Timing {
            self.run_protocol_with_seed(seed).timing
        }

        pub fn run_protocol_with_seed(&self, seed: u64) -> NativeTimedRun {
            let mut rng = StdRng::seed_from_u64(seed);
            self.run_protocol_with_rng(&mut rng)
        }

        fn run_protocol_with_rng<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> NativeTimedRun {
            let nv = self.num_vars;
            let md = self.max_degree;
            let eval_count = 1usize << nv;
            let evals: Vec<Fr> = (0..eval_count).map(|_| Fr::rand(rng)).collect();
            let claimed_sum: Fr = evals
                .iter()
                .map(|x| (0..md).fold(Fr::one(), |acc, _| acc * x))
                .fold(Fr::zero(), |acc, v| acc + v);
            let input_digest = input_digest(nv, md, &claimed_sum, &evals);

            let mle = Arc::new(DenseMultilinearExtension::from_evaluations_vec(nv, evals));
            let mut poly = VirtualPolynomial::new(nv);
            poly.add_mle_list(vec![mle.clone(); md], Fr::one())
                .expect("add_mle_list");

            let mut transcript = <PolyIOP<Fr> as SumCheck<Fr>>::init_transcript();
            let t = Instant::now();
            let proof = <PolyIOP<Fr> as SumCheck<Fr>>::prove(&poly, &mut transcript)
                .expect("hyperplonk prove failed");
            let prove = t.elapsed();

            let aux = poly.aux_info.clone();
            let mut transcript = <PolyIOP<Fr> as SumCheck<Fr>>::init_transcript();
            let t = Instant::now();
            let subclaim =
                <PolyIOP<Fr> as SumCheck<Fr>>::verify(claimed_sum, &proof, &aux, &mut transcript)
                    .expect("hyperplonk verify failed");
            let verify = t.elapsed();

            // Subclaim opening (the final O(2^NV) poly eval) is
            // deliberately outside the timer — in a real SNARK it would
            // be a polynomial commitment opening, not a direct eval.
            // sumcheck.zippel matches by having the prover send the
            // evaluation (from_orig <- eval(...)) so the zippel verifier
            // also doesn't time the eval. Both sides now time pure IOP
            // work. The assert below still validates correctness.
            let lhs = poly.evaluate(&subclaim.point).expect("evaluate");
            assert_eq!(
                lhs, subclaim.expected_evaluation,
                "hyperplonk sumcheck subclaim mismatch"
            );
            let subclaim_digest = subclaim_digest(&subclaim.point, &subclaim.expected_evaluation);

            NativeTimedRun {
                timing: Timing { prove, verify },
                observation: NativeCorrectnessObservation {
                    input_digest,
                    subclaim_digest,
                },
                optimizer: None,
            }
        }
    }

    fn input_digest(num_vars: usize, max_degree: usize, claimed_sum: &Fr, evals: &[Fr]) -> String {
        let mut hasher = tagged_hasher("native.hyperplonk.sumcheck.input.v1");
        update_usize(&mut hasher, "num_vars", num_vars);
        update_usize(&mut hasher, "max_degree", max_degree);
        update_usize(&mut hasher, "eval_count", evals.len());
        update_field(&mut hasher, claimed_sum);
        for value in evals {
            update_field(&mut hasher, value);
        }
        finish_digest(hasher)
    }

    fn subclaim_digest(point: &[Fr], expected_evaluation: &Fr) -> String {
        let mut hasher = tagged_hasher("native.hyperplonk.sumcheck.subclaim.v1");
        update_usize(&mut hasher, "point_len", point.len());
        for value in point {
            update_field(&mut hasher, value);
        }
        update_field(&mut hasher, expected_evaluation);
        finish_digest(hasher)
    }

    fn tagged_hasher(domain: &str) -> Sha256 {
        let mut hasher = Sha256::new();
        hasher.update(domain.as_bytes());
        hasher.update([0]);
        hasher
    }

    fn update_usize(hasher: &mut Sha256, label: &str, value: usize) {
        hasher.update(label.as_bytes());
        hasher.update([0]);
        hasher.update((value as u64).to_le_bytes());
    }

    fn update_field(hasher: &mut Sha256, value: &Fr) {
        let mut bytes = Vec::new();
        value
            .serialize_compressed(&mut bytes)
            .expect("native field serialization for digest failed");
        update_usize(hasher, "field_len", bytes.len());
        hasher.update(&bytes);
    }

    fn finish_digest(hasher: Sha256) -> String {
        format!("sha256:{:x}", hasher.finalize())
    }
}
