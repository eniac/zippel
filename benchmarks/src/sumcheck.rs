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

/// Default number of MLE variables (`NUM_VARS_CONST`) when the caller does
/// not sweep a size; the summation domain is `{0,1}^NUM_VARS`.
pub const DEFAULT_NUM_VARS: usize = 10;
/// Default power (`MAX_DEGREE_CONST`) the base MLE is raised to, i.e. the
/// per-round degree of the sumcheck univariate messages.
pub const DEFAULT_MAX_DEGREE: usize = 10;

/// Zippel half: compiles `examples/sumcheck/sumcheck.zippel` and times its
/// generated prover and verifier.
pub mod zippel_side {
    use super::*;
    use ark_ff::Zero;
    use ark_poly::DenseMultilinearExtension;
    use ark_std::UniformRand;
    use backend::poly_variant::PolyVariant;
    use backend::{ArkBls12_381, ArkConfig, Value, VirtualPolynomial};
    use lang::id::{Tid, Vid};
    use share::Ctx;
    use std::path::PathBuf;
    use std::time::Instant;
    use zippel::{ZippelArgs, ZippelHandler, check_verification};

    /// A compiled sumcheck instance, reusable across `time_protocol` calls.
    ///
    /// Holds the `ZippelHandler` (which owns the compiled prover/verifier
    /// graphs), the two size parameters bound at compile time, and how long
    /// compilation took.
    pub struct Setup {
        handler: ZippelHandler<ArkBls12_381>,
        num_vars: usize,
        max_degree: usize,
        compile_time: std::time::Duration,
    }

    impl Setup {
        /// Compiles the sumcheck protocol with `NUM_VARS_CONST = num_vars`
        /// and `MAX_DEGREE_CONST = max_degree` bound as concrete sizes.
        ///
        /// The compile is timed; execution inputs are sampled later, per
        /// `time_protocol` call.
        ///
        /// # Panics
        /// Panics if the `.zippel` source cannot be read, parsed, type
        /// checked, or lowered to a graph for these sizes.
        pub fn new(num_vars: usize, max_degree: usize) -> Self {
            let compile_start = Instant::now();
            let args = ZippelArgs::new(PathBuf::from("examples/sumcheck/sumcheck.zippel"));
            let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
            let mut sizes = Ctx::new();
            sizes.insert(&Tid::new("NUM_VARS_CONST"), &num_vars);
            sizes.insert(&Tid::new("MAX_DEGREE_CONST"), &max_degree);
            handler.compile(&sizes);
            let compile_time = compile_start.elapsed();

            Setup {
                handler,
                num_vars,
                max_degree,
                compile_time,
            }
        }

        /// Wall-time spent in `ZippelHandler::compile` for this instance:
        /// parsing, type checking, and graph construction only.
        pub fn compile_time(&self) -> std::time::Duration {
            self.compile_time
        }

        /// (prover graph node count, verifier graph node count).
        pub fn graph_sizes(&self) -> (usize, usize) {
            (
                self.handler.prover_graph().node_count(),
                self.handler.verifier_graph().node_count(),
            )
        }

        /// Samples a random base MLE, runs the compiled prover and verifier,
        /// and returns their mean wall-times.
        ///
        /// The claimed sum is computed directly from the evaluation table, and
        /// the summand polynomial is the base MLE multiplied by itself
        /// `max_degree` times.
        ///
        /// # Panics
        /// Panics if the polynomial product cannot be formed, if the prover or
        /// verifier graph fails to execute, or if the verifier rejects the
        /// honestly generated proof.
        pub fn time_protocol(&mut self) -> Timing {
            type F = <ArkBls12_381 as ArkConfig>::F;
            let nv = self.num_vars;
            let md = self.max_degree;
            let eval_count = 1usize << nv;
            let mut rng = rand::rngs::OsRng;
            let base_evals: Vec<F> = (0..eval_count).map(|_| F::rand(&mut rng)).collect();
            let claimed_sum: F = base_evals
                .iter()
                .map(|x| (0..md).fold(F::from(1u64), |acc, _| acc * *x))
                .fold(F::zero(), |acc, v| acc + v);
            let base = VirtualPolynomial::from_poly(PolyVariant::DenseMle(
                DenseMultilinearExtension::from_evaluations_vec(nv, base_evals),
            ));
            let mut full_poly = base.clone();
            for _ in 1..md {
                full_poly = full_poly.poly_mul(&base).expect("poly_mul");
            }
            let inputs = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
                (Vid("claimed_sum".to_string()), Value::Scalar(claimed_sum)),
                (Vid("p".to_string()), Value::Poly(full_poly)),
            ]);
            let mut prove_sum = std::time::Duration::ZERO;
            let mut last_proof = None;
            for _ in 0..*crate::PROVER_SAMPLES {
                let inputs_c = inputs.clone();
                let t = Instant::now();
                let proof = self
                    .handler
                    .run_prover(&inputs_c)
                    .expect("run_prover failed");
                prove_sum += t.elapsed();
                last_proof = Some(proof);
            }
            let prove = prove_sum / *crate::PROVER_SAMPLES;
            let proof = last_proof.expect("PROVER_SAMPLES > 0");
            let mut verify_sum = std::time::Duration::ZERO;
            let mut last_result = None;
            for _ in 0..crate::VERIFY_SAMPLES {
                let proof_c = proof.clone();
                let t = Instant::now();
                let verifier_result = self
                    .handler
                    .run_verifier(&proof_c, &inputs)
                    .expect("run_verifier failed");
                verify_sum += t.elapsed();
                last_result = Some(verifier_result);
            }
            let verify = verify_sum / crate::VERIFY_SAMPLES;

            let result = check_verification(&last_result.expect("VERIFY_SAMPLES > 0"));
            assert!(result, "zippel sumcheck verification FAILED");

            Timing { prove, verify }
        }
    }
}

/// Native sumcheck baseline: hyperplonk's `poly_iop::sum_check`,
/// vendored in-tree under `crate::sumcheck_upstream` and ported to
/// arkworks 0.6 so it shares the zippel-side curve set. Protocol code
/// verbatim from EspressoSystems/hyperplonk `main`; only `use` paths
/// changed.
pub mod native_side {
    use super::*;
    use crate::sumcheck_upstream::arithmetic::VirtualPolynomial;
    use crate::sumcheck_upstream::poly_iop::{PolyIOP, SumCheck};
    use ark_bls12_381::Fr;
    use ark_ff::{One, UniformRand, Zero};
    use ark_poly::DenseMultilinearExtension;
    use std::sync::Arc;
    use std::time::Instant;

    /// The native sumcheck parameters; there is no setup phase to amortize,
    /// so this only records the instance size.
    pub struct Setup {
        num_vars: usize,
        max_degree: usize,
    }

    impl Setup {
        /// Records the instance size; hyperplonk's sumcheck needs no setup.
        pub fn new(num_vars: usize, max_degree: usize) -> Self {
            Setup {
                num_vars,
                max_degree,
            }
        }

        /// Builds an equivalent instance (the same base MLE repeated
        /// `max_degree` times in one `VirtualPolynomial` product term), runs
        /// hyperplonk's prover and verifier, and returns their mean
        /// wall-times.
        ///
        /// The final subclaim evaluation is deliberately excluded from the
        /// verifier timing — in a real SNARK it would be a commitment opening
        /// — but is still checked for correctness.
        ///
        /// # Panics
        /// Panics if the virtual polynomial cannot be assembled, if prove or
        /// verify errors out, or if the subclaim does not match the direct
        /// evaluation of the polynomial.
        pub fn time_protocol(&self) -> Timing {
            let nv = self.num_vars;
            let md = self.max_degree;
            let mut rng = ark_std::test_rng();
            let eval_count = 1usize << nv;
            let evals: Vec<Fr> = (0..eval_count).map(|_| Fr::rand(&mut rng)).collect();
            let claimed_sum: Fr = evals
                .iter()
                .map(|x| (0..md).fold(Fr::one(), |acc, _| acc * x))
                .fold(Fr::zero(), |acc, v| acc + v);

            let mle = Arc::new(DenseMultilinearExtension::from_evaluations_vec(nv, evals));
            let mut poly = VirtualPolynomial::new(nv);
            poly.add_mle_list(vec![mle.clone(); md], Fr::one())
                .expect("add_mle_list");

            let mut prove_sum = std::time::Duration::ZERO;
            let mut last_proof = None;
            for _ in 0..*crate::PROVER_SAMPLES {
                let mut transcript = <PolyIOP<Fr> as SumCheck<Fr>>::init_transcript();
                let t = Instant::now();
                let proof = <PolyIOP<Fr> as SumCheck<Fr>>::prove(&poly, &mut transcript)
                    .expect("hyperplonk prove failed");
                prove_sum += t.elapsed();
                last_proof = Some(proof);
            }
            let prove = prove_sum / *crate::PROVER_SAMPLES;
            let proof = last_proof.expect("PROVER_SAMPLES > 0");

            let aux = poly.aux_info.clone();
            // Verify takes &mut transcript; we re-init transcript per
            // iteration so each run starts from the same state. The
            // re-init happens OUTSIDE the per-call timer.
            let mut verify_sum = std::time::Duration::ZERO;
            let mut last_subclaim = None;
            for _ in 0..crate::VERIFY_SAMPLES {
                let mut transcript = <PolyIOP<Fr> as SumCheck<Fr>>::init_transcript();
                let t = Instant::now();
                let subclaim = <PolyIOP<Fr> as SumCheck<Fr>>::verify(
                    claimed_sum,
                    &proof,
                    &aux,
                    &mut transcript,
                )
                .expect("hyperplonk verify failed");
                verify_sum += t.elapsed();
                last_subclaim = Some(subclaim);
            }
            let verify = verify_sum / crate::VERIFY_SAMPLES;
            let subclaim = last_subclaim.expect("VERIFY_SAMPLES > 0");

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

            Timing { prove, verify }
        }
    }
}
