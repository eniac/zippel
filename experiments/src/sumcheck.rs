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
    use ark_std::UniformRand;
    use backend::poly_variant::DenseMle;
    use backend::poly_variant::PolyVariant;
    use backend::{ArkBls12_381, Backend, Value, VirtualPolynomial};
    use lang::id::{Tid, Vid};
    use share::Ctx;
    use std::path::PathBuf;
    use zippel::{
        CompileOptions, CompiledProtocol, CompiledProver, CompiledVerifier, ParsedModule,
    };

    /// A compiled sumcheck instance, reusable across `time_protocol` calls.
    ///
    /// Holds the projected prover and verifier, the two size parameters bound
    /// at compile time, and how long compilation and projection took.
    pub struct Setup {
        prover: CompiledProver<ArkBls12_381>,
        verifier: CompiledVerifier<ArkBls12_381>,
        num_vars: usize,
        max_degree: usize,
        compile_time: Vec<std::time::Duration>,
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
            let ((prover, verifier), compile_time) = crate::sample_compile(|| {
                let module = ParsedModule::load(
                    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                        .join("..")
                        .join("examples/sumcheck/sumcheck.zippel"),
                )
                .expect("parse protocol");
                let mut sizes = Ctx::new();
                sizes.insert(&Tid::new("NUM_VARS_CONST"), &num_vars);
                sizes.insert(&Tid::new("MAX_DEGREE_CONST"), &max_degree);
                let protocol: CompiledProtocol<ArkBls12_381> = module
                    .compile(&sizes, CompileOptions::default())
                    .expect("compile protocol");
                (
                    protocol.project_prover(),
                    protocol.project_verifier().expect("project verifier"),
                )
            });

            Setup {
                prover,
                verifier,
                num_vars,
                max_degree,
                compile_time,
            }
        }

        /// Wall-time spent in `ParsedModule::compile` for this instance:
        /// parsing, type checking, and graph construction only.
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
            type F = <ArkBls12_381 as Backend>::F;
            let nv = self.num_vars;
            let md = self.max_degree;
            let eval_count = 1usize << nv;
            let mut rng = rand::rngs::OsRng;
            let base_evals: Vec<F> = (0..eval_count).map(|_| F::rand(&mut rng)).collect();
            let claimed_sum: F = base_evals
                .iter()
                .map(|x| (0..md).fold(F::from(1u64), |acc, _| acc * *x))
                .fold(F::zero(), |acc, v| acc + v);
            let base =
                VirtualPolynomial::from_poly(PolyVariant::DenseMle(DenseMle::new(nv, base_evals)));
            let mut full_poly = base.clone();
            for _ in 1..md {
                full_poly = full_poly.poly_mul(&base);
            }
            let inputs = crate::harness_inputs([
                (Vid("claimed_sum".to_string()), Value::Scalar(claimed_sum)),
                (Vid("p".to_string()), Value::poly(full_poly)),
            ]);
            let (prove, prove_peak, proof) = crate::sample_zippel_prover(&self.prover, &inputs);
            let (verify, verify_peak, passed) =
                crate::sample_zippel_verifier(&self.verifier, &proof, &inputs);
            assert!(passed, "zippel sumcheck verification FAILED");

            Timing {
                prove,
                verify,
                prove_peak,
                verify_peak,
            }
        }
    }
}

/// Native sumcheck baseline: hyperplonk's `poly_iop::sum_check`,
/// vendored in-tree under `crate::upstream::sumcheck` and ported to
/// arkworks 0.6 so it shares the zippel-side curve set. Protocol code
/// verbatim from EspressoSystems/hyperplonk `main`; only `use` paths
/// changed.
pub mod native_side {
    use super::*;
    use crate::upstream::sumcheck::arithmetic::VirtualPolynomial;
    use crate::upstream::sumcheck::poly_iop::{PolyIOP, SumCheck};
    use ark_bls12_381::Fr;
    use ark_ff::{One, UniformRand, Zero};
    use ark_poly::DenseMultilinearExtension;
    use std::sync::Arc;

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

            let (prove, prove_peak, proof) = crate::sample(|| {
                let mut transcript = <PolyIOP<Fr> as SumCheck<Fr>>::init_transcript();
                <PolyIOP<Fr> as SumCheck<Fr>>::prove(&poly, &mut transcript)
                    .expect("hyperplonk prove failed")
            });

            let aux = poly.aux_info.clone();
            // Each run makes its own transcript inside the timer, as zippel
            // makes its sponge inside each run.
            let (verify, verify_peak, subclaim) = crate::sample(|| {
                let mut transcript = <PolyIOP<Fr> as SumCheck<Fr>>::init_transcript();
                <PolyIOP<Fr> as SumCheck<Fr>>::verify(claimed_sum, &proof, &aux, &mut transcript)
                    .expect("hyperplonk verify failed")
            });

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
// Cross-verification: at the same challenges, each verifier accepts the other's
// proof, and the native's subclaim holds for both.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod cross_tests {
    use crate::cross::{Challenges, Direction};
    use crate::upstream::sumcheck::arithmetic::VirtualPolynomial;
    use crate::upstream::sumcheck::poly_iop::structs::{IOPProof, IOPProverMessage};
    use crate::upstream::sumcheck::poly_iop::{PolyIOP, SumCheck};
    use ark_bls12_381::Fr;
    use ark_ff::{One, UniformRand};
    use ark_poly::DenseMultilinearExtension;
    use backend::poly_variant::{DenseMle, PolyVariant};
    use backend::{ArkBls12_381, Value};
    use std::sync::Arc;

    type V = Value<ArkBls12_381>;
    type Iop = PolyIOP<Fr>;

    fn frs(v: &V) -> Vec<Fr> {
        match v {
            Value::VecScalar(f) => f.to_vec(),
            _ => panic!("expected scalars, got {v}"),
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
        for (nv, md) in [(3usize, 2usize), (4, 3), (5, 2)] {
            let evals: Vec<Fr> = (0..1 << nv).map(|_| Fr::rand(&mut rng)).collect();
            let sum: Fr = evals
                .iter()
                .map(|x| (0..md).fold(Fr::one(), |a, _| a * x))
                .sum();
            let mle = Arc::new(DenseMultilinearExtension::from_evaluations_vec(
                nv,
                evals.clone(),
            ));
            let mut poly = VirtualPolynomial::new(nv);
            poly.add_mle_list(vec![mle; md], Fr::one()).unwrap();
            let base = backend::VirtualPolynomial::from_poly(PolyVariant::DenseMle(DenseMle::new(
                nv, evals,
            )));
            let full = (1..md).fold(base.clone(), |p, _| p.poly_mul(&base));

            let (prover, verifier) = crate::cross::compile::<ArkBls12_381>(
                "sumcheck",
                &[("NUM_VARS_CONST", nv), ("MAX_DEGREE_CONST", md)],
            );
            let inputs = crate::harness_inputs([
                ("claimed_sum", Value::Scalar(sum)),
                ("p", Value::poly(full)),
            ]);
            // The native's final check: the subclaim is the polynomial at its point.
            let native_verify = |proof: &IOPProof<Fr>| {
                let sub = Iop::verify(sum, proof, &poly.aux_info, &mut Iop::init_transcript())
                    .expect("native verify");
                poly.evaluate(&sub.point).unwrap() == sub.expected_evaluation
            };

            match direction {
                Direction::NativeToZippel => {
                    let native = Iop::prove(&poly, &mut Iop::init_transcript()).unwrap();
                    assert!(
                        native_verify(&native),
                        "nv = {nv}: native rejects its own proof"
                    );
                    let rounds: Vec<V> = native
                        .proofs
                        .iter()
                        .map(|m| Value::vec_scalar(m.evaluations.clone()))
                        .collect();
                    assert!(
                        verifier
                            .verify_with(
                                rounds.clone(),
                                crate::lend(&inputs),
                                &mut Challenges::default()
                            )
                            .unwrap(),
                        "nv = {nv}: Zippel rejects the native proof"
                    );
                    let mut wrong = rounds;
                    wrong[1] =
                        Value::vec_scalar(frs(&wrong[1]).iter().map(|e| *e + Fr::one()).collect());
                    assert!(
                        !verifier
                            .verify_with(wrong, crate::lend(&inputs), &mut Challenges::default())
                            .unwrap(),
                        "nv = {nv}: Zippel accepts a wrong round"
                    );
                }
                Direction::ZippelToNative => {
                    let ours = prover
                        .prove_with(crate::lend(&inputs), &mut Challenges::default())
                        .unwrap();
                    assert_eq!(ours.len(), nv, "nv = {nv}: Zippel's message count");
                    let mut seq = Challenges::default();
                    let proof = IOPProof {
                        point: (0..nv).map(|_| seq.next_scalar()).collect(),
                        proofs: ours
                            .iter()
                            .map(|m| IOPProverMessage {
                                evaluations: frs(m),
                            })
                            .collect(),
                    };
                    assert!(
                        native_verify(&proof),
                        "nv = {nv}: the native verifier rejects Zippel's proof"
                    );
                }
            }
        }
    }
}
