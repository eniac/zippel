//! Sumcheck comparison: zippel-compiled sumcheck vs. Espresso hyperplonk's
//! `subroutines::poly_iop::sum_check`.
//!
//! Both sides run the same protocol shape — sum over {0,1}^num_vars of
//! base(x)^max_degree where base is a random dense MLE — and report
//! pure prover and verifier wall-time (no input construction, no compile).
//!
//! The bundled `.zippel` source pins NUM_VARS_CONST and MAX_DEGREE_CONST
//! to 10 (both as type defaults and as the literal `2..10` range bound on
//! the recursive helper). To sweep sizes on the zippel side we
//! string-substitute those literals at runtime and feed the result to a
//! tempfile that `ZippelArgs` loads.

use crate::Timing;

pub const DEFAULT_NUM_VARS: usize = 10;
pub const DEFAULT_MAX_DEGREE: usize = 10;

fn render_zippel_source(num_vars: usize, max_degree: usize) -> String {
    let template = include_str!("../../examples/sumcheck/sumcheck.zippel");
    template
        .replace("NUM_VARS_CONST: 10", &format!("NUM_VARS_CONST: {num_vars}"))
        .replace("V: 2..10", &format!("V: 2..{num_vars}"))
        .replace(
            "MAX_DEGREE_CONST: 10",
            &format!("MAX_DEGREE_CONST: {max_degree}"),
        )
}

pub mod zippel_side {
    use super::*;
    use ark_ff::Zero;
    use ark_poly::DenseMultilinearExtension;
    use ark_std::UniformRand;
    use backend::poly_variant::PolyVariant;
    use backend::{ArkBls12_381, ArkConfig, Value, VirtualPolynomial};
    use lang::id::{Tid, Vid};
    use share::Ctx;
    use std::io::Write;
    use std::time::Instant;
    use tempfile::NamedTempFile;
    use zippel::{ZippelArgs, ZippelHandler, check_verification};

    pub struct Setup {
        handler: ZippelHandler<ArkBls12_381>,
        num_vars: usize,
        max_degree: usize,
        // Kept alive so the tempfile path remains valid for as long as the
        // handler might need it.
        _source_file: NamedTempFile,
    }

    impl Setup {
        pub fn new(num_vars: usize, max_degree: usize) -> Self {
            let source = render_zippel_source(num_vars, max_degree);
            let mut file = NamedTempFile::with_suffix(".zippel").expect("tempfile");
            file.write_all(source.as_bytes()).expect("write tempfile");

            let args = ZippelArgs::new(file.path().to_path_buf());
            let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
            let mut sizes = Ctx::new();
            sizes.insert(&Tid::new("S"), &10);
            handler.compile(&sizes);

            Setup {
                handler,
                num_vars,
                max_degree,
                _source_file: file,
            }
        }

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
                (Vid("poly".to_string()), Value::Poly(full_poly)),
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
            assert!(result.passed, "zippel sumcheck verification FAILED");

            Timing { prove, verify }
        }
    }
}

pub mod native_side {
    use super::*;
    use arithmetic::VirtualPolynomial;
    use hp_ark_bls12_381::Fr;
    use hp_ark_ff::{One, UniformRand, Zero};
    use hp_ark_poly::DenseMultilinearExtension;
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
            let nv = self.num_vars;
            let md = self.max_degree;
            let mut rng = hp_ark_std::test_rng();
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

            let mut transcript = <PolyIOP<Fr> as SumCheck<Fr>>::init_transcript();
            let t = Instant::now();
            let proof = <PolyIOP<Fr> as SumCheck<Fr>>::prove(&poly, &mut transcript)
                .expect("hyperplonk prove failed");
            let prove = t.elapsed();

            let aux = poly.aux_info.clone();
            let mut transcript = <PolyIOP<Fr> as SumCheck<Fr>>::init_transcript();
            let t = Instant::now();
            let subclaim = <PolyIOP<Fr> as SumCheck<Fr>>::verify(
                claimed_sum,
                &proof,
                &aux,
                &mut transcript,
            )
            .expect("hyperplonk verify failed");
            let verify = t.elapsed();

            let lhs = poly.evaluate(&subclaim.point).expect("evaluate");
            assert_eq!(
                lhs, subclaim.expected_evaluation,
                "hyperplonk sumcheck subclaim mismatch"
            );

            Timing { prove, verify }
        }
    }
}
