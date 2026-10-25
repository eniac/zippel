use ark_ff::Zero;
use ark_poly::DenseMultilinearExtension;
use ark_std::UniformRand;
use backend::VirtualPolynomial;
use backend::poly_variant::PolyVariant;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;

use crate::common;
use crate::common::size;

fn make_inputs(sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as ArkConfig>::F;
    let num_vars = size(sizes, "NUM_VARS_CONST");
    let max_degree = size(sizes, "MAX_DEGREE_CONST");

    let eval_count = 1usize << num_vars;
    let mut rng = rand::rngs::OsRng;
    let base_evals: Vec<F> = (0..eval_count).map(|_| F::rand(&mut rng)).collect();

    let claimed_sum: F = base_evals
        .iter()
        .map(|x| (0..max_degree).fold(F::from(1u64), |acc, _| acc * *x))
        .fold(F::zero(), |acc, val| acc + val);

    let base = VirtualPolynomial::from_poly(PolyVariant::DenseMle(
        DenseMultilinearExtension::from_evaluations_vec(num_vars, base_evals),
    ));
    let mut full_poly = base.clone();
    for _ in 1..max_degree {
        full_poly = full_poly.poly_mul(&base);
    }
    let poly = Value::poly(full_poly);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("claimed_sum".to_string()), Value::Scalar(claimed_sum)),
        (Vid("p".to_string()), poly),
    ])
}

pub fn spec() -> common::ExampleSpec<ArkBls12_381> {
    common::ExampleSpec {
        source: "examples/sumcheck/sumcheck.zippel",
        run_defaults: &[("NUM_VARS_CONST", 19), ("MAX_DEGREE_CONST", 3)],
        analysis_defaults: &[("NUM_VARS_CONST", 3), ("MAX_DEGREE_CONST", 1)],
        validate: Some(|sizes, _analysis| {
            common::check_power_of_two(sizes, "NUM_VARS_CONST")?;
            Ok(())
        }),
        make_inputs,
        analyses: &[common::Analysis::Completeness],
    }
}
