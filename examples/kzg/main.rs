use ark_ff::fields::Field;
use ark_std::UniformRand;
use backend::{ATyp, ArkBls12_381, Backend, Value};
use lang::id::Vid;
use share::Ctx;

use crate::common;
use crate::common::size;

fn make_inputs(sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;

    let n_size = size(sizes, "N");
    let gen_g1_input = <ArkBls12_381 as Backend>::G1::rand(&mut rng);
    let gen_g1: Value<ArkBls12_381> = Value::g1(gen_g1_input);

    let gen_g2_input = <ArkBls12_381 as Backend>::G2::rand(&mut rng);
    let gen_g2: Value<ArkBls12_381> = Value::g2(gen_g2_input);

    let poly_x: Value<ArkBls12_381> =
        Value::<ArkBls12_381>::random(&mut rng, &ATyp::uni(n_size - 1));
    let eval_point: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let tau_input = <ArkBls12_381 as Backend>::F::rand(&mut rng);

    let srs_g1: Value<ArkBls12_381> = Value::vec_g1((0..n_size).map(|_| gen_g1_input).collect())
        * Value::vec_scalar((0..n_size).map(|i| tau_input.pow([i as u64])).collect());

    let eval_result: Value<ArkBls12_381> = poly_x.clone().value_eval(eval_point.clone());

    let srs_g2_s: Value<ArkBls12_381> = Value::g2(gen_g2_input * tau_input);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("poly_x".to_string()), poly_x),
        (Vid("eval_point".to_string()), eval_point),
        (Vid("eval_result".to_string()), eval_result),
        (Vid("srs_g1".to_string()), srs_g1),
        (Vid("gen_g1".to_string()), gen_g1),
        (Vid("gen_g2".to_string()), gen_g2),
        (Vid("srs_g2_s".to_string()), srs_g2_s),
    ])
}

pub fn spec() -> common::ExampleSpec<ArkBls12_381> {
    common::ExampleSpec {
        source: "examples/kzg/kzg.zippel",
        run_defaults: &[("N", 8192)],
        analysis_defaults: &[("N", 2)],
        validate: None,
        make_inputs,
        analyses: &[common::Analysis::Completeness],
    }
}
