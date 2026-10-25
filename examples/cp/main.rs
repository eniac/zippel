use backend::{ATyp, ArkBls12_381, Value};
use lang::id::Vid;
use share::Ctx;

use crate::common;

fn make_inputs(_sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;

    let beta: Value<ArkBls12_381> = Value::random(&mut rng, &ATyp::scalar());
    let g: Value<ArkBls12_381> = Value::random(&mut rng, &ATyp::g1());
    let u: Value<ArkBls12_381> = Value::random(&mut rng, &ATyp::g1());

    let v = g.clone() * beta.clone();
    let w = u.clone() * beta.clone();

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("beta".to_string()), beta),
        (Vid("g".to_string()), g),
        (Vid("u".to_string()), u),
        (Vid("v".to_string()), v),
        (Vid("w".to_string()), w),
    ])
}

pub fn spec() -> common::ExampleSpec<ArkBls12_381> {
    common::ExampleSpec {
        source: "examples/cp/cp.zippel",
        run_defaults: &[],
        analysis_defaults: &[],
        validate: None,
        make_inputs,
        analyses: &[
            common::Analysis::Completeness,
            common::Analysis::Soundness(&[2]),
        ],
    }
}
