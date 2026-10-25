use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;
use std::ops::Mul;

use crate::common;

fn make_inputs(_sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;

    let x = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let r1 = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let r2 = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let g = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let h = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);

    let c1 = g.mul(x) + h.mul(r1);
    let c2 = g.mul(x) + h.mul(r2);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("r_diff".to_string()), Value::Scalar(r1 - r2)),
        (Vid("h".to_string()), Value::g1(h)),
        (Vid("c1".to_string()), Value::g1(c1)),
        (Vid("c2".to_string()), Value::g1(c2)),
    ])
}

pub fn spec() -> common::ExampleSpec<ArkBls12_381> {
    common::ExampleSpec {
        source: "examples/pedersen_eq/pedersen_eq.zippel",
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
