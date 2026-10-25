use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;

use crate::common;

fn make_inputs(_sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as ArkConfig>::F;
    type G1 = <ArkBls12_381 as ArkConfig>::G1;
    let mut rng = rand::rngs::OsRng;

    let x = F::rand(&mut rng);
    let r = F::rand(&mut rng);
    let g = G1::rand(&mut rng);
    let h = G1::rand(&mut rng);

    let c1 = g * r;
    let c2 = h * r + g * x;

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("x".to_string()), Value::Scalar(x)),
        (Vid("r".to_string()), Value::Scalar(r)),
        (Vid("g".to_string()), Value::g1(g)),
        (Vid("h".to_string()), Value::g1(h)),
        (Vid("c1".to_string()), Value::g1(c1)),
        (Vid("c2".to_string()), Value::g1(c2)),
    ])
}

pub fn spec() -> common::ExampleSpec<ArkBls12_381> {
    common::ExampleSpec {
        source: "examples/okamoto_elgamal/okamoto_elgamal.zippel",
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
