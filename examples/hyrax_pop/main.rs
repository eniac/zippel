use ark_std::UniformRand;
use backend::{ArkBls12_381, Backend, Value};
use lang::id::Vid;
use share::Ctx;

use crate::common;

fn make_inputs(_sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;

    let x = <ArkBls12_381 as Backend>::F::rand(&mut rng);
    let y = <ArkBls12_381 as Backend>::F::rand(&mut rng);
    let r_x = <ArkBls12_381 as Backend>::F::rand(&mut rng);
    let r_y = <ArkBls12_381 as Backend>::F::rand(&mut rng);
    let r_z = <ArkBls12_381 as Backend>::F::rand(&mut rng);

    let g = <ArkBls12_381 as Backend>::G1::rand(&mut rng);
    let h = <ArkBls12_381 as Backend>::G1::rand(&mut rng);

    let big_x = g * x + h * r_x;
    let big_y = g * y + h * r_y;
    let big_z = g * (x * y) + h * r_z;

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("x".to_string()), Value::Scalar(x)),
        (Vid("y".to_string()), Value::Scalar(y)),
        (Vid("r_X".to_string()), Value::Scalar(r_x)),
        (Vid("r_Y".to_string()), Value::Scalar(r_y)),
        (Vid("r_Z".to_string()), Value::Scalar(r_z)),
        (Vid("g".to_string()), Value::g1(g)),
        (Vid("h".to_string()), Value::g1(h)),
        (Vid("big_x".to_string()), Value::g1(big_x)),
        (Vid("big_y".to_string()), Value::g1(big_y)),
        (Vid("big_z".to_string()), Value::g1(big_z)),
    ])
}

pub fn spec() -> common::ExampleSpec<ArkBls12_381> {
    common::ExampleSpec {
        source: "examples/hyrax_pop/hyrax_pop.zippel",
        defaults: &[],
        validate: None,
        make_inputs,
        analyses: &[common::Analysis::Completeness, common::Analysis::Zk],
    }
}
