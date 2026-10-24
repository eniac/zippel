use ark_std::UniformRand;
use backend::{ArkBls12_381, Backend, Value};
use lang::id::Vid;
use share::Ctx;

use crate::common;

fn make_inputs(_sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let x = <ArkBls12_381 as Backend>::F::rand(&mut rng);
    let g = <ArkBls12_381 as Backend>::G1::rand(&mut rng);
    let h_affines = backend::Group::batch_mul(&g, &[x]);
    let h = h_affines.into_iter().next().unwrap();
    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("x".to_string()), Value::Scalar(x)),
        (Vid("g".to_string()), Value::g1(g)),
        (Vid("h".to_string()), Value::g1_affine(h)),
    ])
}

pub fn spec() -> common::ExampleSpec<ArkBls12_381> {
    common::ExampleSpec {
        source: "examples/schnorr_3round/schnorr_3round.zippel",
        defaults: &[],
        validate: None,
        make_inputs,
        analyses: &[
            common::Analysis::Completeness,
            common::Analysis::Zk,
            common::Analysis::Soundness(&[2, 2, 2]),
        ],
    }
}
