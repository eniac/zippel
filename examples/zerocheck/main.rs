use ark_ff::{One, Zero};
use backend::{ATyp, ArkConfig, ArkSecp256k1, Value};
use lang::id::Vid;
use share::Ctx;

use crate::common::{self, size};

fn prover_create_inputs(sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkSecp256k1>> {
    let mut rng = rand::rngs::OsRng;

    let zero = <ArkSecp256k1 as ArkConfig>::F::zero();
    let one = <ArkSecp256k1 as ArkConfig>::F::one();

    let mut v_coeffs = vec![zero; size(sizes, "S") + 1];
    *v_coeffs.last_mut().unwrap() = one;
    let v = Value::<ArkSecp256k1>::vec_scalar(v_coeffs.clone()).value_poly();

    let alpha_val: Value<ArkSecp256k1> = Value::<ArkSecp256k1>::random(&mut rng, &ATyp::scalar());
    let alpha = alpha_val.into_scalar();
    let p_coeffs: Vec<<ArkSecp256k1 as ArkConfig>::F> =
        v_coeffs.iter().map(|c| *c * alpha).collect();
    let p = Value::<ArkSecp256k1>::vec_scalar(p_coeffs).value_poly();

    Ctx::<Vid, Value<ArkSecp256k1>>::from_iter([
        (Vid("p".to_string()), p),
        (Vid("v".to_string()), v),
    ])
}

pub fn spec() -> common::ExampleSpec<ArkSecp256k1> {
    common::ExampleSpec {
        source: "examples/zerocheck/zerocheck.zippel",
        defaults: &[("S", 2)],
        validate: None,
        make_inputs: prover_create_inputs,
        analyses: &[common::Analysis::Completeness, common::Analysis::Zk],
    }
}
