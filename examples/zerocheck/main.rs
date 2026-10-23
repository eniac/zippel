use ark_ff::{One, Zero};
use backend::{ATyp, ArkBls12_381, Backend, Value};
use lang::id::Vid;
use share::Ctx;

use crate::common::{self, size};

fn make_inputs(sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;

    let zero = <ArkBls12_381 as Backend>::F::zero();
    let one = <ArkBls12_381 as Backend>::F::one();

    let mut v_coeffs = vec![zero; size(sizes, "S") + 1];
    *v_coeffs.last_mut().unwrap() = one;
    let v = Value::<ArkBls12_381>::vec_scalar(v_coeffs.clone()).value_poly();

    let alpha_val: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let alpha = alpha_val.into_scalar();
    let p_coeffs: Vec<<ArkBls12_381 as Backend>::F> = v_coeffs.iter().map(|c| *c * alpha).collect();
    let p = Value::<ArkBls12_381>::vec_scalar(p_coeffs).value_poly();

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("p".to_string()), p),
        (Vid("v".to_string()), v),
    ])
}

pub fn spec() -> common::ExampleSpec<ArkBls12_381> {
    common::ExampleSpec {
        source: "examples/zerocheck/zerocheck.zippel",
        run_defaults: &[("S", 524_288)],
        analysis_defaults: &[("S", 1)],
        validate: None,
        make_inputs,
        analyses: &[common::Analysis::Completeness],
    }
}
