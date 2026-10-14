use ark_ff::{One, Zero};
use backend::{ATyp, ArkConfig, ArkSecp256k1, Value};
use lang::id::Vid;
use share::Ctx;

use crate::common;
use crate::common::size;

/// The degree bound `N` the protocol is compiled for: `v_H` has degree `N`,
/// `p_A`, `p_B`, `p_C` degree `N - 1`.
#[allow(non_snake_case)]
fn prover_create_inputs(sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkSecp256k1>> {
    let n_val = size(sizes, "N");

    let mut rng = rand::rngs::OsRng;

    let n_val_const = n_val;

    let mut p_a_coeffs = Vec::with_capacity(n_val_const);
    let mut p_b_coeffs = Vec::with_capacity(n_val_const);
    let mut p_c_coeffs = Vec::with_capacity(n_val_const);
    for _ in 0..n_val_const {
        let a_i: Value<ArkSecp256k1> = Value::<ArkSecp256k1>::random(&mut rng, &ATyp::scalar());
        let b_i: Value<ArkSecp256k1> = Value::<ArkSecp256k1>::random(&mut rng, &ATyp::scalar());
        let c_i: Value<ArkSecp256k1> = Value::<ArkSecp256k1>::random(&mut rng, &ATyp::scalar());
        p_a_coeffs.push(a_i.into_scalar());
        p_b_coeffs.push(b_i.into_scalar());
        p_c_coeffs.push(c_i.into_scalar());
    }
    let p_A = Value::<ArkSecp256k1>::vec_scalar(p_a_coeffs).value_poly();
    let p_B = Value::<ArkSecp256k1>::vec_scalar(p_b_coeffs).value_poly();
    let p_C = Value::<ArkSecp256k1>::vec_scalar(p_c_coeffs).value_poly();

    let zero = <ArkSecp256k1 as ArkConfig>::F::zero();
    let one = <ArkSecp256k1 as ArkConfig>::F::one();
    let mut v_h_coeffs = Vec::with_capacity(n_val_const);
    v_h_coeffs.push(one);
    v_h_coeffs.extend(std::iter::repeat_n(zero, n_val_const));
    let v_H = Value::<ArkSecp256k1>::vec_scalar(v_h_coeffs).value_poly();

    Ctx::<Vid, Value<ArkSecp256k1>>::from_iter([
        (Vid("p_A".to_string()), p_A),
        (Vid("p_B".to_string()), p_B),
        (Vid("p_C".to_string()), p_C),
        (Vid("v_H".to_string()), v_H),
    ])
}

pub fn spec() -> common::ExampleSpec<ArkSecp256k1> {
    common::ExampleSpec {
        source: "examples/hadamard/hadamard.zippel",
        defaults: &[("N", 4)],
        validate: None,
        make_inputs: prover_create_inputs,
        analyses: &[common::Analysis::Completeness, common::Analysis::Zk],
    }
}
