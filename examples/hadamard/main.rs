use ark_ff::{One, Zero};
use backend::{ATyp, ArkConfig, ArkSecp256k1, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

use crate::common;

pub fn run(_args: &[String]) {
    println!("=== Hadamard (ArkSecp256k1) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/hadamard/hadamard.zippel"));
    let mut handler: zippel::ZippelHandler<ArkSecp256k1> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &5);
    handler.compile(&sizes);

    let inputs = prover_create_inputs();
    common::run_prover_and_verify(&mut handler, &inputs);

    println!("\n--- Static Analysis ---");
    let analysis_args = ZippelArgs::new(PathBuf::from("examples/hadamard/hadamard.zippel"));
    let mut analysis_handler: ZippelHandler<ArkSecp256k1> = ZippelHandler::new(analysis_args);
    let mut analysis_sizes = Ctx::new();
    analysis_sizes.insert(&Tid::new("S"), &2usize);
    analysis_handler.compile(&analysis_sizes);

    common::time_analysis!("Completeness", analysis_handler.analyze_completeness());
    common::time_analysis!("ZK", analysis_handler.analyze_knowledge());
}

#[allow(non_snake_case)]
fn prover_create_inputs() -> Ctx<Vid, Value<ArkSecp256k1>> {
    let mut rng = rand::rngs::OsRng;

    let n_val_const = 4;

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
    let p_A = Value::<ArkSecp256k1>::VecScalar(p_a_coeffs).value_poly();
    let p_B = Value::<ArkSecp256k1>::VecScalar(p_b_coeffs).value_poly();
    let p_C = Value::<ArkSecp256k1>::VecScalar(p_c_coeffs).value_poly();

    let zero = <ArkSecp256k1 as ArkConfig>::F::zero();
    let one = <ArkSecp256k1 as ArkConfig>::F::one();
    let mut v_h_coeffs = Vec::with_capacity(n_val_const);
    v_h_coeffs.push(one);
    v_h_coeffs.extend(std::iter::repeat_n(zero, n_val_const));
    let v_H = Value::<ArkSecp256k1>::VecScalar(v_h_coeffs).value_poly();

    Ctx::<Vid, Value<ArkSecp256k1>>::from_iter([
        (Vid("p_A".to_string()), p_A),
        (Vid("p_B".to_string()), p_B),
        (Vid("p_C".to_string()), p_C),
        (Vid("v_H".to_string()), v_H),
    ])
}
