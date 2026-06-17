use ark_ff::{One, Zero};
use backend::{ATyp, ArkConfig, ArkSecp256k1, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

#[path = "../common/analysis.rs"]
mod common;

fn main() {
    println!("=== Zerocheck (ArkSecp256k1) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/zerocheck/zerocheck.zippel"));
    let mut handler: zippel::ZippelHandler<ArkSecp256k1> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &2);
    handler.compile(&sizes);

    let inputs = prover_create_inputs();
    common::run_prover_and_verify(&mut handler, inputs);

    println!("\n--- Static Analysis ---");
    let analysis_args = ZippelArgs::new(PathBuf::from("examples/zerocheck/zerocheck.zippel"));
    let mut analysis_handler: ZippelHandler<ArkSecp256k1> = ZippelHandler::new(analysis_args);
    let mut analysis_sizes = Ctx::new();
    analysis_sizes.insert(&Tid::new("S"), &1usize);
    analysis_handler.compile(&analysis_sizes);

    common::time_analysis!("Completeness", analysis_handler.analyze_completeness());
    common::time_analysis!("ZK", analysis_handler.analyze_knowledge());
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkSecp256k1>> {
    let mut rng = rand::rngs::OsRng;

    let zero = <ArkSecp256k1 as ArkConfig>::F::zero();
    let one = <ArkSecp256k1 as ArkConfig>::F::one();

    let v_coeffs = vec![zero, one];
    let v = Value::<ArkSecp256k1>::VecScalar(v_coeffs.clone()).value_poly();

    let alpha_val: Value<ArkSecp256k1> = Value::<ArkSecp256k1>::random(&mut rng, &ATyp::scalar());
    let alpha = alpha_val.into_scalar();
    let p_coeffs: Vec<<ArkSecp256k1 as ArkConfig>::F> =
        v_coeffs.iter().map(|c| *c * alpha).collect();
    let p = Value::<ArkSecp256k1>::VecScalar(p_coeffs).value_poly();

    Ctx::<Vid, Value<ArkSecp256k1>>::from_iter([
        (Vid("p".to_string()), p),
        (Vid("v".to_string()), v),
    ])
}
