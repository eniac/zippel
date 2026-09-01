use backend::{ATyp, ArkBls12_381, Value};
use lang::id::Vid;
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

use crate::common;

pub fn run(_args: &[String]) {
    println!("=== Chaum-Pedersen (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/cp/cp.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile(&Ctx::new());

    let inputs = prover_create_inputs();
    common::run_prover_and_verify(&mut handler, &inputs);

    println!("\n--- Static Analysis ---");
    let analysis_args = ZippelArgs::new(PathBuf::from("examples/cp/cp.zippel"));
    let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
    analysis_handler.compile(&Ctx::new());

    common::time_analysis!("Completeness", analysis_handler.analyze_completeness());
    common::time_analysis!("ZK", analysis_handler.analyze_knowledge());
    common::time_analysis!(
        "Soundness",
        analysis_handler.analyze_special_soundness(vec![2])
    );
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
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
