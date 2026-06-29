use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;
use std::ops::Mul;
use std::path::PathBuf;
use zippel::*;

#[path = "../common/analysis.rs"]
mod common;

fn main() {
    println!("=== Prove Commitment Equality (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from(
        "examples/commitment_equality/commitment_equality.zippel",
    ));
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile(&Ctx::new());

    let inputs = prover_create_inputs();
    common::run_prover_and_verify(&mut handler, &inputs);

    println!("\n--- Static Analysis ---");
    let analysis_args = ZippelArgs::new(PathBuf::from(
        "examples/commitment_equality/commitment_equality.zippel",
    ));
    let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
    analysis_handler.compile(&Ctx::new());

    common::time_analysis!("Completeness", analysis_handler.analyze_completeness());
    common::time_analysis!("ZK", analysis_handler.analyze_knowledge());
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;

    let x = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let r1 = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let r2 = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let g = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let h = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);

    let c1 = g.mul(x) + h.mul(r1);
    let c2 = g.mul(x) + h.mul(r2);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("x".to_string()), Value::Scalar(x)),
        (Vid("r1".to_string()), Value::Scalar(r1)),
        (Vid("r2".to_string()), Value::Scalar(r2)),
        (Vid("g".to_string()), Value::G1(g)),
        (Vid("h".to_string()), Value::G1(h)),
        (Vid("c1".to_string()), Value::G1(c1)),
        (Vid("c2".to_string()), Value::G1(c2)),
    ])
}
