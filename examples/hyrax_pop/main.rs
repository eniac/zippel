use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

#[path = "../common/analysis.rs"]
mod common;

fn main() {
    println!("=== Hyrax PoP (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/hyrax_pop/hyrax_pop.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile(&Ctx::new());

    let inputs = prover_create_inputs();
    common::run_prover_and_verify(&mut handler, &inputs);

    println!("\n--- Static Analysis ---");
    let analysis_args = ZippelArgs::new(PathBuf::from("examples/hyrax_pop/hyrax_pop.zippel"));
    let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
    analysis_handler.compile(&Ctx::new());

    common::time_analysis!("Completeness", analysis_handler.analyze_completeness());
    common::time_analysis!("ZK", analysis_handler.analyze_knowledge());
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;

    let x = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let y = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let r_x = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let r_y = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let r_z = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);

    let g = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let h = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);

    let big_x = g * x + h * r_x;
    let big_y = g * y + h * r_y;
    let big_z = g * (x * y) + h * r_z;

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("x".to_string()), Value::Scalar(x)),
        (Vid("y".to_string()), Value::Scalar(y)),
        (Vid("r_X".to_string()), Value::Scalar(r_x)),
        (Vid("r_Y".to_string()), Value::Scalar(r_y)),
        (Vid("r_Z".to_string()), Value::Scalar(r_z)),
        (Vid("g".to_string()), Value::G1(g)),
        (Vid("h".to_string()), Value::G1(h)),
        (Vid("big_x".to_string()), Value::G1(big_x)),
        (Vid("big_y".to_string()), Value::G1(big_y)),
        (Vid("big_z".to_string()), Value::G1(big_z)),
    ])
}
