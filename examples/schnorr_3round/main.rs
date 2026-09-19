use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, ArkGroupOps, Value};
use lang::id::Vid;
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

use crate::common;

pub fn run(_args: &[String]) {
    println!("=== Schnorr 3-Round (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from(
        "examples/schnorr_3round/schnorr_3round.zippel",
    ));
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile(&Ctx::new());

    let inputs = prover_create_inputs();
    common::run_prover_and_verify(&mut handler, &inputs);

    println!("\n--- Static Analysis ---");
    common::time_analysis!("Completeness", handler.analyze_completeness());
    common::time_analysis!("ZK", handler.analyze_knowledge());
    common::time_analysis!(
        "Soundness",
        handler.analyze_special_soundness(vec![2, 2, 2])
    );
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let x = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let g = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let h_affines = <ArkBls12_381 as ArkConfig>::G1Ops::vec_mul(&g, &[x]);
    let h = h_affines.into_iter().next().unwrap();
    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("x".to_string()), Value::Scalar(x)),
        (Vid("g".to_string()), Value::G1(g)),
        (Vid("h".to_string()), Value::G1Affine(h)),
    ])
}
