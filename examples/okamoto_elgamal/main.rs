use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

use crate::common;

pub fn run(_args: &[String]) {
    println!("=== Okamoto ElGamal (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from(
        "examples/okamoto_elgamal/okamoto_elgamal.zippel",
    ));
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile(&Ctx::new());

    let inputs = prover_create_inputs();
    common::run_prover_and_verify(&mut handler, &inputs);

    println!("\n--- Static Analysis ---");
    common::time_analysis!("Completeness", handler.analyze_completeness());
    common::time_analysis!("ZK", handler.analyze_knowledge());
    common::time_analysis!("Soundness", handler.analyze_special_soundness(vec![2]));
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as ArkConfig>::F;
    type G1 = <ArkBls12_381 as ArkConfig>::G1;
    let mut rng = rand::rngs::OsRng;

    let x = F::rand(&mut rng);
    let r = F::rand(&mut rng);
    let g = G1::rand(&mut rng);
    let h = G1::rand(&mut rng);

    let c1 = g * r;
    let c2 = h * r + g * x;

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("x".to_string()), Value::Scalar(x)),
        (Vid("r".to_string()), Value::Scalar(r)),
        (Vid("g".to_string()), Value::G1(g)),
        (Vid("h".to_string()), Value::G1(h)),
        (Vid("c1".to_string()), Value::G1(c1)),
        (Vid("c2".to_string()), Value::G1(c2)),
    ])
}
