use ark_std::UniformRand;
use backend::{ArkConfig, ArkSecp256k1, Value};
use lang::id::Vid;
use share::Ctx;
use std::ops::Mul;
use std::path::PathBuf;
use zippel::*;

use crate::common;

pub fn run(_args: &[String]) {
    println!("=== Pedersen Equality (ArkSecp256k1) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/pedersen_eq/pedersen_eq.zippel"));
    let mut handler: zippel::ZippelHandler<ArkSecp256k1> = ZippelHandler::new(args);
    handler.compile(&Ctx::new());

    let inputs = prover_create_inputs();
    common::run_prover_and_verify(&mut handler, &inputs);

    println!("\n--- Static Analysis ---");
    common::time_analysis!("Completeness", handler.analyze_completeness());
    common::time_analysis!("ZK", handler.analyze_knowledge());
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkSecp256k1>> {
    let mut rng = rand::rngs::OsRng;

    let m1 = <ArkSecp256k1 as ArkConfig>::F::rand(&mut rng);
    let r1 = <ArkSecp256k1 as ArkConfig>::F::rand(&mut rng);

    let m2 = m1;
    let r2 = <ArkSecp256k1 as ArkConfig>::F::rand(&mut rng);

    let g = <ArkSecp256k1 as ArkConfig>::G1::rand(&mut rng);
    let h = <ArkSecp256k1 as ArkConfig>::G1::rand(&mut rng);

    let c1 = g.mul(m1) + h.mul(r1);
    let c2 = g.mul(m2) + h.mul(r2);

    Ctx::<Vid, Value<ArkSecp256k1>>::from_iter([
        (Vid("m1".to_string()), Value::Scalar(m1)),
        (Vid("r1".to_string()), Value::Scalar(r1)),
        (Vid("m2".to_string()), Value::Scalar(m2)),
        (Vid("r2".to_string()), Value::Scalar(r2)),
        (Vid("g".to_string()), Value::G1(g)),
        (Vid("h".to_string()), Value::G1(h)),
        (Vid("c1".to_string()), Value::G1(c1)),
        (Vid("c2".to_string()), Value::G1(c2)),
    ])
}
