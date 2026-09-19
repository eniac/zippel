use ark_ff::fields::Field;
use ark_std::UniformRand;
use backend::{ATyp, ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

use crate::common;

pub fn run(_args: &[String]) {
    println!("=== ZK-KZG (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/zk_kzg/zk_kzg.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("N"), &2);
    handler.compile(&sizes);

    let inputs = prover_create_inputs();
    common::run_prover_and_verify(&mut handler, &inputs);

    println!("\n--- Static Analysis ---");
    common::time_analysis!("Completeness", handler.analyze_completeness());
    common::time_analysis!("ZK", handler.analyze_knowledge());
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;

    let n_size = 2;
    let srs_size = n_size + 1;

    let g_input = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let g: Value<ArkBls12_381> = Value::G1(g_input);

    let h_input = <ArkBls12_381 as ArkConfig>::G2::rand(&mut rng);
    let h: Value<ArkBls12_381> = Value::G2(h_input);

    let p_val: Value<ArkBls12_381> =
        Value::<ArkBls12_381>::random(&mut rng, &ATyp::uni(n_size - 1));
    let z: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let tau_input = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);

    let ss: Value<ArkBls12_381> = Value::VecG1((0..srs_size).map(|_| g_input).collect())
        * Value::VecScalar((0..srs_size).map(|i| tau_input.pow([i as u64])).collect());

    let y: Value<ArkBls12_381> = p_val.clone().value_eval(z.clone());

    let h_val: Value<ArkBls12_381> = Value::G2(h_input * tau_input);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("p_val".to_string()), p_val),
        (Vid("z".to_string()), z),
        (Vid("y".to_string()), y),
        (Vid("ss".to_string()), ss),
        (Vid("g".to_string()), g),
        (Vid("h".to_string()), h),
        (Vid("h_val".to_string()), h_val),
    ])
}
