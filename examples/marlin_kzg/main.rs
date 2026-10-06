use ark_ff::fields::Field;
use ark_std::UniformRand;
use backend::{ATyp, ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

use crate::common;

pub fn run(_args: &[String], opts: &common::RunOptions) {
    println!("=== Marlin-KZG (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/marlin_kzg/marlin_kzg.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("N"), &2);
    handler.compile(&sizes);

    let inputs: Inputs<_> = prover_create_inputs().into();
    common::run_prover_and_verify(&mut handler, &inputs);

    if !opts.analyses {
        return;
    }
    println!("\n--- Static Analysis ---");
    common::time_analysis!("Completeness", handler.analyze_completeness());
    common::time_analysis!("ZK", handler.analyze_knowledge());
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;

    let n_size = 2;

    let g_input = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let g: Value<ArkBls12_381> = Value::G1(g_input);

    let h_input = <ArkBls12_381 as ArkConfig>::G2::rand(&mut rng);
    let h: Value<ArkBls12_381> = Value::G2(h_input);

    let p_val: Value<ArkBls12_381> =
        Value::<ArkBls12_381>::random(&mut rng, &ATyp::uni(n_size - 1));
    let z: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let tau_input = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let gamma_input = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let gamma_g_input = g_input * gamma_input;

    // Powers of tau: tau^i * g and tau^i * gamma * g.
    let powers = |base| {
        Value::vec_g1((0..n_size).map(|_| base).collect())
            * Value::vec_scalar((0..n_size).map(|i| tau_input.pow([i as u64])).collect())
    };
    let ss: Value<ArkBls12_381> = powers(g_input);
    let gs: Value<ArkBls12_381> = powers(gamma_g_input);

    let y: Value<ArkBls12_381> = p_val.clone().value_eval(z.clone());

    let h_val: Value<ArkBls12_381> = Value::G2(h_input * tau_input);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("p_val".to_string()), p_val),
        (Vid("z".to_string()), z),
        (Vid("y".to_string()), y),
        (Vid("ss".to_string()), ss),
        (Vid("gs".to_string()), gs),
        (Vid("g".to_string()), g),
        (Vid("gamma_g".to_string()), Value::G1(gamma_g_input)),
        (Vid("h".to_string()), h),
        (Vid("h_val".to_string()), h_val),
    ])
}
