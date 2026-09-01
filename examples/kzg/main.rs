use ark_ff::fields::Field;
use ark_std::UniformRand;
use backend::{ATyp, ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

use crate::common;

pub fn run(_args: &[String]) {
    println!("=== KZG (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/kzg/kzg.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("N"), &2);
    handler.compile(&sizes);

    let inputs = prover_create_inputs();
    common::run_prover_and_verify(&mut handler, &inputs);

    // Analyze completeness/ZK at the same (small) N the prover demonstrates.
    // kzg's `where` clause contains `for i in 0..N-1`, which is empty (and
    // ill-typed) at the auto-minimized N=1, so analyze at the compiled N=2.
    println!("\n--- Static Analysis ---");
    let analysis_args = ZippelArgs::new(PathBuf::from("examples/kzg/kzg.zippel"));
    let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
    let mut analysis_sizes = Ctx::new();
    analysis_sizes.insert(&Tid::new("N"), &2);
    analysis_handler.compile(&analysis_sizes);

    common::time_analysis!("Completeness", analysis_handler.analyze_completeness());
    common::time_analysis!("ZK", analysis_handler.analyze_knowledge());
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;

    let n_size = 2;
    let gen_g1_input = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let gen_g1: Value<ArkBls12_381> = Value::G1(gen_g1_input);

    let gen_g2_input = <ArkBls12_381 as ArkConfig>::G2::rand(&mut rng);
    let gen_g2: Value<ArkBls12_381> = Value::G2(gen_g2_input);

    let poly_x: Value<ArkBls12_381> =
        Value::<ArkBls12_381>::random(&mut rng, &ATyp::uni(n_size - 1));
    let eval_point: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let tau_input = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);

    let srs_g1: Value<ArkBls12_381> = Value::VecG1((0..n_size).map(|_| gen_g1_input).collect())
        * Value::VecScalar((0..n_size).map(|i| tau_input.pow([i as u64])).collect());

    let eval_result: Value<ArkBls12_381> = poly_x.clone().value_eval(eval_point.clone());

    let srs_g2_s: Value<ArkBls12_381> = Value::G2(gen_g2_input * tau_input);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("poly_x".to_string()), poly_x),
        (Vid("eval_point".to_string()), eval_point),
        (Vid("eval_result".to_string()), eval_result),
        (Vid("srs_g1".to_string()), srs_g1),
        (Vid("gen_g1".to_string()), gen_g1),
        (Vid("gen_g2".to_string()), gen_g2),
        (Vid("srs_g2_s".to_string()), srs_g2_s),
    ])
}
