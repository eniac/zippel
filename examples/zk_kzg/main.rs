use ark_ff::fields::Field;
use ark_std::UniformRand;
use backend::{ATyp, ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

#[path = "../common/analysis.rs"]
mod common;

const PUBLIC_INPUT_NAMES: &[&str] = &["z", "y", "ss", "g", "h", "h_val"];

fn main() {
    println!("=== ZK-KZG (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/zk-kzg/zk_kzg.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("N"), &2);
    handler.compile(&sizes);

    let inputs = prover_create_inputs();
    let public_inputs = inputs
        .clone()
        .into_iter()
        .filter(|(vid, _)| PUBLIC_INPUT_NAMES.contains(&vid.0.as_str()))
        .collect::<Ctx<Vid, Value<ArkBls12_381>>>();
    handler.set_public_inputs(public_inputs);
    common::run_prover_and_verify(&mut handler, inputs);

    println!("\n--- Static Analysis ---");
    let analysis_args = ZippelArgs::new(PathBuf::from("examples/zk-kzg/zk_kzg.zippel"));
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
    let srs_size = n_size + 1;

    let g_input = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let g: Value<ArkBls12_381> = Value::G1(g_input);

    let h_input = <ArkBls12_381 as ArkConfig>::G2::rand(&mut rng);
    let h: Value<ArkBls12_381> = Value::G2(h_input);

    let p: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_size));
    let z: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let tau_input = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);

    let ss: Value<ArkBls12_381> = Value::VecG1((0..srs_size).map(|_| g_input).collect())
        * Value::VecScalar((0..srs_size).map(|i| tau_input.pow([i as u64])).collect());

    let z_val: Value<ArkBls12_381> =
        Value::Vec((0..n_size).map(|i| z.clone() ^ Value::Index(i)).collect());

    let y: Value<ArkBls12_381> = p.clone().dot(z_val);

    let h_val: Value<ArkBls12_381> = Value::G2(h_input * tau_input);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("p".to_string()), p),
        (Vid("z".to_string()), z),
        (Vid("y".to_string()), y),
        (Vid("ss".to_string()), ss),
        (Vid("g".to_string()), g),
        (Vid("h".to_string()), h),
        (Vid("h_val".to_string()), h_val),
    ])
}
