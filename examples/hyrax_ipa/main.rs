use ark_std::UniformRand;
use backend::{ATyp, ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

#[path = "../common/analysis.rs"]
mod common;

fn main() {
    println!("=== Hyrax Log of Dot Product (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/hyrax_ipa/hyrax_ipa.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &6usize);
    handler.compile(&sizes);

    let inputs = prover_create_inputs();
    common::run_prover_and_verify(&mut handler, &inputs);

    println!("\n--- Static Analysis ---");
    let analysis_args = ZippelArgs::new(PathBuf::from("examples/hyrax_ipa/hyrax_ipa.zippel"));
    let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
    let mut analysis_sizes = Ctx::new();
    analysis_sizes.insert(&Tid::new("S"), &1usize);
    analysis_handler.compile(&analysis_sizes);

    common::time_analysis!("Completeness", analysis_handler.analyze_completeness());
    common::time_analysis!("ZK", analysis_handler.analyze_knowledge());
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let n_val_const = 64;

    let x_vec = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let a_vec = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let y = x_vec.clone().dot(a_vec.clone());

    let r_xi = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let r_tau = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);

    let g_vec = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n_val_const));
    let g_base = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let h_base = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);

    let tau_val = match y.clone() {
        Value::Scalar(y_scalar) => g_base * y_scalar + h_base * r_tau,
        _ => unreachable!(),
    };

    let gx_dot = g_vec.clone().dot(x_vec.clone());
    let xi_val = match gx_dot {
        Value::G1(gx_sum) => h_base * r_xi + gx_sum,
        _ => unreachable!(),
    };

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("xi".to_string()), Value::G1(xi_val)),
        (Vid("tau".to_string()), Value::G1(tau_val)),
        (Vid("a_vec".to_string()), a_vec),
        (Vid("g_vec".to_string()), g_vec),
        (Vid("g_base".to_string()), Value::G1(g_base)),
        (Vid("h_base".to_string()), Value::G1(h_base)),
        (Vid("x_vec".to_string()), x_vec),
        (Vid("y".to_string()), y),
        (Vid("r_xi".to_string()), Value::Scalar(r_xi)),
        (Vid("r_tau".to_string()), Value::Scalar(r_tau)),
    ])
}
