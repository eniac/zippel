use ark_ff::fields::Field;
use ark_std::UniformRand;
use backend::{ATyp, ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

#[path = "../common/analysis.rs"]
mod common;

fn main() {
    println!("=== Zeromorph Hiding KZG ===");
    let args = ZippelArgs::new(PathBuf::from("examples/zeromorph_kzg/zeromorph_kzg.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    let n_size = 2;
    sizes.insert(&Tid::new("N"), &n_size);
    handler.compile(&sizes);

    let inputs = prover_create_inputs(n_size);
    common::run_prover_and_verify(&mut handler, &inputs);

    println!("\n--- Static Analysis ---");
    let analysis_args =
        ZippelArgs::new(PathBuf::from("examples/zeromorph_kzg/zeromorph_kzg.zippel"));
    let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
    let mut analysis_sizes = Ctx::new();
    analysis_sizes.insert(&Tid::new("N"), &n_size);
    analysis_handler.compile(&analysis_sizes);

    common::time_analysis!("Completeness", analysis_handler.analyze_completeness());
    common::time_analysis!("ZK", analysis_handler.analyze_knowledge());
}

fn prover_create_inputs(n_size: usize) -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;

    let g_input = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let g = Value::G1(g_input);

    let h_input = <ArkBls12_381 as ArkConfig>::G2::rand(&mut rng);
    let h = Value::G2(h_input);

    let tau_input = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let xi_input = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);

    let mut srs_g1_vec = vec![];
    for i in 0..n_size {
        srs_g1_vec.push(g_input * tau_input.pow([i as u64]));
    }
    srs_g1_vec.push(g_input * xi_input);
    let srs_g1 = Value::VecG1(srs_g1_vec);

    let tau_g2 = h_input * tau_input;
    let xi_g2 = h_input * xi_input;
    let srs_g2 = Value::VecG2(vec![tau_g2, xi_g2]);

    let p_poly_val = Value::<ArkBls12_381>::random(&mut rng, &ATyp::uni(n_size - 1));

    let u_input = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let u_val = Value::Scalar(u_input);

    let v_val = p_poly_val.clone().value_eval(u_val.clone());

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("p_poly".to_string()), p_poly_val),
        (Vid("u".to_string()), u_val),
        (Vid("v".to_string()), v_val),
        (Vid("srs_g1".to_string()), srs_g1),
        (Vid("srs_g2".to_string()), srs_g2),
        (Vid("gen_g1".to_string()), g),
        (Vid("gen_g2".to_string()), h),
    ])
}
