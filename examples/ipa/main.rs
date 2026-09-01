use backend::{ATyp, ArkSecp256k1, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

use crate::common;

pub fn run(_args: &[String]) {
    println!("=== IPA (ArkSecp256k1) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/ipa/ipa.zippel"));
    let mut handler: zippel::ZippelHandler<ArkSecp256k1> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &8usize);
    handler.compile(&sizes);

    let inputs = prover_create_inputs();
    common::run_prover_and_verify(&mut handler, &inputs);

    println!("\n--- Static Analysis ---");
    let analysis_args = ZippelArgs::new(PathBuf::from("examples/ipa/ipa.zippel"));
    let mut analysis_handler: ZippelHandler<ArkSecp256k1> = ZippelHandler::new(analysis_args);
    let mut analysis_sizes = Ctx::new();
    analysis_sizes.insert(&Tid::new("S"), &1usize);
    analysis_handler.compile(&analysis_sizes);

    common::time_analysis!("Completeness", analysis_handler.analyze_completeness());
    common::time_analysis!("ZK", analysis_handler.analyze_knowledge());
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkSecp256k1>> {
    let mut rng = rand::rngs::OsRng;
    let n_val_const = 256;

    let u_aux_base: Value<ArkSecp256k1> = Value::<ArkSecp256k1>::random(&mut rng, &ATyp::g1());

    let g_vec: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n_val_const));
    let h_vec: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n_val_const));

    let a_vec_witness: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let b_vec_witness: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let ip_val_claimed: Value<ArkSecp256k1> = a_vec_witness.clone().dot(b_vec_witness.clone());
    let p_initial_commitment: Value<ArkSecp256k1> =
        g_vec.clone().dot(a_vec_witness.clone()) + h_vec.clone().dot(b_vec_witness.clone());
    let sum_vec: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec_scalar(n_val_const));

    Ctx::<Vid, Value<ArkSecp256k1>>::from_iter([
        (Vid("g_vec".to_string()), g_vec),
        (Vid("h_vec".to_string()), h_vec),
        (
            Vid("p_initial_commitment".to_string()),
            p_initial_commitment,
        ),
        (Vid("ip_val_claimed".to_string()), ip_val_claimed),
        (Vid("u_aux_base".to_string()), u_aux_base),
        (Vid("a_vec_witness".to_string()), a_vec_witness),
        (Vid("b_vec_witness".to_string()), b_vec_witness),
        (Vid("sum_vec".to_string()), sum_vec),
    ])
}
