use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

#[path = "../common/analysis.rs"]
mod common;

fn main() {
    println!("=== R1CS Sigma (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/r1cs_sigma/r1cs_sigma.zippel"));
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile(&Ctx::new());

    let inputs = prover_create_inputs();
    common::run_prover_and_verify(&mut handler, &inputs);

    println!("\n--- Static Analysis ---");
    let analysis_args = ZippelArgs::new(PathBuf::from("examples/r1cs_sigma/r1cs_sigma.zippel"));
    let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
    analysis_handler.compile(&Ctx::new());

    common::time_analysis!("Completeness", analysis_handler.analyze_completeness());
    common::time_analysis!("ZK", analysis_handler.analyze_knowledge());
    common::time_analysis!(
        "Soundness",
        analysis_handler.analyze_special_soundness(vec![2])
    );
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as ArkConfig>::F;
    type G1 = <ArkBls12_381 as ArkConfig>::G1;
    let mut rng = rand::rngs::OsRng;

    let x0 = F::rand(&mut rng);
    let w0 = x0 * x0;

    let mat_a = vec![F::from(1u64), F::from(0u64)];
    let mat_b = vec![F::from(1u64), F::from(0u64)];
    let mat_c = vec![F::from(0u64), F::from(1u64)];

    let ck = G1::rand(&mut rng);
    let h_base = G1::rand(&mut rng);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("ck".to_string()), Value::VecG1(vec![ck])),
        (Vid("h_base".to_string()), Value::G1(h_base)),
        (Vid("mat_A".to_string()), Value::VecScalar(mat_a)),
        (Vid("mat_B".to_string()), Value::VecScalar(mat_b)),
        (Vid("mat_C".to_string()), Value::VecScalar(mat_c)),
        (Vid("x".to_string()), Value::VecScalar(vec![x0])),
        (Vid("w".to_string()), Value::VecScalar(vec![w0])),
    ])
}
