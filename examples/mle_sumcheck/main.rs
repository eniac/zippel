use ark_ff::Zero;
use ark_poly::DenseMultilinearExtension;
use ark_std::UniformRand;
use backend::VirtualPolynomial;
use backend::poly_variant::PolyVariant;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

#[path = "../common/analysis.rs"]
mod common;

const NUM_VARS: usize = 10;

fn main() {
    let zippel_file =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/mle_sumcheck/mle_sumcheck.zippel");
    let num_vars = NUM_VARS;

    println!("=== Multilinear Sumcheck (ArkBls12_381) ===");
    println!("num_vars:       {num_vars}");
    let args = ZippelArgs::new(zippel_file.clone());
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("NUM_VARS"), &num_vars);
    sizes.insert(&Tid::new("MAX_DEGREE_CONST"), &1usize);
    handler.compile(&sizes);

    let inputs = prover_create_inputs(num_vars);
    common::run_prover_and_verify(&mut handler, &inputs);

    println!("\n--- Static Analysis ---");
    let analysis_args = ZippelArgs::new(zippel_file);
    let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
    let mut analysis_sizes = Ctx::new();
    analysis_sizes.insert(&Tid::new("NUM_VARS"), &2usize);
    analysis_sizes.insert(&Tid::new("MAX_DEGREE_CONST"), &1usize);
    analysis_handler.compile(&analysis_sizes);

    common::time_analysis!("Completeness", analysis_handler.analyze_completeness());
    common::time_analysis!("ZK", analysis_handler.analyze_knowledge());
}

fn prover_create_inputs(num_vars: usize) -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as ArkConfig>::F;
    let eval_count = 1usize << num_vars;
    let mut rng = rand::rngs::OsRng;
    let base_evals: Vec<F> = (0..eval_count).map(|_| F::rand(&mut rng)).collect();

    let claimed_sum: F = base_evals.iter().fold(F::zero(), |acc, val| acc + val);

    let base = VirtualPolynomial::from_poly(PolyVariant::DenseMle(
        DenseMultilinearExtension::from_evaluations_vec(num_vars, base_evals),
    ));
    let poly = Value::Poly(base);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("claimed_sum".to_string()), Value::Scalar(claimed_sum)),
        (Vid("p".to_string()), poly),
    ])
}
