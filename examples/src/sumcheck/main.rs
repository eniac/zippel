use zippel::*;
use std::path::PathBuf;
use backend::{ArkBls12_381, ArkConfig, Value, ATyp};
use lang::id::Vid;
use share::Ctx;
use ark_ff::Zero;

// Keep this in sync with `NUM_VARS_CONST` in `examples/sumcheck.zippel`.
const NUM_VARS: usize = 2;

fn main() {
    println!("Starting sum-check example");
    let args = ZippelArgs::new(PathBuf::from("sumcheck.zippel"))
        .with_pdf(PathBuf::from("sumcheck.pdf"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile();
    println!("Compiled and wrote PDF");

    let inputs = prover_create_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    let proof = handler.run_prover(prover_scheduled, inputs);
    println!("Ran prover");

    let verifier_scheduled = handler.default_schedule_verifier();
    let verifier_result = handler.run_verifier(verifier_scheduled, proof);
    println!("Verifier result for sum-check: {:?}", verifier_result);
    println!("Finished sum-check example");

    handler.analyze_completeness();
    handler.analyze_knowledge();
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let mut random_scalar = || {
        Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar()).into_scalar()
    };

    let eval_count = 1usize << NUM_VARS;
    let g_evals: Vec<_> = (0..eval_count).map(|_| random_scalar()).collect();

    let claimed_sum = g_evals.iter()
        .fold(<ArkBls12_381 as ArkConfig>::F::zero(), |acc, val| acc + val);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("claimed_sum".to_string()), Value::Scalar(claimed_sum)),
        (Vid("g_evals".to_string()), Value::VecScalar(g_evals.clone())),
    ])
}

