use zippel::*;
use std::path::PathBuf;
use backend::{ArkBls12_381, ArkConfig, Value, ATyp};
use backend::poly_variant::PolyVariant;
use ark_poly::DenseMultilinearExtension;
use lang::id::Vid;
use share::Ctx;
use ark_ff::Zero;

// Keep this in sync with `NUM_VARS_CONST` in `examples/sumcheck.zippel`.
const NUM_VARS: usize = 1;

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

    let half = eval_count / 2;
    let zero = <ArkBls12_381 as ArkConfig>::F::zero();
    let g1_0 = g_evals[0..half].iter().copied()
        .fold(zero, |acc, val| acc + val);
    let g1_1 = g_evals[half..].iter().copied()
        .fold(zero, |acc, val| acc + val);
    let round_claims = vec![g1_0, g1_1];

    let g_poly = DenseMultilinearExtension::from_evaluations_vec(NUM_VARS, g_evals.clone());
    let g_poly_value = Value::Poly(PolyVariant::DenseMle(g_poly));

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("claimed_sum".to_string()), Value::Scalar(claimed_sum)),
        (Vid("g_poly".to_string()), g_poly_value),
        (Vid("round_claims".to_string()), Value::VecScalar(round_claims)),
    ])
}

