use zippel::*;
use std::path::PathBuf;
use backend::{ArkBls12_381, Value, ATyp};
use lang::id::Vid;
use share::Ctx;

fn main() {
    println!("Starting MLE example");
    println!("Current working directory: {:?}", std::env::current_dir().unwrap());
    let args = ZippelArgs::new(PathBuf::from("mle_test.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile();
    println!("Compiled and wrote PDF");
    let inputs = prover_create_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    let proof = handler.run_prover(prover_scheduled, inputs);
    println!("Ran prover");

    let verifier_scheduled = handler.default_schedule_verifier();
    let verifier_result = handler.run_verifier(verifier_scheduled, proof);
    println!("Verifier result for mle test: {:?}", verifier_result);
    println!("Finished MLE example");

    handler.analyze_completeness();
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let inputs = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("x".to_string()), Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar())),
    ]);

    return inputs;
}