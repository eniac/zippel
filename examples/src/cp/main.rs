use zippel::*;
use std::path::PathBuf;
use backend::{ArkBls12_381, Value, ATyp};
use lang::id::Vid;
use share::Ctx;

fn main() {
    let args = ZippelArgs::new(PathBuf::from("cp.zippel"))
        .with_pdf(PathBuf::from("cp.pdf"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile();

    let inputs = prover_create_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    let proof = handler.run_prover(prover_scheduled, inputs);


    let verifier_scheduled = handler.default_schedule_verifier();
    let verifier_result = handler.run_verifier(verifier_scheduled, proof);
    println!("Verifier result: {:?}", verifier_result);


    // handler.analyze_completeness();
    // handler.analyze_knowledge();
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;

    let beta: Value<ArkBls12_381> = Value::random(&mut rng, &ATyp::scalar());
    let g: Value<ArkBls12_381> = Value::random(&mut rng, &ATyp::g1());
    let u: Value<ArkBls12_381> = Value::random(&mut rng, &ATyp::g1());

    let v = g.clone() * beta.clone();
    let w = u.clone() * beta.clone();

    let inputs = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("beta".to_string()), beta),
        (Vid("g".to_string()), g),
        (Vid("u".to_string()), u),
        (Vid("v".to_string()), v),
        (Vid("w".to_string()), w),
    ]);

    inputs
}