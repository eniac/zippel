use zippel::*;
use std::path::PathBuf;
use backend::{ArkBls12_381, Value, ATyp};
use lang::id::Vid;
use share::Ctx;

fn main() {
    println!("Starting toy_record example");
    let args = ZippelArgs::new(PathBuf::from("toy_record.zippel"))
        .with_pdf(PathBuf::from("toy_record_example.pdf"));
    
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    
    println!("Compiling...");
    handler.compile();
    println!("Compiled and wrote PDF");
    
    let inputs = create_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    
    println!("Running prover...");
    let proof = handler.run_prover(prover_scheduled, inputs);
    println!("Ran prover");
    
    let verifier_scheduled = handler.default_schedule_verifier();
    
    println!("Running verifier...");
    let verifier_result = handler.run_verifier(verifier_scheduled, proof);
    println!("Verifier result: {:?}", verifier_result);
    
    // handler.analyze_completeness();
    // handler.analyze_knowledge();
    
    println!("Finished toy_record example");
}

fn create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    
    let x: Value<ArkBls12_381> = Value::random(&mut rng, &ATyp::scalar());
    let y: Value<ArkBls12_381> = Value::random(&mut rng, &ATyp::scalar());
    let status_g1: Value<ArkBls12_381> = Value::random(&mut rng, &ATyp::g1());
    
    Ctx::from_iter([
        (Vid("x".to_string()), x),
        (Vid("y".to_string()), y),
        (Vid("status_g1".to_string()), status_g1),
    ])
}
