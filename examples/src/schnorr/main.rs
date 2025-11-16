use zippel::*;
use std::path::PathBuf;
use backend::{ArkBls12_381, Value, ATyp};
use lang::id::Vid;
use share::Ctx;

fn main() {
    let args = ZippelArgs::new(PathBuf::from("schnorr.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile();

    // let inputs = prover_create_inputs();
    // let prover_scheduled = handler.default_schedule_prover();
    // let proof = handler.run_prover(prover_scheduled, inputs);


    // let verifier_scheduled = handler.default_schedule_verifier();
    // let verifier_result = handler.run_verifier(verifier_scheduled, proof);
    // println!("Verifier result: {:?}", verifier_result);


    handler.analyze_completeness();
    handler.analyze_knowledge();
}

