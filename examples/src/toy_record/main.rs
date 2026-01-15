use zippel::*;
use std::path::PathBuf;
use backend::{ArkBls12_381, Value};
use lang::id::Vid;
use share::Ctx;

fn main() {
    println!("Starting toy_record example");
    let args = ZippelArgs::new(PathBuf::from("toy_record.zippel"))
        .with_pdf(PathBuf::from("toy_record.pdf"));
    
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    
    println!("Compiling...");
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        handler.compile();
    })) {
        Ok(_) => println!("Compiled and wrote PDF"),
        Err(_) => {
            println!("Compilation panicked!");
            return;
        }
    }
    
    let inputs = create_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    
    println!("Running prover...");
    let proof = handler.run_prover(prover_scheduled, inputs);
    println!("Ran prover");
    
    let verifier_scheduled = handler.default_schedule_verifier();
    
    println!("Running verifier...");
    let verifier_result = handler.run_verifier(verifier_scheduled, proof);
    println!("Verifier result: {:?}", verifier_result);
    
    handler.analyze_completeness();
    handler.analyze_knowledge();
    
    println!("Finished toy_record example");
}

fn create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let ctx = Ctx::new();
 
    
    ctx
}
