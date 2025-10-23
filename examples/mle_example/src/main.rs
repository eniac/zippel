use cli::*;
use std::path::PathBuf;
use backend::{ArkField17, Value, ATyp};
use lang::id::Vid;
use share::Ctx;

fn main() {
    let path = PathBuf::from("../mle_test.zippel");
    let args = CliArgs { file_path: path, pdf_path_opt: None, subgraph: None };
    let mut handler: cli::ZippelHandler<ArkField17> = ZippelHandler::new(args);
    handler.compile();
    handler.combined_graph_pdf("mle_test_prover_verifier1");

    let inputs = prover_create_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    let proof = handler.run_prover(prover_scheduled, inputs);


    let verifier_scheduled = handler.default_schedule_verifier();
    let verifier_result = handler.run_verifier(verifier_scheduled, proof);
    println!("Verifier result for mle test: {:?}", verifier_result);
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkField17>> {
    let mut rng = rand::rngs::OsRng;
    let mut inputs = Ctx::<Vid, Value<ArkField17>>::from_iter([
        (Vid("x".to_string()), Value::<ArkField17>::random(&mut rng, &ATyp::scalar())),
    ]);

    return inputs;
}