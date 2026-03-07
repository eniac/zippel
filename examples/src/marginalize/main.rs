use zippel::*;
use std::path::PathBuf;
use backend::{ArkField17, Value, ATyp};
use lang::id::Vid;
use share::Ctx;

fn main() {
    println!("Starting marginalize example");
    let args = ZippelArgs::new(PathBuf::from("marginalize.zippel"))
        .with_pdf(PathBuf::from("marginalize_example.pdf"));

    // Use a tiny field (mod 17) so the numbers that appear in the
    // marginalize test are small and easy to understand.
    let mut handler: zippel::ZippelHandler<ArkField17> = ZippelHandler::new(args);

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

    println!("Finished marginalize example");
}

fn create_inputs() -> Ctx<Vid, Value<ArkField17>> {
    let mut rng = rand::rngs::OsRng;

    // Build a polynomial over two variables (x, y) that is the product
    // of two MLEs:
    //
    //   f(x, y)  = x + y
    //   g(x, y)  = 2x + 2y
    //   poly(x,y) = f(x,y) * g(x,y) = (x + y) * (2x + 2y)
    //
    // Each MLE is represented by its evaluations over the Boolean
    // hypercube {(0,0), (0,1), (1,0), (1,1)} in that order.
    let mle1_evals: Value<ArkField17> = Value::VecIndex(vec![
        0, // f(0,0) = 0
        1, // f(0,1) = 1
        1, // f(1,0) = 1
        2, // f(1,1) = 2
    ]);
    let mle2_evals: Value<ArkField17> = Value::VecIndex(vec![
        0, // g(0,0) = 0
        2, // g(0,1) = 2
        2, // g(1,0) = 2
        4, // g(1,1) = 4
    ]);

    let mle1_poly = mle1_evals.value_mle();
    let mle2_poly = mle2_evals.value_mle();

    let poly: Value<ArkField17> = match (mle1_poly, mle2_poly) {
        (Value::Poly(p1), Value::Poly(p2)) => {
            Value::Poly(p1.poly_mul(&p2).expect("Polynomial multiplication failed"))
        }
        _ => panic!("Expected polynomials for MLEs"),
    };

    // Two variables (x, y) in the sum-check sense, degree 2 in x,
    // and we care about g(0), g(1), g(2).
    let num_variables: Value<ArkField17> = Value::Index(2);
    let max_degree: Value<ArkField17> = Value::Index(2);

    // Extra public scalar input `y` used in the Zippel spec.
    let y: Value<ArkField17> = Value::random(&mut rng, &ATyp::scalar());

    // Challenge is irrelevant for the evaluation test; we just sample it.
    let challenge: Value<ArkField17> = Value::random(&mut rng, &ATyp::scalar());

    Ctx::from_iter([
        (Vid("poly".to_string()), poly),
        (Vid("num_variables".to_string()), num_variables),
        (Vid("max_degree".to_string()), max_degree),
        (Vid("round".to_string()), Value::Index(1)),
        (Vid("y".to_string()), y),
        (Vid("challenge".to_string()), challenge),
    ])
}

