use zippel::*;
use std::path::PathBuf;
use backend::ArkBls12_381;
<<<<<<< HEAD
use share::Ctx;

fn main() {
    println!("=== Marginalize (ArkBls12_381, compile-only) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/marginalize/marginalize.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile(&Ctx::new());
    println!("Compilation:    ✓ OK");

    // Static analysis (completeness & ZK)
    println!("\n--- Static Analysis ---");
    let analysis_args = ZippelArgs::new(PathBuf::from("examples/marginalize/marginalize.zippel"));
    let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
    let analysis = analysis_handler.minimal_analysis();
    match &analysis.completeness {
        Ok(()) => println!("Completeness:   ✓"),
        Err(e) => println!("Completeness:   ✗ {}", e),
    }
    match &analysis.zk {
        Ok(()) => println!("ZK:             ✓"),
        Err(e) => println!("ZK:             ✗ {}", e),
    }

fn main() {
    println!("Starting marginalize example");
    // Path relative to workspace root when running: cargo run --example marginalize
    let args = ZippelArgs::new(PathBuf::from("examples/marginalize.zippel"))
        .with_pdf(PathBuf::from("marginalize_example.pdf"));

    // Use a tiny field (mod 17) so the numbers that appear in the
    // marginalize test are small and easy to understand.
    let mut handler: zippel::ZippelHandler<ArkField17> = ZippelHandler::new(args);

    println!("Compiling...");
    handler.compile();
    println!("Compilation:    ✓ OK");
>>>>>>> 9327b6c (Cleanup)
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
    // and we care about e(0), e(1), e(2) where e(t) = Σ_{y∈{0,1}} poly(t, y).
    let num_variables: Value<ArkField17> = Value::Index(2);
    let max_degree: Value<ArkField17> = Value::Index(2);

    // Round 0: no variable fixed yet; we marginalize over first variable t and sum over y.
    // This yields e(t) = 4t² + 4t + 2, so e(0)=2, e(1)=10, e(2)=9 (matching marginalize_proto).
    let round: Value<ArkField17> = Value::Index(0);

    // Challenge is only used when round > 0; for round 0 we still need to supply it.
    let challenge: Value<ArkField17> = Value::random(&mut rng, &ATyp::scalar());

    Ctx::from_iter([
        (Vid("poly".to_string()), poly),
        (Vid("num_variables".to_string()), num_variables),
        (Vid("max_degree".to_string()), max_degree),
        (Vid("round".to_string()), round),
        (Vid("challenge".to_string()), challenge),
    ])
}

