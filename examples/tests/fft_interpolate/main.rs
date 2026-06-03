use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use backend::ArkConfig;
use backend::{ArkField17, Value};
use lang::id::Vid;
use share::Ctx;
use std::path::PathBuf;
use std::time::Instant;
use zippel::*;

// Toggle this to compare runtime behavior:
// - true  => roots-of-unity interpolate path
// - false => arbitrary-point interpolate fallback path
const RUN_ROOTS_CASE: bool = true;

fn main() {
    let zippel_path = PathBuf::from("examples/tests/fft_interpolate/fft_interpolate.zippel");
    let subgraph = if RUN_ROOTS_CASE {
        "fft_interpolate_roots"
    } else {
        "fft_interpolate_random"
    };
    let args = ZippelArgs::new(zippel_path).with_subgraph(subgraph.to_string());
    let mut handler: ZippelHandler<ArkField17> = ZippelHandler::new(args);

    println!("=== FFT/Interpolate (ArkField17) ===");
    println!(
        "Mode: {}",
        if RUN_ROOTS_CASE {
            "roots-of-unity"
        } else {
            "arbitrary-points"
        }
    );

    handler.compile(&Ctx::new());
    let inputs = if RUN_ROOTS_CASE {
        inputs_roots()
    } else {
        inputs_random()
    };

    let prover_sched = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let proof = handler
        .run_prover(prover_sched, inputs)
        .expect("run_prover failed");
    let prover_elapsed = prover_start.elapsed();

    let verifier_sched = handler.default_schedule_verifier();
    let verifier_start = Instant::now();
    let verifier_result = handler
        .run_verifier(verifier_sched, proof)
        .expect("run_verifier failed");
    let verifier_elapsed = verifier_start.elapsed();

    let result = check_verification(verifier_result);
    println!("Prover time:   {prover_elapsed:.2?}");
    println!("Verifier time: {verifier_elapsed:.2?}");
    if result.passed {
        println!("Verification:  ✓ PASSED");
    } else {
        println!("Verification:  ✗ FAILED");
        std::process::exit(1);
    }
}

fn inputs_roots() -> Ctx<Vid, Value<ArkField17>> {
    let domain = GeneralEvaluationDomain::<<ArkField17 as ArkConfig>::F>::new(16)
        .expect("size-16 domain should exist in F17");
    let points = domain.elements().collect::<Vec<_>>();
    Ctx::from_iter([
        (
            Vid("coeffs".to_string()),
            Value::VecIndex(vec![3, 2, 5, 7, 1, 4, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16]),
        ),
        (Vid("points".to_string()), Value::VecScalar(points)),
    ])
}

fn inputs_random() -> Ctx<Vid, Value<ArkField17>> {
    Ctx::from_iter([
        (
            Vid("coeffs".to_string()),
            Value::VecIndex(vec![3, 2, 5, 7, 1, 4, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16]),
        ),
        // Same field values shuffled; distinct points keep interpolation well-defined,
        // and this ordering avoids the FFT-domain fast-path check.
        (
            Vid("points".to_string()),
            Value::VecIndex(vec![1, 3, 5, 7, 9, 11, 13, 15, 2, 4, 6, 8, 10, 12, 14, 16]),
        ),
    ])
}
