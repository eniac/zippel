use backend::{ArkConfig, HasOpFactory, Value};
use lang::id::Vid;
use share::Ctx;
use std::time::Instant;
use zippel::{ZippelHandler, check_verification, proof_size_bytes};

/// Run a named analysis pass, print the result immediately, and report timing.
///
/// Usage:
/// ```
/// time_analysis!("Completeness", handler.analyze_completeness());
/// time_analysis!("ZK", handler.analyze_knowledge());
/// time_analysis!("Soundness", handler.analyze_special_soundness(vec![2]));
/// ///
/// /// Note: the caller must have `use std::time::Instant;` or `use ark_std::Instant;`
/// /// in scope, since this macro uses `Instant::now()`.
/// ```
macro_rules! time_analysis {
    ($label:expr, $expr:expr) => {{
        let __start = std::time::Instant::now();
        match $expr {
            Ok(()) => println!("{}:   ✓", $label),
            Err(e) => println!("{}:   ✗ {}", $label, e),
        }
        println!("{} time:  {:.2?}", $label, __start.elapsed());
    }};
}

pub(crate) use time_analysis;

/// Run the prover and verifier for a compiled handler, printing timing and proof
/// size. Exits with code 1 if verification fails.
///
/// `C` is the backend config type (e.g. `ArkBls12_381`, `ArkSecp256k1`).
/// `handler` must already be compiled. `inputs` is the prover witness context.
pub fn run_prover_and_verify<C: ArkConfig + HasOpFactory>(
    handler: &mut ZippelHandler<C>,
    inputs: &Ctx<Vid, Value<C>>,
) {
    let prover_start = Instant::now();
    let proof = handler.run_prover(inputs).expect("run_prover failed");
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<C>(&proof);
    println!("Prover time:    {prover_elapsed:.2?}");
    println!(
        "Proof size:     {proof_bytes} bytes ({} elements)",
        proof.len()
    );

    let verifier_start = Instant::now();
    let verifier_result = handler
        .run_verifier(&proof, inputs)
        .expect("run_verifier failed");
    let verifier_elapsed = verifier_start.elapsed();
    let passed = check_verification(&verifier_result);
    println!("Verifier time:  {verifier_elapsed:.2?}");
    if passed {
        println!("Verification:   ✓ PASSED");
    } else {
        println!("Verification:   ✗ FAILED");
        std::process::exit(1);
    }
}
