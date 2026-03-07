use zippel::*;
use std::{path::PathBuf, time::Instant};
use backend::{ArkConfig, ArkSecp256k1, Value, ATyp};
use ark_ff::{One, Zero};
use lang::id::Vid;
use share::Ctx;

fn main() {
    println!("=== Zerocheck (ArkSecp256k1) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/zerocheck.zippel"));
    let mut handler: zippel::ZippelHandler<ArkSecp256k1> = ZippelHandler::new(args);
    handler.compile();

    let inputs = prover_create_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let proof = handler.run_prover(prover_scheduled, inputs);
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkSecp256k1>(&proof);
    println!("Prover time:    {prover_elapsed:.2?}");
    println!("Proof size:     {proof_bytes} bytes ({} elements)", proof.len());

    let verifier_scheduled = handler.default_schedule_verifier();
    let verifier_start = Instant::now();
    let verifier_result = handler.run_verifier(verifier_scheduled, proof);
    let verifier_elapsed = verifier_start.elapsed();
    let result = check_verification(verifier_result);
    println!("Verifier time:  {verifier_elapsed:.2?}");
    if result.passed {
        println!("Verification:   ✓ PASSED");
    } else {
        println!("Verification:   ✗ FAILED");
        std::process::exit(1);
    }
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkSecp256k1>> {
    let mut rng = rand::rngs::OsRng;

    // Keep this in sync with `N:2` in `examples/zerocheck.zippel`.
    let zero = <ArkSecp256k1 as ArkConfig>::F::zero();
    let one = <ArkSecp256k1 as ArkConfig>::F::one();

    // Choose v(X) = X, encoded as coefficients [0, 1], then store as a polynomial.
    let v_coeffs = vec![zero, one];
    let v = Value::<ArkSecp256k1>::VecScalar(v_coeffs.clone()).value_poly();

    // Pick random alpha and set p(X) = alpha * X so that q(X) = p(X)/v(X) = alpha.
    let alpha_val: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::scalar());
    let alpha = alpha_val.into_scalar();
    let p_coeffs: Vec<<ArkSecp256k1 as ArkConfig>::F> =
        v_coeffs.iter().map(|c| *c * alpha).collect();
    let p = Value::<ArkSecp256k1>::VecScalar(p_coeffs).value_poly();

    Ctx::<Vid, Value<ArkSecp256k1>>::from_iter([
        (Vid("p".to_string()), p),
        (Vid("v".to_string()), v),
    ])
}
