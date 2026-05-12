// Multivariate ZeroCheck PIOP example driver.
//
// Builds three 2-variable MLEs a, b, c with a o b = c (Hadamard) on the
// 4-point boolean hypercube, then runs the ZeroCheck protocol on
// f = a*b - c.

use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;
use std::{path::PathBuf, thread, time::Instant};
use zippel::*;

const WORKER_STACK_BYTES: usize = 64 * 1024 * 1024;

fn main() {
    thread::Builder::new()
        .name("hyperplonk-zerocheck".into())
        .stack_size(WORKER_STACK_BYTES)
        .spawn(run)
        .expect("failed to spawn worker thread")
        .join()
        .expect("worker thread panicked");
}

fn run() {
    let zippel_file = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/hyperplonk_zerocheck/hyperplonk_zerocheck.zippel");

    println!("=== HyperPlonk ZeroCheck PIOP (s = 2) ===");

    let args = ZippelArgs::new(zippel_file.clone());
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile(&Ctx::new());

    let inputs = prover_create_inputs();

    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let proof = handler.run_prover(prover_scheduled, inputs);
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkBls12_381>(&proof);
    println!("Prover time:    {prover_elapsed:.2?}");
    println!(
        "Proof size:     {proof_bytes} bytes ({} elements)",
        proof.len()
    );

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

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as ArkConfig>::F;
    let mut rng = rand::rngs::OsRng;

    // Pick random a and b, compute c = a o b entrywise so the ZeroCheck
    // statement (a*b - c)(x) = 0 holds on every hypercube point.
    let a: Vec<F> = (0..4).map(|_| F::rand(&mut rng)).collect();
    let b: Vec<F> = (0..4).map(|_| F::rand(&mut rng)).collect();
    let c: Vec<F> = a.iter().zip(b.iter()).map(|(x, y)| *x * *y).collect();

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("a_evs".to_string()), Value::VecScalar(a)),
        (Vid("b_evs".to_string()), Value::VecScalar(b)),
        (Vid("c_evs".to_string()), Value::VecScalar(c)),
    ])
}
