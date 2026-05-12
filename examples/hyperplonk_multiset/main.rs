// MultiSet Check PIOP example driver.
//
// Builds two 2-variable MLE evaluation vectors f, g where g is a random
// permutation of f, then runs the multiset-equality protocol.

use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use rand::seq::SliceRandom;
use share::Ctx;
use std::{path::PathBuf, thread, time::Instant};
use zippel::*;

const WORKER_STACK_BYTES: usize = 64 * 1024 * 1024;

fn main() {
    thread::Builder::new()
        .name("hyperplonk-multiset".into())
        .stack_size(WORKER_STACK_BYTES)
        .spawn(run)
        .expect("failed to spawn worker thread")
        .join()
        .expect("worker thread panicked");
}

fn run() {
    let zippel_file = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/hyperplonk_multiset/hyperplonk_multiset.zippel");

    println!("=== HyperPlonk MultiSet Check PIOP (s = 2) ===");

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

    // Random length-4 vector and a random permutation of it.
    let f: Vec<F> = (0..4).map(|_| F::rand(&mut rng)).collect();
    let mut g = f.clone();
    g.shuffle(&mut rng);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("f_evs".to_string()), Value::VecScalar(f)),
        (Vid("g_evs".to_string()), Value::VecScalar(g)),
    ])
}
