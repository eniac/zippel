// Permutation PIOP example driver.
//
// Picks a random length-4 vector f, a random permutation σ on the 4 indices,
// and sets g[i] = f[σ(i)] so that g(x) = f(σ(x)) on every hypercube point.
// Runs the HyperPlonk §3.5 permutation protocol on (f, g, s_σ).

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
        .name("hyperplonk-permutation".into())
        .stack_size(WORKER_STACK_BYTES)
        .spawn(run)
        .expect("failed to spawn worker thread")
        .join()
        .expect("worker thread panicked");
}

fn run() {
    let zippel_file = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/hyperplonk_permutation/hyperplonk_permutation.zippel");

    println!("=== HyperPlonk Permutation PIOP (s = 2) ===");

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

    // Random f, a random permutation sigma of {0..3}, and g[i] = f[sigma(i)].
    let f: Vec<F> = (0..4).map(|_| F::rand(&mut rng)).collect();
    let mut sigma: Vec<usize> = (0..4).collect();
    sigma.shuffle(&mut rng);
    let g: Vec<F> = sigma.iter().map(|&j| f[j]).collect();

    // s_sigma(x) = [sigma(x)]: hypercube evaluations are sigma's indices,
    // cast into the field.
    let s_sigma: Vec<F> = sigma.iter().map(|&j| F::from(j as u64)).collect();

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("f_evs".to_string()), Value::VecScalar(f)),
        (Vid("g_evs".to_string()), Value::VecScalar(g)),
        (Vid("s_sigma_evs".to_string()), Value::VecScalar(s_sigma)),
    ])
}
