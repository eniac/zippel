// ProductCheck PIOP example driver.
//
// Picks a random 2-variable MLE f, computes the product s = prod_x f(x) over
// the 4-point boolean hypercube, builds the auxiliary product-tree polynomial
// ṽ as in HyperPlonk §3.3, and runs the protocol.

use ark_ff::Zero;
use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;
use std::{path::PathBuf, thread, time::Instant};
use zippel::*;

const WORKER_STACK_BYTES: usize = 64 * 1024 * 1024;

fn main() {
    thread::Builder::new()
        .name("hyperplonk-productcheck".into())
        .stack_size(WORKER_STACK_BYTES)
        .spawn(run)
        .expect("failed to spawn worker thread")
        .join()
        .expect("worker thread panicked");
}

fn run() {
    let zippel_file = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/hyperplonk_productcheck/hyperplonk_productcheck.zippel");

    println!("=== HyperPlonk ProductCheck PIOP (s = 2) ===");

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

    // Random non-zero leaves f(x) on the hypercube.
    let f: Vec<F> = (0..4).map(|_| F::rand(&mut rng)).collect();

    // Build the product-tree MLE ṽ on B_3 (8 evaluations, LSB-first):
    //   v[idx] = ṽ(X_0 = idx_bit_0, X_1 = idx_bit_1, X_2 = idx_bit_2)
    //
    //   X_0 = 0  (leaves):              v[idx] = f(X_1, X_2)
    //   X_0 = 1  (internal nodes):      v[idx] = ṽ(X_1, X_2, 0) * ṽ(X_1, X_2, 1)
    //
    // and we pin ṽ(1, 1, 1) := 0 so that the recursion at the self-referential
    // hypercube point trivially satisfies its constraint.
    let v_0 = f[0]; // (X_0=0, X_1=0, X_2=0): f(0, 0)
    let v_2 = f[1]; // (X_0=0, X_1=1, X_2=0): f(1, 0)
    let v_4 = f[2]; // (X_0=0, X_1=0, X_2=1): f(0, 1)
    let v_6 = f[3]; // (X_0=0, X_1=1, X_2=1): f(1, 1)

    let v_1 = f[0] * f[2]; // ṽ(1, 0, 0) = ṽ(0, 0, 0) * ṽ(0, 0, 1) = f(0,0) * f(0,1)
    let v_5 = f[1] * f[3]; // ṽ(1, 0, 1) = ṽ(0, 1, 0) * ṽ(0, 1, 1) = f(1,0) * f(1,1)
    let v_3 = v_1 * v_5; // ṽ(1, 1, 0) = root = f(0,0) f(0,1) f(1,0) f(1,1) = product
    let v_7 = F::zero(); // ṽ(1, 1, 1) — chosen 0 to satisfy the recursion.

    let v_evs = vec![v_0, v_1, v_2, v_3, v_4, v_5, v_6, v_7];
    let claimed = v_3;

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("f_evs".to_string()), Value::VecScalar(f)),
        (Vid("v_evs".to_string()), Value::VecScalar(v_evs)),
        (Vid("claimed".to_string()), Value::Scalar(claimed)),
    ])
}
