// Multivariate ZeroCheck PIOP example driver.
//
// Builds a random satisfying instance with NUM_POINTS hypercube points and
// runs the ZeroCheck protocol from hyperplonk_zerocheck.zippel on it.

use ark_ff::Field;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use rand::Rng;
use share::Ctx;
use std::{path::PathBuf, thread, time::Instant};
use zippel::*;

// ZeroCheck dimension. The proto is parametric over s = log2(num_points);
// here we instantiate s = 2 by passing S = 2 into the compile context, and
// num_points = 2^S = 4 follows. Bump S to scale up the example.
const S: usize = 2;
const NUM_POINTS: usize = 1 << S; // |B_s| = 2^S

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

    println!("=== HyperPlonk ZeroCheck PIOP ===");
    println!("num_points = {NUM_POINTS}, s = log num_points = {S}");

    let args = ZippelArgs::new(zippel_file.clone());
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &S);
    handler.compile(&sizes);

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

/// A satisfying ZeroCheck instance: three length-`num_points` MLE evaluation
/// vectors `a`, `b`, `c` with `c = a ⊙ b` (Hadamard) on every hypercube
/// point, so that `f(x) = a(x)·b(x) - c(x)` vanishes on B_s.
struct ZeroCheckInstance<F> {
    a: Vec<F>,
    b: Vec<F>,
    c: Vec<F>,
}

/// Build a random satisfying ZeroCheck instance: draw `a` and `b` uniformly,
/// set `c[i] = a[i] · b[i]`.
fn random_zerocheck<F, R>(rng: &mut R, num_points: usize) -> ZeroCheckInstance<F>
where
    F: Field,
    R: Rng + ?Sized,
{
    let a: Vec<F> = (0..num_points).map(|_| F::rand(rng)).collect();
    let b: Vec<F> = (0..num_points).map(|_| F::rand(rng)).collect();
    let c: Vec<F> = a.iter().zip(b.iter()).map(|(x, y)| *x * *y).collect();
    ZeroCheckInstance { a, b, c }
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as ArkConfig>::F;
    let mut rng = rand::rngs::OsRng;

    // -------------------------------------------------------------------
    // Generate a random satisfying ZeroCheck instance.
    //
    //   a, b, c (length NUM_POINTS each)  — MLE evaluations with c = a ⊙ b
    //
    // Replace `random_zerocheck(...)` with explicit Vec<F> constants below
    // if you want to pin a specific instance.
    // -------------------------------------------------------------------
    let inst = random_zerocheck::<F, _>(&mut rng, NUM_POINTS);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("a_evs".to_string()), Value::VecScalar(inst.a)),
        (Vid("b_evs".to_string()), Value::VecScalar(inst.b)),
        (Vid("c_evs".to_string()), Value::VecScalar(inst.c)),
    ])
}
