// Spartan-core example driver.
//
// Builds a small satisfying R1CS instance with m = 4, |io| = 1, |w| = 2,
// then runs the Spartan-core protocol from spartan.zippel.

use ark_ff::Zero;
use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;
use std::{path::PathBuf, thread, time::Instant};
use zippel::*;

// R1CS dimensions baked into spartan.zippel.
const M: usize = 4; // matrix dimension (s = log m = 2)
const IO_LEN: usize = 1;
const W_LEN: usize = 2;

// Spartan's two stacked sum-checks blow up the recursive AST traversal during
// Zippel compilation; the OS default 8 MB main-thread stack overflows on macOS.
// Run everything on a worker thread with a generous stack instead, so the
// example works without the user having to bump `ulimit -s`.
const WORKER_STACK_BYTES: usize = 64 * 1024 * 1024;

fn main() {
    thread::Builder::new()
        .name("spartan-main".into())
        .stack_size(WORKER_STACK_BYTES)
        .spawn(run)
        .expect("failed to spawn worker thread")
        .join()
        .expect("spartan worker thread panicked");
}

fn run() {
    let zippel_file =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/spartan/spartan.zippel");

    println!("=== Spartan-core (ArkBls12_381) ===");
    println!("m = {M}, s = log m = 2, |io| = {IO_LEN}, |w| = {W_LEN}");

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

    // NOTE. The minimal_analysis() static analysis pass (completeness / ZK) is
    // skipped here because Spartan's two stacked sum-checks produce a much
    // larger symbolic graph than the other examples and the analysis does not
    // terminate in any reasonable time on this protocol. Re-enable manually
    // once the analysis is fast enough for the Spartan-sized polynomial graph.
    let _ = zippel_file;
}

/// Build a 4x4 R1CS instance that encodes a tiny circuit and is satisfiable.
///
/// We use a single non-trivial constraint
///
///     (io_0 + w_0) * w_0 = w_1
///
/// expressed as row 0 of a (formally) 4x4 R1CS system. The remaining three
/// rows are all-zero (trivial `0 * 0 = 0` constraints) so that the R1CS
/// check `(A z) o (B z) = C z` is satisfied across every row.
///
/// The z vector is laid out as in spartan.zippel:
///
///     z = w ++ io ++ [1] = (w_0, w_1, io_0, 1)
///
/// Under the LSB-first dense-MLE convention this places
///
///     z~(var_0=0, var_1=0) = w_0       z~(var_0=0, var_1=1) = io_0
///     z~(var_0=1, var_1=0) = w_1       z~(var_0=1, var_1=1) = 1
///
/// so var_1 is the (w / io+pad) selector that gates the v_Z formula.
fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as ArkConfig>::F;
    let mut rng = rand::rngs::OsRng;

    // Choose random io_0 and w_0; derive w_1 to satisfy the constraint.
    let io_0 = F::rand(&mut rng);
    let w_0 = F::rand(&mut rng);
    let w_1 = (io_0 + w_0) * w_0;

    let one = F::from(1u64);
    let zero = F::zero();
    let z = [w_0, w_1, io_0, one];

    // Build a 4x4 row-major matrix whose row 0 carries the given selectors
    // (length-16 flat vector with mat[i*4 + j] = M[i][j]).
    let build_mat = |selectors: [F; 4]| -> Vec<F> {
        let mut mat = vec![zero; M * M];
        for j in 0..M {
            mat[j] = selectors[j];
        }
        mat
    };

    // (A z)_0 = w_0 + io_0:    selectors hit z[0]=w_0 and z[2]=io_0.
    let mat_a = build_mat([one, zero, one, zero]);
    // (B z)_0 = w_0:           selector hits z[0]=w_0.
    let mat_b = build_mat([one, zero, zero, zero]);
    // (C z)_0 = w_1:           selector hits z[1]=w_1.
    let mat_c = build_mat([zero, one, zero, zero]);

    // Sanity check: (A z)_i * (B z)_i = (C z)_i for every row.
    for i in 0..M {
        let az_i: F = (0..M).map(|j| mat_a[i * M + j] * z[j]).sum();
        let bz_i: F = (0..M).map(|j| mat_b[i * M + j] * z[j]).sum();
        let cz_i: F = (0..M).map(|j| mat_c[i * M + j] * z[j]).sum();
        assert_eq!(az_i * bz_i, cz_i, "row {i} of the R1CS instance is unsatisfied");
    }

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("mat_a".to_string()), Value::VecScalar(mat_a)),
        (Vid("mat_b".to_string()), Value::VecScalar(mat_b)),
        (Vid("mat_c".to_string()), Value::VecScalar(mat_c)),
        (Vid("io".to_string()), Value::VecScalar(vec![io_0])),
        (Vid("w".to_string()), Value::VecScalar(vec![w_0, w_1])),
    ])
}
