// Spartan-core example driver.
//
// Builds a random satisfying R1CS instance with NUM_CONSTRAINTS rows and runs
// the Spartan-core protocol from spartan.zippel on it.
//
// spartan.zippel is currently hard-coded for square matrices with
// num_constraints = 4 (s = log num_constraints = 2) and z-length 4. Within
// those dimensions the witness `w`, the public instance `io`, and the
// constraint matrices A, B, C can be any satisfying values — see
// `random_r1cs` below for the construction.

use ark_ff::Field;
use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use rand::Rng;
use share::Ctx;
use std::{path::PathBuf, thread, time::Instant};
use zippel::*;

// R1CS dimensions baked into spartan.zippel.
// Square matrices (rows == columns == |z|), so we require
//   NUM_CONSTRAINTS == WITNESS_LEN + IO_LEN + 1.
const NUM_CONSTRAINTS: usize = 4; // m: number of R1CS rows (= |z|)
const IO_LEN: usize = 1; // |io|: public-input length
const WITNESS_LEN: usize = 2; // |w|: private-witness length

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
    println!(
        "num_constraints = {NUM_CONSTRAINTS}, s = log num_constraints = 2, |io| = {IO_LEN}, |w| = {WITNESS_LEN}"
    );

    let args = ZippelArgs::new(zippel_file.clone());
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile(&Ctx::new());

    let inputs = prover_create_inputs();

    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let proof = handler
        .run_prover(prover_scheduled, inputs)
        .expect("run_prover failed");
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkBls12_381>(&proof);
    println!("Prover time:    {prover_elapsed:.2?}");
    println!(
        "Proof size:     {proof_bytes} bytes ({} elements)",
        proof.len()
    );

    let verifier_scheduled = handler.default_schedule_verifier();
    let verifier_start = Instant::now();
    let verifier_result = handler
        .run_verifier(verifier_scheduled, proof)
        .expect("run_verifier failed");
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
    // skipped here
    let _ = zippel_file;
}

/// A satisfying R1CS instance: three matrices A, B, C (length-`m·n`,
/// row-major), the public-input vector `io`, and the private witness `w`.
/// Per spartan.zippel the variable vector is `z = w ++ io ++ [1]`.
struct R1csInstance<F> {
    mat_a: Vec<F>,
    mat_b: Vec<F>,
    mat_c: Vec<F>,
    io: Vec<F>,
    w: Vec<F>,
}

/// Build a random satisfying R1CS instance for the given witness and
/// instance, using square matrices of size `num_constraints × num_vars`
/// where `num_vars = witness.len() + instance.len() + 1`.
fn random_r1cs<F, R>(
    rng: &mut R,
    num_constraints: usize,
    witness: &[F],
    instance: &[F],
) -> R1csInstance<F>
where
    F: Field,
    R: Rng + ?Sized,
{
    let num_vars = witness.len() + instance.len() + 1;
    assert_eq!(
        num_vars, num_constraints,
        "spartan.zippel uses square matrices: witness.len() + instance.len() + 1 must equal num_constraints",
    );

    // z = w ++ io ++ [1]   (matches the layout in spartan.zippel)
    let mut z = Vec::with_capacity(num_vars);
    z.extend_from_slice(witness);
    z.extend_from_slice(instance);
    z.push(F::from(1u64));

    let constant_col = num_vars - 1;
    let mut mat_a = vec![F::from(0u64); num_constraints * num_vars];
    let mut mat_b = vec![F::from(0u64); num_constraints * num_vars];
    let mut mat_c = vec![F::from(0u64); num_constraints * num_vars];

    for i in 0..num_constraints {
        let a_row: Vec<F> = (0..num_vars).map(|_| F::rand(rng)).collect();
        let b_row: Vec<F> = (0..num_vars).map(|_| F::rand(rng)).collect();
        let mut c_row: Vec<F> = (0..num_vars).map(|_| F::rand(rng)).collect();

        let az_i: F = a_row.iter().zip(z.iter()).map(|(x, y)| *x * *y).sum();
        let bz_i: F = b_row.iter().zip(z.iter()).map(|(x, y)| *x * *y).sum();
        let target = az_i * bz_i;

        // c_row · z = c_row[const] · 1 + Σ_{j ≠ const} c_row[j] · z[j]
        // Solve c_row[const] so that c_row · z = target.
        let other_terms: F = c_row
            .iter()
            .zip(z.iter())
            .enumerate()
            .filter(|(j, _)| *j != constant_col)
            .map(|(_, (c, zj))| *c * *zj)
            .sum();
        c_row[constant_col] = target - other_terms;

        for j in 0..num_vars {
            mat_a[i * num_vars + j] = a_row[j];
            mat_b[i * num_vars + j] = b_row[j];
            mat_c[i * num_vars + j] = c_row[j];
        }
    }

    R1csInstance {
        mat_a,
        mat_b,
        mat_c,
        io: instance.to_vec(),
        w: witness.to_vec(),
    }
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as ArkConfig>::F;
    let mut rng = rand::rngs::OsRng;

    // -------------------------------------------------------------------
    // Fill in the witness and instance here.
    //
    //   witness  (length WITNESS_LEN)  — private inputs of the proof
    //   instance (length IO_LEN)       — public  inputs of the proof
    //
    // By default both are uniformly random; replace either line with
    // concrete F constants to pin a specific assignment.
    // -------------------------------------------------------------------
    let witness: Vec<F> = (0..WITNESS_LEN).map(|_| F::rand(&mut rng)).collect();
    let instance: Vec<F> = (0..IO_LEN).map(|_| F::rand(&mut rng)).collect();

    // z = witness ++ instance ++ [1]   (matches the layout in spartan.zippel)
    let one = F::from(1u64);
    let mut z: Vec<F> = Vec::with_capacity(NUM_CONSTRAINTS);
    z.extend_from_slice(&witness);
    z.extend_from_slice(&instance);
    z.push(one);

    // Generate random A, B, C that make this z satisfy R1CS row-by-row.
    let r1cs = random_r1cs::<F, _>(&mut rng, NUM_CONSTRAINTS, &witness, &instance);

    // Sanity check: every row holds (A z)_i · (B z)_i = (C z)_i.
    for i in 0..NUM_CONSTRAINTS {
        let az_i: F = (0..NUM_CONSTRAINTS)
            .map(|j| r1cs.mat_a[i * NUM_CONSTRAINTS + j] * z[j])
            .sum();
        let bz_i: F = (0..NUM_CONSTRAINTS)
            .map(|j| r1cs.mat_b[i * NUM_CONSTRAINTS + j] * z[j])
            .sum();
        let cz_i: F = (0..NUM_CONSTRAINTS)
            .map(|j| r1cs.mat_c[i * NUM_CONSTRAINTS + j] * z[j])
            .sum();
        assert_eq!(
            az_i * bz_i,
            cz_i,
            "row {i} of the random R1CS instance is unsatisfied",
        );
    }

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("mat_a".to_string()), Value::VecScalar(r1cs.mat_a)),
        (Vid("mat_b".to_string()), Value::VecScalar(r1cs.mat_b)),
        (Vid("mat_c".to_string()), Value::VecScalar(r1cs.mat_c)),
        (Vid("io".to_string()), Value::VecScalar(r1cs.io)),
        (Vid("w".to_string()), Value::VecScalar(r1cs.w)),
    ])
}
