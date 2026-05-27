use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

const N: usize = 3; // Total dimension of z
const N_PUB: usize = 1; // Public input dimension
const M: usize = 1; // Number of constraints (rows in A, B, C)

fn main() {
    println!(
        "=== R1CS Sigma (ArkBls12_381, N={}, n={}, m={}) ===",
        N, N_PUB, M
    );
    let args = ZippelArgs::new(PathBuf::from("examples/r1cs_sigma/r1cs_sigma.zippel"));
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

    // Static analysis (completeness & ZK)
    println!("\n--- Static Analysis ---");
    let analysis_result = std::panic::catch_unwind(|| {
        let analysis_args = ZippelArgs::new(PathBuf::from("examples/r1cs_sigma/r1cs_sigma.zippel"));
        let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
        analysis_handler.minimal_analysis()
    });
    match analysis_result {
        Ok(analysis) => {
            match &analysis.completeness {
                Ok(()) => println!("Completeness:   ✓"),
                Err(e) => println!("Completeness:   ✗ {}", e),
            }
            match &analysis.zk {
                Ok(()) => println!("ZK:             ✓"),
                Err(e) => println!("ZK:             ✗ {}", e),
            }
        }
        Err(_) => println!("Analysis:       ⚠ not supported (non-polynomial operations)"),
    }
}

/// Build a valid R1CS instance (A, B, C, x, w) such that Az ∘ Bz = Cz.
///
/// We construct a simple 1x3 system with 1 constraint over z = (x0, w0, w1):
///   Constraint 0:  x0 * w0 = w1        (1 public variable by private variable constraint)
///
/// Row-major 1×3 matrices:
///   A = [[1,0,0]]   selects: x0
///   B = [[0,1,0]]   selects: w0
///   C = [[0,0,1]]   selects: w1
///
fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as ArkConfig>::F;
    let mut rng = rand::rngs::OsRng;

    // Pick a random public input x0 and private w0
    let x0 = F::rand(&mut rng);
    let w0 = F::rand(&mut rng);

    // Derive w1 from constraints
    let w1 = x0 * w0;

    // A (1×3)
    let mat_a: Vec<F> = vec![F::from(1u64), F::from(0u64), F::from(0u64)];

    // B (1×3)
    let mat_b: Vec<F> = vec![F::from(0u64), F::from(1u64), F::from(0u64)];

    // C (1×3)
    let mat_c: Vec<F> = vec![F::from(0u64), F::from(0u64), F::from(1u64)];

    // Verify the R1CS relation: Az ∘ Bz = Cz
    let z = [x0, w0, w1];
    for i in 0..M {
        let az_i: F = (0..N).map(|j| mat_a[i * N + j] * z[j]).sum();
        let bz_i: F = (0..N).map(|j| mat_b[i * N + j] * z[j]).sum();
        let cz_i: F = (0..N).map(|j| mat_c[i * N + j] * z[j]).sum();
        assert_eq!(az_i * bz_i, cz_i, "R1CS constraint {} failed", i);
    }

    // Commitment key: random group elements
    let ck: Vec<<ArkBls12_381 as ArkConfig>::G1> = (0..M)
        .map(|_| <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng))
        .collect();
    let h_base = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("ck".to_string()), Value::VecG1(ck)),
        (Vid("h_base".to_string()), Value::G1(h_base)),
        (Vid("mat_A".to_string()), Value::VecScalar(mat_a)),
        (Vid("mat_B".to_string()), Value::VecScalar(mat_b)),
        (Vid("mat_C".to_string()), Value::VecScalar(mat_c)),
        (Vid("x".to_string()), Value::VecScalar(vec![x0])),
        (Vid("w".to_string()), Value::VecScalar(vec![w0, w1])),
    ])
}
