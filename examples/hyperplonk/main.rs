// HyperPlonk example driver (gate identity + wiring), s = 2.
//
// Builds a satisfying instance for the top-level HyperPlonk protocol:
//   - Master witness w ∈ F^4 (random).
//   - Random permutation σ on {0..3}.
//   - Wires:  a = w,  b[i] = w[σ(i)],  c = a ⊙ b (Hadamard product).
//   - Selectors:  q_L = q_R = q_C = 0,  q_M = 1,  q_O = -1.
//     Then the gate identity
//         q_L·a + q_R·b + q_O·c + q_M·a·b + q_C
//       = a·b - c = 0
//     holds on every hypercube point.
//   - Wiring identity: b(x) = a(σ(x)) by construction.
//
// The protocol is then expected to verify on (a, b, c, q_L, q_R, q_O, q_M,
// q_C, s_σ) where s_σ encodes σ as field elements (σ(i) → F::from(i)).

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
        .name("hyperplonk".into())
        .stack_size(WORKER_STACK_BYTES)
        .spawn(run)
        .expect("failed to spawn worker thread")
        .join()
        .expect("worker thread panicked");
}

fn run() {
    let zippel_file =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/hyperplonk/hyperplonk.zippel");

    println!("=== HyperPlonk (gate identity + wiring) (s = 2) ===");

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

    // Master witness w of length 4.
    let w: Vec<F> = (0..4).map(|_| F::rand(&mut rng)).collect();

    // Random permutation σ on {0..3}.
    let mut sigma: Vec<usize> = (0..4).collect();
    sigma.shuffle(&mut rng);

    // Wires.
    let a: Vec<F> = w.clone();
    let b: Vec<F> = sigma.iter().map(|&j| w[j]).collect();
    let c: Vec<F> = a.iter().zip(b.iter()).map(|(x, y)| *x * *y).collect();

    // Selectors: gate identity reduces to a·b - c = 0.
    let q_l = vec![F::from(0u64); 4];
    let q_r = vec![F::from(0u64); 4];
    let q_o = vec![-F::from(1u64); 4];
    let q_m = vec![F::from(1u64); 4];
    let q_c = vec![F::from(0u64); 4];

    // s_σ(x) = [σ(x)] as field elements.
    let s_sigma: Vec<F> = sigma.iter().map(|&j| F::from(j as u64)).collect();

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("a_evs".to_string()), Value::VecScalar(a)),
        (Vid("b_evs".to_string()), Value::VecScalar(b)),
        (Vid("c_evs".to_string()), Value::VecScalar(c)),
        (Vid("q_l_evs".to_string()), Value::VecScalar(q_l)),
        (Vid("q_r_evs".to_string()), Value::VecScalar(q_r)),
        (Vid("q_o_evs".to_string()), Value::VecScalar(q_o)),
        (Vid("q_m_evs".to_string()), Value::VecScalar(q_m)),
        (Vid("q_c_evs".to_string()), Value::VecScalar(q_c)),
        (Vid("s_sigma_evs".to_string()), Value::VecScalar(s_sigma)),
    ])
}
