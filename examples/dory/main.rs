use zippel::*;
use std::{path::PathBuf, time::Instant};
use backend::{ArkBls12_381, ArkConfig, Value, ArkGroupOps, ArkPairingOps, ArkScalarOps};
use lang::id::Vid;
use share::Ctx;
use ark_std::UniformRand;

fn main() {
    println!("=== Dory Evaluation Proof (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/dory.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    println!("Compiling Zippel files...");
    handler.compile();
    println!("Compilation successful.");

    let inputs = prover_create_inputs();
    println!("Generating default schedule for prover...");
    let prover_scheduled = handler.default_schedule_prover();
    println!("Running prover...");
    let prover_start = Instant::now();
    let proof = handler.run_prover(prover_scheduled, inputs);
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkBls12_381>(&proof);
    println!("Prover time:    {prover_elapsed:.2?}");
    println!("Proof size:     {proof_bytes} bytes ({} elements)", proof.len());

    println!("Generating default schedule for verifier...");
    let verifier_scheduled = handler.default_schedule_verifier();
    println!("Running verifier...");
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
    let mut rng = rand::rngs::OsRng;
    let n = 2;

    // Generate random vectors
    let u_vec = <ArkBls12_381 as ArkConfig>::G1Ops::vec_rand(&mut rng, n);
    let g_vec = <ArkBls12_381 as ArkConfig>::G2Ops::vec_rand(&mut rng, n);
    
    let gamma1 = <ArkBls12_381 as ArkConfig>::G1Ops::vec_rand(&mut rng, n);
    let gamma2 = <ArkBls12_381 as ArkConfig>::G2Ops::vec_rand(&mut rng, n);
    
    // Simulating gamma primes (just taking a random half-size vector for proof-of-concept)
    let gamma1_prime = <ArkBls12_381 as ArkConfig>::G1Ops::vec_rand(&mut rng, n / 2);
    let gamma2_prime = <ArkBls12_381 as ArkConfig>::G2Ops::vec_rand(&mut rng, n / 2);

    // Compute c1, c2, c3
    let c1 = <ArkBls12_381 as ArkConfig>::POps::billinear_vec_dot(&u_vec, &g_vec);
    let c2 = <ArkBls12_381 as ArkConfig>::POps::billinear_vec_dot(&u_vec, &gamma2);
    let c3 = <ArkBls12_381 as ArkConfig>::POps::billinear_vec_dot(&gamma1, &g_vec);

    // Preprocessing values
    let gamma_pair_ipp = <ArkBls12_381 as ArkConfig>::POps::billinear_vec_dot(&gamma1, &gamma2);
    
    // Hash L and R are just pairings of gamma halves
    let gamma1_L = gamma1[0..n/2].to_vec();
    let gamma1_R = gamma1[n/2..n].to_vec();
    
    let hash_L = <ArkBls12_381 as ArkConfig>::POps::billinear_vec_dot(&gamma1_L, &gamma2_prime);
    let hash_R = <ArkBls12_381 as ArkConfig>::POps::billinear_vec_dot(&gamma1_R, &gamma2_prime);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("c1".to_string()), Value::GT(c1)),
        (Vid("c2".to_string()), Value::GT(c2)),
        (Vid("c3".to_string()), Value::GT(c3)),
        (Vid("gamma1".to_string()), Value::VecG1(gamma1)),
        (Vid("gamma2".to_string()), Value::VecG2(gamma2)),
        (Vid("gamma1_prime".to_string()), Value::VecG1(gamma1_prime)),
        (Vid("gamma2_prime".to_string()), Value::VecG2(gamma2_prime)),
        (Vid("hash_L".to_string()), Value::GT(hash_L)),
        (Vid("hash_R".to_string()), Value::GT(hash_R)),
        (Vid("gamma_pair_ipp".to_string()), Value::GT(gamma_pair_ipp)),
        (Vid("u_vec".to_string()), Value::VecG1(u_vec)),
        (Vid("g_vec".to_string()), Value::VecG2(g_vec)),
    ])
}
