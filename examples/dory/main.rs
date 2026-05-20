use backend::{ArkBls12_381, ArkConfig, ArkGroupOps, ArkPairingOps, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

fn main() {
    env_logger::init();
    println!("=== Dory Evaluation Proof (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/dory/dory.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    println!("Compiling Zippel files...");
    const LOG_N: usize = 8;
    let mut sizes: Ctx<Tid, usize> = Ctx::new();
    sizes.insert(&Tid::new("S"), &LOG_N);
    handler.compile(&sizes);
    println!("Compilation successful.");

    let inputs = prover_create_inputs();
    println!("Generating default schedule for prover...");
    let prover_scheduled = handler.default_schedule_prover();
    println!("Running prover...");
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

    println!("Generating default schedule for verifier...");
    let verifier_scheduled = handler.default_schedule_verifier();
    println!("Running verifier...");
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
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let n = 256;

    // Generate random vectors
    let u_vec = <ArkBls12_381 as ArkConfig>::G1Ops::vec_rand(&mut rng, n);
    let g_vec = <ArkBls12_381 as ArkConfig>::G2Ops::vec_rand(&mut rng, n);

    let gamma1 = <ArkBls12_381 as ArkConfig>::G1Ops::vec_rand(&mut rng, n);
    let gamma2 = <ArkBls12_381 as ArkConfig>::G2Ops::vec_rand(&mut rng, n);

    // Preprocessing: we need exactly log_2(n) gamma' arrays
    // For n=64, we need level 1 (size 32), ... down to level 6 (size 1).
    // The top-level inputs to dory_eval require just gamma1, gamma2, gamma1_prime, gamma2_prime, and their hashes
    // Since our protocol takes scalar variables directly, we will precompute exactly the hashes for n=64
    let gamma1_prime = <ArkBls12_381 as ArkConfig>::G1Ops::vec_rand(&mut rng, n / 2);
    let gamma2_prime = <ArkBls12_381 as ArkConfig>::G2Ops::vec_rand(&mut rng, n / 2);

    // Compute c1, c2, c3
    let c1 = <ArkBls12_381 as ArkConfig>::POps::billinear_vec_dot(&u_vec, &g_vec);
    let c2 = <ArkBls12_381 as ArkConfig>::POps::billinear_vec_dot(&u_vec, &gamma2);
    let c3 = <ArkBls12_381 as ArkConfig>::POps::billinear_vec_dot(&gamma1, &g_vec);

    // Hash levels construction for O(log n) Dory preprocessing
    let mut hash1_l_vec = Vec::new();
    let mut hash1_r_vec = Vec::new();
    let mut hash2_l_vec = Vec::new();
    let mut hash2_r_vec = Vec::new();
    let mut gamma_pair_ipp_vec = Vec::new();

    let mut current_n = n;
    let mut cur_gamma1 = gamma1.clone();
    let mut cur_gamma2 = gamma2.clone();

    while current_n > 1 {
        let half_n = current_n / 2;

        let g1_l = cur_gamma1[0..half_n].to_vec();
        let g1_r = cur_gamma1[half_n..current_n].to_vec();
        let g2_l = cur_gamma2[0..half_n].to_vec();
        let g2_r = cur_gamma2[half_n..current_n].to_vec();

        // The primes used for this round are the first half_n elements of the global primes
        let cur_g1_prime = gamma1_prime[0..half_n].to_vec();
        let cur_g2_prime = gamma2_prime[0..half_n].to_vec();

        let h1_l = <ArkBls12_381 as ArkConfig>::POps::billinear_vec_dot(&g1_l, &cur_g2_prime);
        let h1_r = <ArkBls12_381 as ArkConfig>::POps::billinear_vec_dot(&g1_r, &cur_g2_prime);
        let h2_l = <ArkBls12_381 as ArkConfig>::POps::billinear_vec_dot(&cur_g1_prime, &g2_l);
        let h2_r = <ArkBls12_381 as ArkConfig>::POps::billinear_vec_dot(&cur_g1_prime, &g2_r);
        let ipp = <ArkBls12_381 as ArkConfig>::POps::billinear_vec_dot(&cur_gamma1, &cur_gamma2);

        hash1_l_vec.push(h1_l);
        hash1_r_vec.push(h1_r);
        hash2_l_vec.push(h2_l);
        hash2_r_vec.push(h2_r);
        gamma_pair_ipp_vec.push(ipp);

        cur_gamma1 = cur_g1_prime;
        cur_gamma2 = cur_g2_prime;
        current_n = half_n;
    }

    let final_gamma1 = cur_gamma1[0];
    let final_gamma2 = cur_gamma2[0];

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("c1".to_string()), Value::GT(c1)),
        (Vid("c2".to_string()), Value::GT(c2)),
        (Vid("c3".to_string()), Value::GT(c3)),
        (Vid("hash1_l_vec".to_string()), Value::VecGT(hash1_l_vec)),
        (Vid("hash1_r_vec".to_string()), Value::VecGT(hash1_r_vec)),
        (Vid("hash2_l_vec".to_string()), Value::VecGT(hash2_l_vec)),
        (Vid("hash2_r_vec".to_string()), Value::VecGT(hash2_r_vec)),
        (
            Vid("gamma_pair_ipp_vec".to_string()),
            Value::VecGT(gamma_pair_ipp_vec),
        ),
        (Vid("final_gamma1".to_string()), Value::G1(final_gamma1)),
        (Vid("final_gamma2".to_string()), Value::G2(final_gamma2)),
        (Vid("gamma1".to_string()), Value::VecG1(gamma1)),
        (Vid("gamma2".to_string()), Value::VecG2(gamma2)),
        (Vid("gamma1_prime".to_string()), Value::VecG1(gamma1_prime)),
        (Vid("gamma2_prime".to_string()), Value::VecG2(gamma2_prime)),
        (Vid("u_vec".to_string()), Value::VecG1(u_vec)),
        (Vid("g_vec".to_string()), Value::VecG2(g_vec)),
    ])
}
