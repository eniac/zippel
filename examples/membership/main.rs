use ark_ff::fields::Field;
use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

fn main() {
    println!("=== Membership ===");
    let n_size = 2;
    let m_size = 2;
    assert!(n_size >= 1, "n_size must be at least 1");
    assert!(m_size >= 1, "m_size must be at least 1");
    let l_size = (n_size - 1) * m_size;
    let s_size = usize::max(n_size, l_size);

    let args = ZippelArgs::new(PathBuf::from("examples/membership/membership.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("N"), &n_size);
    sizes.insert(&Tid::new("M"), &m_size);
    sizes.insert(&Tid::new("S"), &s_size);
    handler.compile(&sizes);

    let inputs = prover_create_inputs(n_size, m_size);
    let public_inputs = inputs
        .clone()
        .into_iter()
        .filter(|(vid, _)| vid.0 != "f_coeffs")
        .collect::<Ctx<Vid, Value<ArkBls12_381>>>();
    let prover_start = Instant::now();
    let proof = handler.run_prover(&inputs).expect("run_prover failed");
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkBls12_381>(&proof);
    println!("Prover time:    {prover_elapsed:.2?}");
    println!(
        "Proof size:     {proof_bytes} bytes ({} elements)",
        proof.len()
    );

    let args = ZippelArgs::new(PathBuf::from("examples/membership/membership.zippel"));
    let mut verifier_handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    verifier_handler.compile(&sizes);
    verifier_handler.set_public_inputs(public_inputs);
    let verifier_start = Instant::now();
    let verifier_result = verifier_handler
        .run_verifier(&proof)
        .expect("run_verifier failed");
    let verifier_elapsed = verifier_start.elapsed();
    let passed = check_verification(&verifier_result);
    println!("Verifier time:  {verifier_elapsed:.2?}");
    if passed {
        println!("Verification:   ✓ PASSED");
    } else {
        println!("Verification:   ✗ FAILED");
        std::process::exit(1);
    }

    println!("\n--- Static Analysis ---");
    let analysis_args = ZippelArgs::new(PathBuf::from("examples/membership/membership.zippel"));
    let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
    let mut analysis_sizes = Ctx::new();
    analysis_sizes.insert(&Tid::new("N"), &n_size);
    analysis_sizes.insert(&Tid::new("M"), &m_size);
    analysis_sizes.insert(&Tid::new("S"), &s_size);
    analysis_handler.compile(&analysis_sizes);

    let completeness_start = Instant::now();
    match analysis_handler.analyze_completeness() {
        Ok(()) => println!("Completeness:    ✓"),
        Err(e) => println!("Completeness:    ✗ {}", e),
    }
    println!("Completeness time: {:.2?}", completeness_start.elapsed());

    let zk_start = Instant::now();
    match analysis_handler.analyze_knowledge() {
        Ok(()) => println!("ZK:              ✓"),
        Err(e) => println!("ZK:              ✗ {}", e),
    }
    println!("ZK time:         {:.2?}", zk_start.elapsed());
}

fn prover_create_inputs(n_size: usize, m_size: usize) -> Ctx<Vid, Value<ArkBls12_381>> {
    assert!(n_size >= 1, "n_size must be at least 1");
    assert!(m_size >= 1, "m_size must be at least 1");
    let mut rng = rand::rngs::OsRng;
    let l_size = (n_size - 1) * m_size;
    let s_size = usize::max(n_size, l_size);

    let g_input = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let g: Value<ArkBls12_381> = Value::G1(g_input);

    let h_input = <ArkBls12_381 as ArkConfig>::G2::rand(&mut rng);
    let h: Value<ArkBls12_381> = Value::G2(h_input);

    let tau_input = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);

    // SRS G1 up to size S
    let ss_g: Value<ArkBls12_381> = Value::VecG1((0..s_size).map(|_| g_input).collect());
    let ss_index = Value::VecScalar((0..s_size).map(|i| tau_input.pow([i as u64])).collect());
    let ss = ss_g * ss_index;

    // SRS G2_s
    let h_val: Value<ArkBls12_381> = Value::G2(h_input * tau_input);

    // Set S of size M (choose 0, 1, 2, ..., M-1)
    let s_val = Value::VecScalar(
        (0..m_size)
            .map(|i| <ArkBls12_381 as ArkConfig>::F::from(i as u64))
            .collect(),
    );

    // f_coeffs. Constant term must be one of the elements of S (we choose S[0] which is 0).
    let mut f_coeffs_vec = vec![<ArkBls12_381 as ArkConfig>::F::from(0u64)];
    for _ in 1..n_size {
        f_coeffs_vec.push(<ArkBls12_381 as ArkConfig>::F::rand(&mut rng));
    }
    let f_coeffs = Value::VecScalar(f_coeffs_vec);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("f_coeffs".to_string()), f_coeffs),
        (Vid("s".to_string()), s_val),
        (Vid("gen_g1".to_string()), g),
        (Vid("gen_g2".to_string()), h),
        (Vid("srs_g1".to_string()), ss),
        (Vid("srs_g2_s".to_string()), h_val),
    ])
}
