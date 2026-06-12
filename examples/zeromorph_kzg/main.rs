use ark_ff::{One, Zero, fields::Field};
use ark_std::UniformRand;
use backend::{ATyp, ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

const PUBLIC_INPUT_NAMES: &[&str] = &["u", "v", "srs_g1", "gen_g1", "gen_g2", "srs_g2"];

fn main() {
    println!("=== Zeromorph Hiding KZG ===");
    let args = ZippelArgs::new(PathBuf::from("examples/zeromorph_kzg/zeromorph_kzg.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    let n_size = 2;
    sizes.insert(&Tid::new("N"), &n_size);
    handler.compile(&sizes);

    let inputs = prover_create_inputs(n_size as usize);
    let public_inputs = inputs
        .clone()
        .into_iter()
        .filter(|(vid, _)| PUBLIC_INPUT_NAMES.contains(&vid.0.as_str()))
        .collect::<Ctx<Vid, Value<ArkBls12_381>>>();

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

    let args = ZippelArgs::new(PathBuf::from("examples/zeromorph_kzg/zeromorph_kzg.zippel"));
    let mut verifier_handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    verifier_handler.compile(&sizes);
    verifier_handler.set_public_inputs(public_inputs);

    let verifier_scheduled = verifier_handler.default_schedule_verifier();
    let verifier_start = Instant::now();
    let verifier_result = verifier_handler
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

    println!("\n--- Static Analysis ---");
    let analysis_result = std::panic::catch_unwind(|| {
        let analysis_args =
            ZippelArgs::new(PathBuf::from("examples/zeromorph_kzg/zeromorph_kzg.zippel"));
        let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
        let mut analysis_sizes = Ctx::new();
        analysis_sizes.insert(&Tid::new("N"), &n_size);
        analysis_handler.compile(&analysis_sizes);
        let completeness_start = Instant::now();
        let completeness = analysis_handler.analyze_completeness();
        let completeness_time = completeness_start.elapsed();
        let zk_start = Instant::now();
        let zk = analysis_handler.analyze_knowledge();
        let zk_time = zk_start.elapsed();
        AnalysisResult {
            completeness,
            zk,
            completeness_time,
            zk_time,
        }
    });
    match analysis_result {
        Ok(analysis) => {
            match &analysis.completeness {
                Ok(()) => println!("Completeness:   ✓"),
                Err(e) => println!("Completeness:   ✗ {}", e),
            }
            println!("Completeness time:  {:.2?}", analysis.completeness_time);
            match &analysis.zk {
                Ok(()) => println!("ZK:             ✓"),
                Err(e) => println!("ZK:             ✗ {}", e),
            }
            println!("ZK time:            {:.2?}", analysis.zk_time);
        }
        Err(_) => println!("Analysis:       ⚠ not supported (non-polynomial operations)"),
    }
}

fn prover_create_inputs(n_size: usize) -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;

    let g_input = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let g = Value::G1(g_input);

    let h_input = <ArkBls12_381 as ArkConfig>::G2::rand(&mut rng);
    let h = Value::G2(h_input);

    let tau_input = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let xi_input = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);

    let mut srs_g1_vec = vec![];
    for i in 0..n_size {
        srs_g1_vec.push(g_input * tau_input.pow([i as u64]));
    }
    srs_g1_vec.push(g_input * xi_input);
    let srs_g1 = Value::VecG1(srs_g1_vec);

    let tau_g2 = h_input * tau_input;
    let xi_g2 = h_input * xi_input;
    let srs_g2 = Value::VecG2(vec![tau_g2, xi_g2]);

    let p_coeffs_val = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_size));

    let u_input = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let u_val = Value::Scalar(u_input);

    let p_coeffs_unwrapped = match &p_coeffs_val {
        Value::VecScalar(v) => v.clone(),
        _ => panic!("Expected VecScalar"),
    };

    let mut v_input = <ArkBls12_381 as ArkConfig>::F::zero();
    let mut u_pow = <ArkBls12_381 as ArkConfig>::F::one();
    for i in 0..n_size {
        v_input += p_coeffs_unwrapped[i] * u_pow;
        u_pow *= u_input;
    }
    let v_val = Value::Scalar(v_input);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("p_coeffs".to_string()), p_coeffs_val),
        (Vid("u".to_string()), u_val),
        (Vid("v".to_string()), v_val),
        (Vid("srs_g1".to_string()), srs_g1),
        (Vid("srs_g2".to_string()), srs_g2),
        (Vid("gen_g1".to_string()), g),
        (Vid("gen_g2".to_string()), h),
    ])
}
