use ark_ff::fields::Field;
use ark_std::UniformRand;
use backend::{ATyp, ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

fn main() {
    println!("=== KZG (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/kzg/kzg.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &2);
    handler.compile(&sizes);

    let inputs = prover_create_inputs();
    let public_inputs = inputs
        .clone()
        .into_iter()
        .filter(|(vid, _)| vid.0 != "poly_coeffs")
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

    let args = ZippelArgs::new(PathBuf::from("examples/kzg/kzg.zippel"));
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

    // Static analysis (completeness & ZK)
    println!("\n--- Static Analysis ---");
    let analysis_start = Instant::now();
    let analysis_result = std::panic::catch_unwind(|| {
        let analysis_args = ZippelArgs::new(PathBuf::from("examples/kzg/kzg.zippel"));
        let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
        analysis_handler.minimal_analysis()
    });
    let analysis_elapsed = analysis_start.elapsed();
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
    println!("Analysis time:  {analysis_elapsed:.2?}");
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;

    let n_size = 2;
    let g_input = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let g: Value<ArkBls12_381> = Value::G1(g_input);

    let h_input = <ArkBls12_381 as ArkConfig>::G2::rand(&mut rng);
    let h: Value<ArkBls12_381> = Value::G2(h_input);

    let s_temp: Value<ArkBls12_381> = Value::G1(<ArkBls12_381 as ArkConfig>::G1::rand(&mut rng));

    // let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Uni(n_size));
    // let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Uni(n_size));

    // let p: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Uni(n_size));
    let p: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_size));
    let z: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let tau_input = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    // let tau = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let tau = Value::<ArkBls12_381>::Scalar(tau_input);

    let ss_g: Value<ArkBls12_381> = Value::VecG1((0..n_size).map(|_| g_input).collect());

    let ss_index = Value::VecScalar((0..n_size).map(|i| tau_input.pow([i as u64])).collect());

    let ss = ss_g.clone() * ss_index.clone();
    let _s = s_temp.clone() * tau.clone();

    let z_val: Value<ArkBls12_381> =
        Value::Vec((0..n_size).map(|i| z.clone() ^ Value::Index(i)).collect());

    let y: Value<ArkBls12_381> = p.clone().dot(z_val.clone());
    // let y =  Value::<ArBls12_381>::random(&mut rng, &ATyp::scalar());
    let h_val: Value<ArkBls12_381> = Value::G2(h_input * tau_input);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("poly_coeffs".to_string()), p),
        (Vid("gen_g1".to_string()), g),
        (Vid("gen_g2".to_string()), h),
        (Vid("eval_point".to_string()), z),
        (Vid("eval_result".to_string()), y),
        (Vid("srs_g1".to_string()), ss),
        (Vid("srs_g2_s".to_string()), h_val),
    ])
}
