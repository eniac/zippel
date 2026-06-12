use ark_ff::fields::Field;
use ark_std::UniformRand;
use backend::{ATyp, ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::{path::PathBuf, thread, time::Instant};
use zippel::*;

const KZG_EXAMPLE_STACK_SIZE: usize = 256 * 1024 * 1024;
const PUBLIC_INPUT_NAMES: &[&str] = &["eval_point", "eval_result", "gen_g1", "gen_g2", "srs_g2_s"];

fn main() {
    let worker = thread::Builder::new()
        .name("zippel-kzg-example".to_string())
        .stack_size(KZG_EXAMPLE_STACK_SIZE)
        .spawn(run_kzg_example)
        .expect("failed to spawn kzg example worker thread");
    if let Err(payload) = worker.join() {
        std::panic::resume_unwind(payload);
    }
}

fn run_kzg_example() {
    println!("=== KZG (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/kzg/kzg.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("N"), &2);
    handler.compile(&sizes);

    let inputs = prover_create_inputs();
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

    println!("\n--- Static Analysis ---");
    // Analyze completeness/ZK at the same (small) N the prover demonstrates.
    // kzg's `where` clause contains `for i in 0..N-1`, which is empty (and
    // ill-typed) at the auto-minimized N=1, so analyze at the compiled N=2
    // rather than via `minimal_analysis()`.
    let analysis_result = std::panic::catch_unwind(|| {
        let analysis_args = ZippelArgs::new(PathBuf::from("examples/kzg/kzg.zippel"));
        let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
        let mut analysis_sizes = Ctx::new();
        analysis_sizes.insert(&Tid::new("N"), &2);
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

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;

    let n_size = 2;
    let gen_g1_input = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let gen_g1: Value<ArkBls12_381> = Value::G1(gen_g1_input);

    let gen_g2_input = <ArkBls12_381 as ArkConfig>::G2::rand(&mut rng);
    let gen_g2: Value<ArkBls12_381> = Value::G2(gen_g2_input);

    let poly_coeffs: Value<ArkBls12_381> =
        Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_size));
    let eval_point: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let tau_input = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);

    let srs_g1: Value<ArkBls12_381> = Value::VecG1((0..n_size).map(|_| gen_g1_input).collect())
        * Value::VecScalar((0..n_size).map(|i| tau_input.pow([i as u64])).collect());

    let eval_point_val: Value<ArkBls12_381> = Value::Vec(
        (0..n_size)
            .map(|i| eval_point.clone() ^ Value::Index(i))
            .collect(),
    );

    let eval_result: Value<ArkBls12_381> = poly_coeffs.clone().dot(eval_point_val);

    let srs_g2_s: Value<ArkBls12_381> = Value::G2(gen_g2_input * tau_input);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("poly_coeffs".to_string()), poly_coeffs),
        (Vid("eval_point".to_string()), eval_point),
        (Vid("eval_result".to_string()), eval_result),
        (Vid("srs_g1".to_string()), srs_g1),
        (Vid("gen_g1".to_string()), gen_g1),
        (Vid("gen_g2".to_string()), gen_g2),
        (Vid("srs_g2_s".to_string()), srs_g2_s),
    ])
}
