use backend::{ATyp, ArkBls12_381, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

// Need to match Zippel decl
const N_VAL: usize = 10240;
const M_VAL: usize = 1280;

fn main() {
    println!("=== Benchmark (ArkBls12_381, N={}, M={}) ===", N_VAL, M_VAL);
    let args = ZippelArgs::new(PathBuf::from("examples/benchmark/benchmark.zippel"));
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("N_val_const"), &N_VAL);
    sizes.insert(&Tid::new("M_val_const"), &M_VAL);
    handler.compile(&sizes);

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

    println!("\n--- Static Analysis ---");
    let analysis_start = Instant::now();
    let analysis_result = std::panic::catch_unwind(|| {
        let analysis_args = ZippelArgs::new(PathBuf::from("examples/benchmark/benchmark.zippel"));
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

    let g_a_vec: Value<ArkBls12_381> = Value::random(&mut rng, &ATyp::vec(&ATyp::g1(), N_VAL));
    let g_b_vec: Value<ArkBls12_381> = Value::random(&mut rng, &ATyp::vec(&ATyp::g1(), M_VAL));
    let a: Value<ArkBls12_381> = Value::random(&mut rng, &ATyp::vec_scalar(N_VAL));
    let b: Value<ArkBls12_381> = Value::random(&mut rng, &ATyp::vec_scalar(M_VAL));

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("g_a_vec".to_string()), g_a_vec),
        (Vid("g_b_vec".to_string()), g_b_vec),
        (Vid("a".to_string()), a),
        (Vid("b".to_string()), b),
    ])
}
