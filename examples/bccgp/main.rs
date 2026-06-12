use backend::{ATyp, ArkSecp256k1, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

fn main() {
    println!("=== BCCGP 2016 IPA (ArkSecp256k1) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/bccgp/bccgp.zippel"));
    let mut handler: zippel::ZippelHandler<ArkSecp256k1> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &6usize);
    handler.compile(&sizes);

    let inputs = prover_create_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let proof = handler
        .run_prover(prover_scheduled, inputs)
        .expect("run_prover failed");
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkSecp256k1>(&proof);
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
        let analysis_args = ZippelArgs::new(PathBuf::from("examples/bccgp/bccgp.zippel"));
        let mut analysis_handler: ZippelHandler<ArkSecp256k1> = ZippelHandler::new(analysis_args);
        analysis_handler.minimal_analysis()
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

fn prover_create_inputs() -> Ctx<Vid, Value<ArkSecp256k1>> {
    let mut rng = rand::rngs::OsRng;
    let n_val_const = 64;

    let g_vec: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n_val_const));
    let h_vec: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n_val_const));

    let a_vec: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let b_vec: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec_scalar(n_val_const));

    let c_val: Value<ArkSecp256k1> = a_vec.clone().dot(b_vec.clone());
    let p_commitment: Value<ArkSecp256k1> =
        g_vec.clone().dot(a_vec.clone()) + h_vec.clone().dot(b_vec.clone());

    Ctx::<Vid, Value<ArkSecp256k1>>::from_iter([
        (Vid("g_vec".to_string()), g_vec),
        (Vid("h_vec".to_string()), h_vec),
        (Vid("p_commitment".to_string()), p_commitment),
        (Vid("c_val".to_string()), c_val),
        (Vid("a_vec".to_string()), a_vec),
        (Vid("b_vec".to_string()), b_vec),
    ])
}
