use backend::{ATyp, ArkField17, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

fn main() {
    println!("=== IPA Field (ArkField17) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/ipa_field/ipa_field.zippel"));
    let mut handler: zippel::ZippelHandler<ArkField17> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &2usize);
    handler.compile(&sizes);

    let inputs = prover_create_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let proof = handler.run_prover(prover_scheduled, inputs);
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkField17>(&proof);
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

    // Static analysis (completeness & ZK)
    println!("\n--- Static Analysis ---");
    let analysis_start = Instant::now();
    let analysis_result = std::panic::catch_unwind(|| {
        let analysis_args = ZippelArgs::new(PathBuf::from("examples/ipa_field/ipa_field.zippel"));
        let mut analysis_handler: ZippelHandler<ArkField17> = ZippelHandler::new(analysis_args);
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

fn prover_create_inputs() -> Ctx<Vid, Value<ArkField17>> {
    let mut rng = rand::rngs::OsRng;
    let n_val_const = 4;

    let u_aux_base: Value<ArkField17> = Value::<ArkField17>::random(&mut rng, &ATyp::scalar());

    let g_vec: Value<ArkField17> =
        Value::<ArkField17>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let h_vec: Value<ArkField17> =
        Value::<ArkField17>::random(&mut rng, &ATyp::vec_scalar(n_val_const));

    let a_vec_witness: Value<ArkField17> =
        Value::<ArkField17>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let b_vec_witness: Value<ArkField17> =
        Value::<ArkField17>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let ip_val_claimed: Value<ArkField17> = a_vec_witness.clone().dot(b_vec_witness.clone());
    let p_initial_commitment: Value<ArkField17> =
        g_vec.clone().dot(a_vec_witness.clone()) + h_vec.clone().dot(b_vec_witness.clone());

    let inputs = Ctx::<Vid, Value<ArkField17>>::from_iter([
        (Vid("g_vec".to_string()), g_vec),
        (Vid("h_vec".to_string()), h_vec),
        (
            Vid("p_initial_commitment".to_string()),
            p_initial_commitment,
        ),
        (Vid("ip_val_claimed".to_string()), ip_val_claimed),
        (Vid("u_aux_base".to_string()), u_aux_base),
        (Vid("a_vec_witness".to_string()), a_vec_witness),
        (Vid("b_vec_witness".to_string()), b_vec_witness),
    ]);

    return inputs;
}
