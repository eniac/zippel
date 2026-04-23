use zippel::*;
use std::{path::PathBuf, time::Instant};
use backend::{ArkBls12_381, ArkConfig, Value, ATyp};
use lang::id::{Tid, Vid};
use share::Ctx;
use ark_std::UniformRand;

fn main() {
    println!("=== Hyrax PoDP (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/hyrax_podp/hyrax_podp.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &4);
    handler.compile(&sizes);

    let inputs = prover_create_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let proof = handler.run_prover(prover_scheduled, inputs);
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkBls12_381>(&proof);
    println!("Prover time:    {prover_elapsed:.2?}");
    println!("Proof size:     {proof_bytes} bytes ({} elements)", proof.len());

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
        let analysis_args = ZippelArgs::new(PathBuf::from("examples/hyrax_podp/hyrax_podp.zippel"));
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
    let n = 4;
    
    // Sample scalar vectors x_vec and a_vec
    let x_vec = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n));
    let a_vec = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n));
    
    // Calculate dot product y = <x_vec, a_vec>
    let y = x_vec.clone().dot(a_vec.clone());

    // Sample scalar randomness
    let r_xi = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let r_tau = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);

    // Sample group elements and bases
    let g_vec = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n));
    let g = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let h = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);

    // Compute commitments:
    // tau = g * y + h * r_tau
    let tau_val = match y.clone() {
        Value::Scalar(y_scalar) => g * y_scalar + h * r_tau,
        _ => unreachable!(),
    };

    // xi = h * r_xi + sum(g_i * x_i)
    let g_dot_x = g_vec.clone().dot(x_vec.clone());
    let xi_val = match g_dot_x {
        Value::G1(gx_sum) => h * r_xi + gx_sum,
        _ => unreachable!(),
    };

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("x_vec".to_string()), x_vec),
        (Vid("r_xi".to_string()), Value::Scalar(r_xi)),
        (Vid("y".to_string()), y),
        (Vid("r_tau".to_string()), Value::Scalar(r_tau)),
        (Vid("g_vec".to_string()), g_vec),
        (Vid("a_vec".to_string()), a_vec),
        (Vid("g".to_string()), Value::G1(g)),
        (Vid("h".to_string()), Value::G1(h)),
        (Vid("xi".to_string()), Value::G1(xi_val)),
        (Vid("tau".to_string()), Value::G1(tau_val)),
    ])
}
