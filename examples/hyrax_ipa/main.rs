use zippel::*;
use std::{path::PathBuf, time::Instant};
use backend::{ArkBls12_381, ArkConfig, Value, ATyp};
use lang::id::{Tid, Vid};
use share::Ctx;
use ark_std::UniformRand;

fn main() {
    println!("=== Hyrax Log of Dot Product (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/hyrax_ipa/hyrax_ipa.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &6usize);
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
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let n_val_const = 64;
    
    // Private Witness Config
    let x_vec = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let a_vec = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let y = x_vec.clone().dot(a_vec.clone());

    let r_xi = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let r_tau = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);

    // Public Base and Elements
    let g_vec = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n_val_const));
    let g_base = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let h_base = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);

    // Compute \tau = g_base * y + h_base * r_tau
    let tau_val = match y.clone() {
        Value::Scalar(y_scalar) => g_base * y_scalar + h_base * r_tau,
        _ => unreachable!(),
    };

    // Compute \xi = h_base * r_xi + <g_vec, x_vec>
    let gx_dot = g_vec.clone().dot(x_vec.clone());
    let xi_val = match gx_dot {
        Value::G1(gx_sum) => h_base * r_xi + gx_sum,
        _ => unreachable!(),
    };

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("xi".to_string()), Value::G1(xi_val)),
        (Vid("tau".to_string()), Value::G1(tau_val)),
        (Vid("a_vec_public".to_string()), a_vec),
        (Vid("g_vec_public".to_string()), g_vec),
        (Vid("g_base".to_string()), Value::G1(g_base)),
        (Vid("h_base".to_string()), Value::G1(h_base)),
        (Vid("x_vec_private".to_string()), x_vec),
        (Vid("y_private".to_string()), y),
        (Vid("r_xi_private".to_string()), Value::Scalar(r_xi)),
        (Vid("r_tau_private".to_string()), Value::Scalar(r_tau)),
    ])
}
