use zippel::*;
use std::{path::PathBuf, time::Instant};
use backend::{ArkBls12_381, ArkConfig, Value, ATyp};
use lang::id::{Tid, Vid};
use share::Ctx;
use ark_std::UniformRand;
use ark_ff::fields::Field;

fn main() {
    println!("=== KZG (ArkBls12_381) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/kzg_test.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &2);
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
    
    let n_size = 2;
    let g_input = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let g: Value<ArkBls12_381> = Value::G1(g_input.clone());

    let h_input = <ArkBls12_381 as ArkConfig>::G2::rand(&mut rng);
    let h: Value<ArkBls12_381> = Value::G2(h_input.clone());
    
    let s_temp: Value<ArkBls12_381> = Value::G1(<ArkBls12_381 as ArkConfig>::G1::rand(&mut rng));
    

    // let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Uni(n_size));
    // let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Uni(n_size));
  
    // let p: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Uni(n_size));
    let p: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_size));
    let z: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let tau_input = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    // let tau = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let tau = Value::<ArkBls12_381>::Scalar(tau_input.clone());

    let ss_g: Value<ArkBls12_381> = Value::VecG1((0..n_size).map(|_| {
        g_input.clone()
    }).collect());

    let ss_index = Value::VecScalar((0..n_size).map(|i |{
        tau_input.clone().pow(&[i as u64])
    }).collect());

    let ss = ss_g.clone() * ss_index.clone();
    let _s = s_temp.clone() * tau.clone();

    let z_val: Value<ArkBls12_381> = Value::Vec((0..n_size).map(|i| {
        z.clone() ^ Value::Index(i)
    }).collect());
    
    let y: Value<ArkBls12_381> = p.clone().dot(z_val.clone());
    // let y =  Value::<ArBls12_381>::random(&mut rng, &ATyp::scalar());
    let h_val: Value<ArkBls12_381> = Value::G2(h_input.clone() * tau_input.clone());

    let inputs = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
            (Vid("p".to_string()), p),
            (Vid("g".to_string()), g),
            (Vid("h".to_string()), h),
            (Vid("z".to_string()), z),
            (Vid("y".to_string()), y),
            (Vid("ss".to_string()), ss),
            (Vid("h_val".to_string()), h_val),
        ]);
    return inputs;
}