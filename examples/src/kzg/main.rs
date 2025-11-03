use cli::*;
use std::path::PathBuf;
use backend::{ArkBls12_381, ArkConfig, Value, ATyp};
use lang::id::Vid;
use share::Ctx;
use ark_std::UniformRand;
use ark_ff::fields::Field;

fn main() {
    println!("Starting KZG example");
    println!("Current working directory: {:?}", std::env::current_dir().unwrap());
    let path = PathBuf::from("kzg_test.zippel");
    let args = CliArgs { 
        file_path: path, 
        pdf_path_opt: Some(PathBuf::from("kzg_test.pdf")),
        subgraph: None 
    };
    
    let mut handler: cli::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile();
    println!("Compiled and wrote PDF");
    let inputs = prover_create_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    let proof = handler.run_prover(prover_scheduled, inputs);
    println!("Ran prover");

    let verifier_scheduled = handler.default_schedule_verifier();
    let verifier_result = handler.run_verifier(verifier_scheduled, proof);
    println!("Verifier result for mle test: {:?}", verifier_result);
    println!("Finished KZG example");
    
    handler.analyze_completeness();
}


fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    
    let n_size = 2;
    let g_input = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let g: Value<ArkBls12_381> = Value::G1(g_input.clone());

    let h_input = <ArkBls12_381 as ArkConfig>::G2::rand(&mut rng);
    let h: Value<ArkBls12_381> = Value::G2(h_input.clone());
    
    let y: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let s_temp: Value<ArkBls12_381> = Value::G1(<ArkBls12_381 as ArkConfig>::G1::rand(&mut rng));
    

    // let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Uni(n_size));
    // let b = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Uni(n_size));
  
    // let p: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::Uni(n_size));
    let p: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_size));
    let z: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let tau_input = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    // let tau = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    let tau = Value::<ArkBls12_381>::Scalar(tau_input.clone());

    let ss_g: Value<ArkBls12_381> = Value::VecG1((0..n_size).map(|i| {
        // println!("i: {}", i);
        // println!("test: {}", s.clone() ^ Value::Index(i));
        // s.clone() ^ Value::Index(i)
        g_input.clone()
    }).collect());

    let ss_index = Value::VecScalar((0..n_size).map(|i |{
        tau_input.clone().pow(&[i as u64])
    }).collect());

    let ss = ss_g.clone() * ss_index.clone();
    let s = s_temp.clone() * tau.clone();

    let z_val: Value<ArkBls12_381> = Value::Vec((0..n_size).map(|i| {
        z.clone() ^ Value::Index(i)
    }).collect());
    
    let y: Value<ArkBls12_381> = p.clone().dot(z_val.clone());
    // let y =  Value::<ArBls12_381>::random(&mut rng, &ATyp::scalar());
    let h_val: Value<ArkBls12_381> = Value::G2(h_input.clone() * tau_input.clone());

    let mut inputs = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
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