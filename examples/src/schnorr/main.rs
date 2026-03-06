use zippel::*;
use std::path::PathBuf;
use backend::{ArkBls12_381, ArkConfig, ArkGroupOps, Value};
use lang::id::Vid;
use share::Ctx;
use ark_std::UniformRand;

fn main() {
    let args = ZippelArgs::new(PathBuf::from("schnorr.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile();

    let inputs = prover_create_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    let proof = handler.run_prover(prover_scheduled, inputs);


    let verifier_scheduled = handler.default_schedule_verifier();
    let verifier_result = handler.run_verifier(verifier_scheduled, proof);
    println!("Verifier result: {:?}", verifier_result);


    handler.analyze_completeness();
    handler.analyze_knowledge();
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let x = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let g = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let h_affines = <ArkBls12_381 as ArkConfig>::G1Ops::vec_mul(&g, &vec![x]);
    let h = h_affines.into_iter().next().unwrap();
    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("x".to_string()), Value::Scalar(x)),
        (Vid("g".to_string()), Value::G1(g)),
        (Vid("h".to_string()), Value::G1Affine(h)),
    ])
}

