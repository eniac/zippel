use zippel::*;
use std::path::PathBuf;
use backend::{ArkBls12_381, Value, ATyp};
use lang::id::Vid;
use share::Ctx;

fn main() {
    let args = ZippelArgs::new(PathBuf::from("ipa.zippel"))
        .with_pdf(PathBuf::from("ipa.pdf"));
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
    let n_val_const = 2;

    let u_aux_base: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::g1());

    let g_vec: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n_val_const));
    let h_vec: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n_val_const));

    let a_vec_witness: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let b_vec_witness: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let ip_val_claimed: Value<ArkBls12_381> = a_vec_witness.clone().dot(b_vec_witness.clone());
    let p_initial_commitment: Value<ArkBls12_381> = g_vec.clone().dot(a_vec_witness.clone()) +
    h_vec.clone().dot(b_vec_witness.clone());
    let sum_vec: Value<ArkBls12_381> = 
        Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_val_const));

    let mut inputs = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("g_vec".to_string()), g_vec),
        (Vid("h_vec".to_string()), h_vec),
        (Vid("P_initial_commitment".to_string()), p_initial_commitment),
        (Vid("ip_val_claimed".to_string()), ip_val_claimed),
        (Vid("u_aux_base".to_string()), u_aux_base),
        (Vid("a_vec_witness".to_string()), a_vec_witness),
        (Vid("b_vec_witness".to_string()), b_vec_witness),
        (Vid("sum_vec".to_string()), sum_vec),
    ]);

    return inputs;
}