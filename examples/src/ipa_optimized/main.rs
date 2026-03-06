use zippel::*;
use std::{path::PathBuf, time::Instant};
use backend::{ArkSecp256k1, Value, ATyp};
use lang::id::Vid;
use share::Ctx;

fn main() {
    let args = ZippelArgs::new(PathBuf::from("ipa_optimized.zippel"))
        .with_pdf(PathBuf::from("ipa_optimized.pdf"));
    let mut handler: zippel::ZippelHandler<ArkSecp256k1> = ZippelHandler::new(args);
    handler.compile();

    let inputs = prover_create_inputs();
    let prover_scheduled = handler.default_schedule_prover();
    let prover_start = Instant::now();
    let proof = handler.run_prover(prover_scheduled, inputs);
    let prover_elapsed = prover_start.elapsed();
    println!("Prover runtime: {:?}", prover_elapsed);


    let verifier_scheduled = handler.default_schedule_verifier();
    let verifier_start = Instant::now();
    let verifier_result = handler.run_verifier(verifier_scheduled, proof);
    let verifier_elapsed = verifier_start.elapsed();
    println!("Verifier runtime: {:?}", verifier_elapsed);
    println!("Verifier result: {:?}", verifier_result);


    // handler.analyze_completeness();
    // handler.analyze_knowledge();
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkSecp256k1>> {
    let mut rng = rand::rngs::OsRng;
    let n_val_const = 32;

    let u_aux_base: Value<ArkSecp256k1> = Value::<ArkSecp256k1>::random(&mut rng, &ATyp::g1());

    let g_vec: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n_val_const));
    let h_vec: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n_val_const));

    // Generator weighting factors (analogous to G_factors, H_factors in the Rust code)
    let G_factors: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let H_factors: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec_scalar(n_val_const));

    let a_vec_witness: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let b_vec_witness: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let ip_val_claimed: Value<ArkSecp256k1> =
        a_vec_witness.clone().dot(b_vec_witness.clone());

    // Compute P_initial_commitment using weighted bases:
    //   G'_i = G_i * G_factors_i,  H'_i = H_i * H_factors_i
    // so P = <G', a> + <H', b>.
    let g_weighted = g_vec.clone() * G_factors.clone();
    let h_weighted = h_vec.clone() * H_factors.clone();
    let p_initial_commitment: Value<ArkSecp256k1> =
        g_weighted.dot(a_vec_witness.clone())
        + h_weighted.dot(b_vec_witness.clone());
    let sum_vec: Value<ArkSecp256k1> = 
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec_scalar(n_val_const));

    let inputs = Ctx::<Vid, Value<ArkSecp256k1>>::from_iter([
        (Vid("g_vec".to_string()), g_vec),
        (Vid("h_vec".to_string()), h_vec),
        (Vid("G_factors".to_string()), G_factors),
        (Vid("H_factors".to_string()), H_factors),
        (Vid("P_initial_commitment".to_string()), p_initial_commitment),
        (Vid("ip_val_claimed".to_string()), ip_val_claimed),
        (Vid("u_aux_base".to_string()), u_aux_base),
        (Vid("a_vec_witness".to_string()), a_vec_witness),
        (Vid("b_vec_witness".to_string()), b_vec_witness),
        (Vid("sum_vec".to_string()), sum_vec),
    ]);

    return inputs;
}
