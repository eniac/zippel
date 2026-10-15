use backend::{ATyp, ArkSecp256k1, Value};
use lang::id::Vid;
use share::Ctx;

use crate::common;
use crate::common::size;

#[allow(non_snake_case)]
fn make_inputs(sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkSecp256k1>> {
    let mut rng = rand::rngs::OsRng;
    let n_val_const = 1usize << size(sizes, "S");

    let u_aux_base: Value<ArkSecp256k1> = Value::<ArkSecp256k1>::random(&mut rng, &ATyp::g1());

    let g_vec: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n_val_const));
    let h_vec: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n_val_const));

    let G_factors: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let H_factors: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec_scalar(n_val_const));

    let a_vec_witness: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let b_vec_witness: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let ip_val_claimed: Value<ArkSecp256k1> = a_vec_witness.clone().dot(b_vec_witness.clone());

    let g_weighted = g_vec.clone() * G_factors.clone();
    let h_weighted = h_vec.clone() * H_factors.clone();
    let p_initial_commitment: Value<ArkSecp256k1> =
        g_weighted.dot(a_vec_witness.clone()) + h_weighted.dot(b_vec_witness.clone());
    let sum_vec: Value<ArkSecp256k1> =
        Value::<ArkSecp256k1>::random(&mut rng, &ATyp::vec_scalar(n_val_const));

    Ctx::<Vid, Value<ArkSecp256k1>>::from_iter([
        (Vid("g_vec".to_string()), g_vec),
        (Vid("h_vec".to_string()), h_vec),
        (Vid("g_factors".to_string()), G_factors),
        (Vid("h_factors".to_string()), H_factors),
        (
            Vid("p_initial_commitment".to_string()),
            p_initial_commitment,
        ),
        (Vid("ip_val_claimed".to_string()), ip_val_claimed),
        (Vid("u_aux_base".to_string()), u_aux_base),
        (Vid("a_vec_witness".to_string()), a_vec_witness),
        (Vid("b_vec_witness".to_string()), b_vec_witness),
        (Vid("sum_vec".to_string()), sum_vec),
    ])
}

pub fn spec() -> common::ExampleSpec<ArkSecp256k1> {
    common::ExampleSpec {
        source: "examples/ipa_weighted/ipa_weighted.zippel",
        defaults: &[("S", 2)],
        validate: Some(|sizes, _analysis| {
            common::check_power_of_two(sizes, "S")?;
            Ok(())
        }),
        make_inputs,
        analyses: &[common::Analysis::Completeness, common::Analysis::Zk],
    }
}
