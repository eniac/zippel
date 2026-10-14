use backend::{ATyp, ArkSecp256k1, Value};
use lang::id::Vid;
use share::Ctx;

use crate::common;
use crate::common::size;

fn prover_create_inputs(sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkSecp256k1>> {
    let mut rng = rand::rngs::OsRng;
    let n_val_const = 1usize << size(sizes, "S");

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

pub fn spec() -> common::ExampleSpec<ArkSecp256k1> {
    common::ExampleSpec {
        source: "examples/bccgp/bccgp.zippel",
        defaults: &[("S", 2)],
        validate: Some(|sizes, _analysis| {
            common::check_power_of_two(sizes, "S")?;
            Ok(())
        }),
        make_inputs: prover_create_inputs,
        analyses: &[common::Analysis::Completeness, common::Analysis::Zk],
    }
}
