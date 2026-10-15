use ark_std::UniformRand;
use backend::{ATyp, ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;

use crate::common;
use crate::common::size;

fn make_inputs(sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let n_val_const = 1usize << size(sizes, "S");

    let x_vec = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let a_vec = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n_val_const));
    let y = x_vec.clone().dot(a_vec.clone());

    let r_xi = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let r_tau = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);

    let g_vec = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n_val_const));
    let g_base = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let h_base = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);

    let tau_val = match y.clone() {
        Value::Scalar(y_scalar) => g_base * y_scalar + h_base * r_tau,
        _ => unreachable!(),
    };

    let gx_dot = g_vec.clone().dot(x_vec.clone());
    let xi_val = match gx_dot {
        Value::G1(gx_sum) => h_base * r_xi + *gx_sum,
        _ => unreachable!(),
    };

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("xi".to_string()), Value::g1(xi_val)),
        (Vid("tau".to_string()), Value::g1(tau_val)),
        (Vid("a_vec".to_string()), a_vec),
        (Vid("g_vec".to_string()), g_vec),
        (Vid("g_base".to_string()), Value::g1(g_base)),
        (Vid("h_base".to_string()), Value::g1(h_base)),
        (Vid("x_vec".to_string()), x_vec),
        (Vid("y".to_string()), y),
        (Vid("r_xi".to_string()), Value::Scalar(r_xi)),
        (Vid("r_tau".to_string()), Value::Scalar(r_tau)),
    ])
}

pub fn spec() -> common::ExampleSpec<ArkBls12_381> {
    common::ExampleSpec {
        source: "examples/hyrax_ipa/hyrax_ipa.zippel",
        defaults: &[("S", 2)],
        validate: Some(|sizes, _analysis| {
            common::check_power_of_two(sizes, "S")?;
            Ok(())
        }),
        make_inputs,
        analyses: &[common::Analysis::Completeness, common::Analysis::Zk],
    }
}
