use ark_std::UniformRand;
use backend::{ATyp, ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;

use crate::common;
use crate::common::size;

fn prover_create_inputs(sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let n = size(sizes, "S");

    let x_vec = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n));
    let a_vec = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(n));

    let y = x_vec.clone().dot(a_vec.clone());

    let r_xi = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);
    let r_tau = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);

    let g_vec = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec(&ATyp::g1(), n));
    let g = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let h = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);

    let tau_val = match y.clone() {
        Value::Scalar(y_scalar) => g * y_scalar + h * r_tau,
        _ => unreachable!(),
    };

    let g_dot_x = g_vec.clone().dot(x_vec.clone());
    let xi_val = match g_dot_x {
        Value::G1(gx_sum) => h * r_xi + *gx_sum,
        _ => unreachable!(),
    };

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("x_vec".to_string()), x_vec),
        (Vid("r_xi".to_string()), Value::Scalar(r_xi)),
        (Vid("y".to_string()), y),
        (Vid("r_tau".to_string()), Value::Scalar(r_tau)),
        (Vid("g_vec".to_string()), g_vec),
        (Vid("a_vec".to_string()), a_vec),
        (Vid("g".to_string()), Value::g1(g)),
        (Vid("h".to_string()), Value::g1(h)),
        (Vid("xi".to_string()), Value::g1(xi_val)),
        (Vid("tau".to_string()), Value::g1(tau_val)),
    ])
}

pub fn spec() -> common::ExampleSpec<ArkBls12_381> {
    common::ExampleSpec {
        source: "examples/hyrax_podp/hyrax_podp.zippel",
        defaults: &[("S", 4)],
        validate: None,
        make_inputs: prover_create_inputs,
        analyses: &[common::Analysis::Completeness, common::Analysis::Zk],
    }
}
