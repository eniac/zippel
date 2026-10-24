use ark_ff::fields::Field;
use ark_std::UniformRand;
use backend::{ATyp, ArkBls12_381, Backend, Value};
use lang::id::Vid;
use share::Ctx;

use crate::common;
use crate::common::size;

fn make_inputs(sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkBls12_381>> {
    let n_size = size(sizes, "N");

    let mut rng = rand::rngs::OsRng;

    let g_input = <ArkBls12_381 as Backend>::G1::rand(&mut rng);
    let g = Value::g1(g_input);

    let h_input = <ArkBls12_381 as Backend>::G2::rand(&mut rng);
    let h = Value::g2(h_input);

    let tau_input = <ArkBls12_381 as Backend>::F::rand(&mut rng);
    let xi_input = <ArkBls12_381 as Backend>::F::rand(&mut rng);

    let mut srs_g1_vec = vec![];
    for i in 0..n_size {
        srs_g1_vec.push(g_input * tau_input.pow([i as u64]));
    }
    srs_g1_vec.push(g_input * xi_input);
    let srs_g1 = Value::vec_g1(srs_g1_vec);

    let tau_g2 = h_input * tau_input;
    let xi_g2 = h_input * xi_input;
    let srs_g2 = Value::vec_g2(vec![tau_g2, xi_g2]);

    let p_poly_val = Value::<ArkBls12_381>::random(&mut rng, &ATyp::uni(n_size - 1));

    let u_input = <ArkBls12_381 as Backend>::F::rand(&mut rng);
    let u_val = Value::Scalar(u_input);

    let v_val = p_poly_val.clone().value_eval(u_val.clone());

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("p_poly".to_string()), p_poly_val),
        (Vid("u".to_string()), u_val),
        (Vid("v".to_string()), v_val),
        (Vid("srs_g1".to_string()), srs_g1),
        (Vid("tau_g1".to_string()), Value::g1(g_input * tau_input)),
        (Vid("srs_g2".to_string()), srs_g2),
        (Vid("gen_g1".to_string()), g),
        (Vid("gen_g2".to_string()), h),
    ])
}

pub fn spec() -> common::ExampleSpec<ArkBls12_381> {
    common::ExampleSpec {
        source: "examples/zeromorph_kzg/zeromorph_kzg.zippel",
        defaults: &[("N", 2)],
        validate: None,
        make_inputs,
        analyses: &[common::Analysis::Completeness, common::Analysis::Zk],
    }
}
