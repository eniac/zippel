use ark_std::UniformRand;
use backend::{ArkBls12_381, Backend, Value};
use lang::id::Vid;
use share::Ctx;

use crate::common;
use crate::common::size;

fn make_inputs(sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as Backend>::F;
    type G1 = <ArkBls12_381 as Backend>::G1;
    let mut rng = rand::rngs::OsRng;

    let (n_instance, n_witness, n_rows) = (
        size(sizes, "n"),
        size(sizes, "N") - size(sizes, "n"),
        size(sizes, "m"),
    );
    let x: Vec<F> = (0..n_instance).map(|_| F::rand(&mut rng)).collect();
    let mut w: Vec<F> = (0..n_witness).map(|_| F::rand(&mut rng)).collect();
    w[0] = x[0] * x[0];
    let width = n_instance + n_witness;
    let mut mat_a = vec![F::from(0u64); width * n_rows];
    let mut mat_b = mat_a.clone();
    let mut mat_c = mat_a.clone();
    for row in 0..n_rows {
        mat_a[row * width] = F::from(1u64);
        mat_b[row * width] = F::from(1u64);
        mat_c[row * width + n_instance] = F::from(1u64);
    }
    let ck = (0..n_rows).map(|_| G1::rand(&mut rng)).collect();
    let h_base = G1::rand(&mut rng);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("ck".to_string()), Value::vec_g1(ck)),
        (Vid("h_base".to_string()), Value::g1(h_base)),
        (Vid("mat_A".to_string()), Value::vec_scalar(mat_a)),
        (Vid("mat_B".to_string()), Value::vec_scalar(mat_b)),
        (Vid("mat_C".to_string()), Value::vec_scalar(mat_c)),
        (Vid("x".to_string()), Value::vec_scalar(x)),
        (Vid("w".to_string()), Value::vec_scalar(w)),
    ])
}

pub fn spec() -> common::ExampleSpec<ArkBls12_381> {
    common::ExampleSpec {
        source: "examples/r1cs_sigma/r1cs_sigma.zippel",
        defaults: &[("N", 2), ("n", 1), ("m", 1)],
        validate: None,
        make_inputs,
        analyses: &[
            common::Analysis::Completeness,
            common::Analysis::Zk,
            common::Analysis::Soundness(&[2]),
        ],
    }
}
