use ark_ff::Field;
use ark_std::UniformRand;
use backend::{ArkBls12_381, Backend, Value};
use lang::id::Vid;
use share::Ctx;

use crate::common;

/// The number of simulated instances; the relation assumes one.
const K: usize = 1;

fn make_inputs(sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as Backend>::F;
    type G1 = <ArkBls12_381 as Backend>::G1;
    let n = common::size(sizes, "N");
    let mut rng = rand::rngs::OsRng;

    let g = G1::rand(&mut rng);

    let mut w_vec = Vec::with_capacity(n);
    let mut r_vec = Vec::with_capacity(n);
    let mut b_vec = Vec::with_capacity(n);
    let mut c_sim_vec = Vec::with_capacity(n);
    let mut m2_sim_vec = Vec::with_capacity(n);
    let mut pk_vec = Vec::with_capacity(n);

    let mut u_points_vec = Vec::new();
    let mut u_evals_vec = Vec::new();
    let mut eval_points_vec = Vec::with_capacity(n);

    for i in 0..n {
        let is_known = i < (n - K);
        eval_points_vec.push(F::from((i + 1) as u64));

        let w_val = F::rand(&mut rng);
        w_vec.push(w_val);

        let pk_affines = backend::Group::batch_mul(&g, &[w_val]);
        let pk = pk_affines.into_iter().next().unwrap();
        pk_vec.push(pk);

        let r_val = F::rand(&mut rng);
        r_vec.push(r_val);

        let c_sim_val = F::rand(&mut rng);
        c_sim_vec.push(c_sim_val);

        let m2_sim_val = F::rand(&mut rng);
        m2_sim_vec.push(m2_sim_val);

        if is_known {
            b_vec.push(F::from(1u64));
        } else {
            b_vec.push(F::from(0u64));
            u_points_vec.push(F::from((i + 1) as u64));
            u_evals_vec.push(c_sim_val);
        }
    }

    // The relation's product: every point, times its difference from every
    // other point.
    let distinct_product: F = (0..n)
        .map(|i| {
            let differences: F = (1..n)
                .map(|d| eval_points_vec[i] - eval_points_vec[(i + d) % n])
                .product();
            eval_points_vec[i] * differences
        })
        .product();
    let distinct_inv = distinct_product
        .inverse()
        .expect("the points 1..=N are distinct and nonzero");

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("g".to_string()), Value::g1(g)),
        (Vid("keys".to_string()), Value::vec_g1_affine(pk_vec)),
        (
            Vid("eval_points".to_string()),
            Value::vec_scalar(eval_points_vec),
        ),
        (Vid("w".to_string()), Value::vec_scalar(w_vec)),
        (Vid("r".to_string()), Value::vec_scalar(r_vec)),
        (Vid("b".to_string()), Value::vec_scalar(b_vec)),
        (Vid("c_sim".to_string()), Value::vec_scalar(c_sim_vec)),
        (Vid("m2_sim".to_string()), Value::vec_scalar(m2_sim_vec)),
        (Vid("u_points".to_string()), Value::vec_scalar(u_points_vec)),
        (Vid("u_evals".to_string()), Value::vec_scalar(u_evals_vec)),
        (Vid("distinct_inv".to_string()), Value::Scalar(distinct_inv)),
    ])
}

pub fn spec() -> common::ExampleSpec<ArkBls12_381> {
    common::ExampleSpec {
        source: "examples/cds/cds.zippel",
        defaults: &[("N", 2)],
        validate: Some(|sizes, _analysis| {
            if common::size(sizes, "N") <= K {
                return Err(format!("N must exceed K = {K}: some instance must be real"));
            }
            Ok(())
        }),
        make_inputs,
        analyses: &[common::Analysis::Completeness, common::Analysis::Zk],
    }
}
