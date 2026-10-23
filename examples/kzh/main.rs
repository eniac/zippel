use ark_ec::PrimeGroup;
use ark_std::UniformRand;
use backend::{ArkBls12_381, Backend, Value};
use lang::id::Vid;
use share::Ctx;

use crate::common;
use crate::common::size;

type F = <ArkBls12_381 as Backend>::F;
type G1 = <ArkBls12_381 as Backend>::G1;
type G2 = <ArkBls12_381 as Backend>::G2;

/// eq(x, r) over x ∈ {0,1}^n with r[0] the low bit (irondict's `build_eq_x_r`).
fn eq_weights(r: &[F]) -> Vec<F> {
    let mut w = vec![F::from(1u64)];
    for &ri in r {
        w = w
            .iter()
            .map(|&v| v * (F::from(1u64) - ri))
            .chain(w.iter().map(|&v| v * ri))
            .collect();
    }
    w
}

fn make_inputs(sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkBls12_381>> {
    let nx = size(sizes, "NX");
    let ny = size(sizes, "NY");

    let mut rng = rand::rngs::OsRng;
    let (nxv, nyv) = (1usize << nx, 1usize << ny);

    // KZH-k setup (Figure 12) at k = 2.
    let g = G1::generator();
    let v = G2::generator();
    let mu1: Vec<F> = (0..nxv).map(|_| F::rand(&mut rng)).collect();
    let mu2: Vec<F> = (0..nyv).map(|_| F::rand(&mut rng)).collect();
    let h1: Vec<G1> = (0..nxv * nyv)
        .map(|k| g * (mu1[k / nyv] * mu2[k % nyv]))
        .collect();
    let h2: Vec<G1> = mu2.iter().map(|m| g * m).collect();
    let v1: Vec<G2> = mu1.iter().map(|m| v * m).collect();

    let f: Vec<F> = (0..nxv * nyv).map(|_| F::rand(&mut rng)).collect();
    let x0: Vec<F> = (0..nx).map(|_| F::rand(&mut rng)).collect();
    let y0: Vec<F> = (0..ny).map(|_| F::rand(&mut rng)).collect();
    let (eqx, eqy) = (eq_weights(&x0), eq_weights(&y0));
    let z0: F = (0..nxv * nyv)
        .map(|k| eqx[k / nyv] * eqy[k % nyv] * f[k])
        .sum();

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter(
        [
            ("f", Value::vec_scalar(f)),
            ("x0", Value::vec_scalar(x0)),
            ("y0", Value::vec_scalar(y0)),
            ("z0", Value::Scalar(z0)),
            ("h1", Value::vec_g1(h1)),
            ("h2", Value::vec_g1(h2)),
            ("v1", Value::vec_g2(v1)),
            ("v_gen", Value::g2(v)),
            ("g_gen", Value::g1(g)),
        ]
        .into_iter()
        .map(|(k, val)| (Vid(k.to_string()), val)),
    )
}

pub fn spec() -> common::ExampleSpec<ArkBls12_381> {
    common::ExampleSpec {
        source: "examples/kzh/kzh.zippel",
        defaults: &[("NX", 2), ("NY", 2)],
        validate: Some(|sizes, _analysis| {
            common::check_power_of_two(sizes, "NX")?;
            common::check_power_of_two(sizes, "NY")?;
            common::check_power_of_two_sum(sizes, "NX", "NY")?;
            Ok(())
        }),
        make_inputs,
        analyses: &[common::Analysis::Completeness, common::Analysis::Zk],
    }
}
