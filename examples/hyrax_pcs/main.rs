use ark_std::One;
use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;

use crate::common;
use crate::common::size;

type F = <ArkBls12_381 as ArkConfig>::F;
type G1 = <ArkBls12_381 as ArkConfig>::G1;

fn make_inputs(sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkBls12_381>> {
    let l = size(sizes, "L");
    let m = size(sizes, "M");
    let nrows = 1 << l;
    let ncols = 1 << m;
    let ntot = nrows * ncols;

    let mut rng = rand::rngs::OsRng;
    let one = F::one();

    let p: Vec<F> = (0..ntot).map(|_| F::rand(&mut rng)).collect();
    let z_row: Vec<F> = (0..l).map(|_| F::rand(&mut rng)).collect();
    let z_col: Vec<F> = (0..m).map(|_| F::rand(&mut rng)).collect();

    let l_vec = eq_evals(&z_row, one);
    let r_vec = eq_evals(&z_col, one);
    let y: F = (0..nrows)
        .flat_map(|i| (0..ncols).map(move |j| (i, j)))
        .map(|(i, j)| l_vec[i] * r_vec[j] * p[i * ncols + j])
        .sum();

    let g_vec: Vec<G1> = (0..ncols).map(|_| G1::rand(&mut rng)).collect();
    let g_base = G1::rand(&mut rng);
    let h_base = G1::rand(&mut rng);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("p".to_string()), Value::vec_scalar(p)),
        (Vid("z_row".to_string()), Value::vec_scalar(z_row)),
        (Vid("z_col".to_string()), Value::vec_scalar(z_col)),
        (Vid("y".to_string()), Value::Scalar(y)),
        (Vid("g_vec".to_string()), Value::vec_g1(g_vec)),
        (Vid("g_base".to_string()), Value::g1(g_base)),
        (Vid("h_base".to_string()), Value::g1(h_base)),
    ])
}

fn eq_evals(x: &[F], one: F) -> Vec<F> {
    let n = x.len();
    let mut out = vec![one; 1 << n];
    let mut size = 1;
    for &xi in x {
        let one_m_xi = one - xi;
        for i in (0..size).rev() {
            let v = out[i];
            out[size + i] = v * xi;
            out[i] = v * one_m_xi;
        }
        size *= 2;
    }
    out
}

pub fn spec() -> common::ExampleSpec<ArkBls12_381> {
    common::ExampleSpec {
        source: "examples/hyrax_pcs/hyrax_pcs.zippel",
        run_defaults: &[("L", 7), ("M", 8)],
        analysis_defaults: &[("L", 2), ("M", 2)],
        validate: Some(|sizes, _analysis| {
            common::check_power_of_two(sizes, "L")?;
            common::check_power_of_two(sizes, "M")?;
            common::check_power_of_two_sum(sizes, "L", "M")?;
            Ok(())
        }),
        make_inputs,
        analyses: &[common::Analysis::Completeness],
    }
}
