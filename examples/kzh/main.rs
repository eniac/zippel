use ark_ec::PrimeGroup;
use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

use crate::common;

type F = <ArkBls12_381 as ArkConfig>::F;
type G1 = <ArkBls12_381 as ArkConfig>::G1;
type G2 = <ArkBls12_381 as ArkConfig>::G2;

const NX: usize = 1;
const NY: usize = 1;

fn build_sizes_ctx() -> Ctx<Tid, usize> {
    let mut ctx = Ctx::new();
    ctx.insert(&Tid::new("NX"), &NX);
    ctx.insert(&Tid::new("NY"), &NY);
    ctx
}

pub fn run(opts: &common::RunOptions) {
    println!("=== KZH-2 (ArkBls12_381, NX={}, NY={}) ===", NX, NY);
    let args = ZippelArgs::new(PathBuf::from("examples/kzh/kzh.zippel"));
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    handler.compile(&build_sizes_ctx());

    common::run_prover_and_verify(&mut handler, prover_create_inputs());

    if !opts.analyses {
        return;
    }
    println!("\n--- Static Analysis ---");
    common::time_analysis!("Completeness", handler.analyze_completeness());
    common::time_analysis!("ZK", handler.analyze_knowledge());
}

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

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let (nxv, nyv) = (1usize << NX, 1usize << NY);

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
    let x0: Vec<F> = (0..NX).map(|_| F::rand(&mut rng)).collect();
    let y0: Vec<F> = (0..NY).map(|_| F::rand(&mut rng)).collect();
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
