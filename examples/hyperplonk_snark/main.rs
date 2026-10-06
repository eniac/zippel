use ark_ec::{CurveGroup, VariableBaseMSM};
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

/// Number of variables: 2^S gates.
const S: usize = 2;

pub fn run(opts: &common::RunOptions) {
    println!(
        "=== HyperPlonk SNARK (ArkBls12_381, S={S}, {} gates) ===",
        1 << S
    );
    let args = ZippelArgs::new(PathBuf::from(
        "examples/hyperplonk_snark/hyperplonk_snark.zippel",
    ));
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &S);
    handler.compile(&sizes);

    let inputs: Inputs<_> = prover_create_inputs().into();
    common::run_prover_and_verify(&mut handler, &inputs);

    if !opts.analyses {
        return;
    }
    println!("\n--- Static Analysis ---");
    common::time_analysis!("Completeness", handler.analyze_completeness());
    common::time_analysis!("ZK", handler.analyze_knowledge());
}

/// eq(x, r) over x ∈ {0,1}^n with r[0] the low bit.
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

fn msm(bases: &[G1], scalars: &[F]) -> G1 {
    G1::msm(&G1::normalize_batch(bases), scalars).unwrap()
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let n = 1usize << S;

    // Multilinear KZG setup: level i holds eq(t[i..], b)·g, the last is [g].
    let t: Vec<F> = (0..S).map(|_| F::rand(&mut rng)).collect();
    let g = G1::rand(&mut rng);
    let h = G2::rand(&mut rng);
    let ck: Vec<G1> = (0..=S)
        .flat_map(|i| eq_weights(&t[i..]).into_iter().map(move |e| g * e))
        .collect();
    let h_mask: Vec<G2> = t.iter().map(|&ti| h * ti).collect();

    // A random satisfying vanilla-Plonk circuit with identity wiring.
    let col = |_| (0..n).map(|_| F::rand(&mut rng)).collect::<Vec<F>>();
    let w: Vec<Vec<F>> = (0..3).map(col).collect();
    let mut q: Vec<Vec<F>> = (0..4)
        .map(|_| (0..n).map(|_| F::rand(&mut rng)).collect())
        .collect();
    q.push(
        (0..n)
            .map(|i| {
                -(q[0][i] * w[0][i]
                    + q[1][i] * w[1][i]
                    + q[2][i] * w[2][i]
                    + q[3][i] * w[0][i] * w[1][i])
            })
            .collect(),
    );
    let s: Vec<Vec<F>> = (0..3)
        .map(|l| (0..n).map(|i| F::from((l * n + i) as u64)).collect())
        .collect();

    let sel_comms: Vec<G1> = q.iter().map(|c| msm(&ck[..n], c)).collect();
    let perm_comms: Vec<G1> = s.iter().map(|c| msm(&ck[..n], c)).collect();

    let mut named = vec![
        ("sel_comms", Value::VecG1(sel_comms)),
        ("perm_comms", Value::VecG1(perm_comms)),
        ("pub_input", Value::VecScalar(w[0][..4].to_vec())),
        ("ck", Value::VecG1(ck)),
        ("g", Value::G1(g)),
        ("h", Value::G2(h)),
        ("h_mask", Value::VecG2(h_mask)),
    ];
    for (name, c) in ["w0", "w1", "w2"].into_iter().zip(w) {
        named.push((name, Value::VecScalar(c)));
    }
    for (name, c) in ["q0", "q1", "q2", "q3", "q4"].into_iter().zip(q) {
        named.push((name, Value::VecScalar(c)));
    }
    for (name, c) in ["s0", "s1", "s2"].into_iter().zip(s) {
        named.push((name, Value::VecScalar(c)));
    }
    Ctx::from_iter(named.into_iter().map(|(k, v)| (Vid(k.to_string()), v)))
}
