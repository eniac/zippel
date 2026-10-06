use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ff::Zero;
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
type P = <ArkBls12_381 as ArkConfig>::P;
type GT = PairingOutput<P>;

/// nu = sigma = K: a 2^K × 2^K coefficient matrix.
const K: usize = 1;

pub fn run(opts: &common::RunOptions) {
    println!("=== Dory PCS (ArkBls12_381, K={K}) ===");
    let args = ZippelArgs::new(PathBuf::from("examples/dory_pcs/dory_pcs.zippel"));
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("K"), &K);
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

fn multi_pair(g1: &[G1], g2: &[G2]) -> GT {
    P::multi_pairing(g1.iter().copied(), g2.iter().copied())
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    let mut rng = rand::rngs::OsRng;
    let nv = 1usize << K;

    // Transparent setup: random Γ1, Γ2, H1, H2, and the verifier's pairings.
    let g1_vec: Vec<G1> = (0..nv).map(|_| G1::rand(&mut rng)).collect();
    let g2_vec: Vec<G2> = (0..nv).map(|_| G2::rand(&mut rng)).collect();
    let h1 = G1::rand(&mut rng);
    let h2 = G2::rand(&mut rng);
    let ht = P::pairing(h1, h2);
    let mut chi = vec![P::pairing(g1_vec[0], g2_vec[0])];
    let (mut delta_1r, mut delta_2r) = (vec![GT::zero()], vec![GT::zero()]);
    for k in 1..=K {
        let (half, full) = (1 << (k - 1), 1 << k);
        delta_1r.push(multi_pair(&g1_vec[half..full], &g2_vec[..half]));
        delta_2r.push(multi_pair(&g1_vec[..half], &g2_vec[half..full]));
        chi.push(chi[k - 1] + multi_pair(&g1_vec[half..full], &g2_vec[half..full]));
    }
    let delta_1l: Vec<GT> = std::iter::once(GT::zero())
        .chain(chi[..K].iter().copied())
        .collect();

    let m: Vec<F> = (0..nv * nv).map(|_| F::rand(&mut rng)).collect();
    let col_pt: Vec<F> = (0..K).map(|_| F::rand(&mut rng)).collect();
    let row_pt: Vec<F> = (0..K).map(|_| F::rand(&mut rng)).collect();
    let (eqr, eqc) = (eq_weights(&row_pt), eq_weights(&col_pt));
    let y: F = (0..nv * nv).map(|i| eqr[i / nv] * eqc[i % nv] * m[i]).sum();

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter(
        [
            ("m", Value::VecScalar(m)),
            ("col_pt", Value::VecScalar(col_pt)),
            ("row_pt", Value::VecScalar(row_pt)),
            ("y", Value::Scalar(y)),
            ("g1_0", Value::G1(g1_vec[0])),
            ("g2_0", Value::G2(g2_vec[0])),
            ("g1_vec", Value::VecG1(g1_vec)),
            ("g2_vec", Value::VecG2(g2_vec)),
            ("h1", Value::G1(h1)),
            ("h2", Value::G2(h2)),
            ("ht", Value::GT(ht)),
            ("chi", Value::VecGT(chi)),
            ("delta_1l", Value::VecGT(delta_1l)),
            ("delta_1r", Value::VecGT(delta_1r)),
            ("delta_2r", Value::VecGT(delta_2r)),
        ]
        .into_iter()
        .map(|(k, v)| (Vid(k.to_string()), v)),
    )
}
