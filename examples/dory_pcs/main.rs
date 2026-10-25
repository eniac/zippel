use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ff::Zero;
use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;

use crate::common;
use crate::common::size;

type F = <ArkBls12_381 as ArkConfig>::F;
type G1 = <ArkBls12_381 as ArkConfig>::G1;
type G2 = <ArkBls12_381 as ArkConfig>::G2;
type P = <ArkBls12_381 as ArkConfig>::P;
type GT = PairingOutput<P>;

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

fn make_inputs(sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkBls12_381>> {
    let k = size(sizes, "K");

    let mut rng = rand::rngs::OsRng;
    let nv = 1usize << k;

    // Transparent setup: random Γ1, Γ2, H1, H2, and the verifier's pairings.
    let g1_vec: Vec<G1> = (0..nv).map(|_| G1::rand(&mut rng)).collect();
    let g2_vec: Vec<G2> = (0..nv).map(|_| G2::rand(&mut rng)).collect();
    let h1 = G1::rand(&mut rng);
    let h2 = G2::rand(&mut rng);
    let ht = P::pairing(h1, h2);
    let mut chi = vec![P::pairing(g1_vec[0], g2_vec[0])];
    let (mut delta_1r, mut delta_2r) = (vec![GT::zero()], vec![GT::zero()]);
    for k in 1..=k {
        let (half, full) = (1 << (k - 1), 1 << k);
        delta_1r.push(multi_pair(&g1_vec[half..full], &g2_vec[..half]));
        delta_2r.push(multi_pair(&g1_vec[..half], &g2_vec[half..full]));
        chi.push(chi[k - 1] + multi_pair(&g1_vec[half..full], &g2_vec[half..full]));
    }
    let delta_1l: Vec<GT> = std::iter::once(GT::zero())
        .chain(chi[..k].iter().copied())
        .collect();

    let m: Vec<F> = (0..nv * nv).map(|_| F::rand(&mut rng)).collect();
    let col_pt: Vec<F> = (0..k).map(|_| F::rand(&mut rng)).collect();
    let row_pt: Vec<F> = (0..k).map(|_| F::rand(&mut rng)).collect();
    let (eqr, eqc) = (eq_weights(&row_pt), eq_weights(&col_pt));
    let y: F = (0..nv * nv).map(|i| eqr[i / nv] * eqc[i % nv] * m[i]).sum();

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter(
        [
            ("m", Value::vec_scalar(m)),
            ("col_pt", Value::vec_scalar(col_pt)),
            ("row_pt", Value::vec_scalar(row_pt)),
            ("y", Value::Scalar(y)),
            ("g1_0", Value::g1(g1_vec[0])),
            ("g2_0", Value::g2(g2_vec[0])),
            ("g1_vec", Value::vec_g1(g1_vec)),
            ("g2_vec", Value::vec_g2(g2_vec)),
            ("h1", Value::g1(h1)),
            ("h2", Value::g2(h2)),
            ("ht", Value::gt(ht)),
            ("chi", Value::vec_gt(chi)),
            ("delta_1l", Value::vec_gt(delta_1l)),
            ("delta_1r", Value::vec_gt(delta_1r)),
            ("delta_2r", Value::vec_gt(delta_2r)),
        ]
        .into_iter()
        .map(|(k, v)| (Vid(k.to_string()), v)),
    )
}

pub fn spec() -> common::ExampleSpec<ArkBls12_381> {
    common::ExampleSpec {
        source: "examples/dory_pcs/dory_pcs.zippel",
        run_defaults: &[("K", 6)],
        analysis_defaults: &[("K", 3)],
        validate: Some(|sizes, _analysis| {
            common::check_power_of_two(sizes, "K")?;
            Ok(())
        }),
        make_inputs,
        analyses: &[common::Analysis::Completeness],
    }
}
