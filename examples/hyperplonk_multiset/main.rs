// MultiSet Check PIOP example driver.

use ark_ff::{Field, Zero};
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use rand::Rng;
use rand::seq::SliceRandom;
use share::Ctx;

use crate::common;
use crate::common::size;

// The input dimensions follow the resolved S size.

struct MultiSetInstance<F> {
    f: Vec<F>,
    g: Vec<F>,
    r: F,
    v_evs: Vec<F>,
    g_shift_inv: Vec<F>,
}

/// Build the rational product tree ṽ from per-point ratios `leaves`.
/// Same dense LSB-first layout as in `examples/hyperplonk_productcheck`.
fn build_v_tree<F: Field + Zero>(leaves: &[F]) -> Vec<F> {
    let n = leaves.len();
    assert!(n.is_power_of_two());
    let mut v = vec![F::zero(); 2 * n];
    for k in 0..n {
        v[2 * k] = leaves[k];
    }
    v[2 * n - 1] = F::zero();
    let mut done = vec![false; n];
    done[n - 1] = true;
    let mut changed = true;
    while changed {
        changed = false;
        for y in 0..n {
            if done[y] {
                continue;
            }
            let v_y_ready = y.is_multiple_of(2) || done[(y - 1) / 2];
            let v_yn_ready = (y + n).is_multiple_of(2) || done[(y + n - 1) / 2];
            if v_y_ready && v_yn_ready {
                v[1 + 2 * y] = v[y] * v[y + n];
                done[y] = true;
                changed = true;
            }
        }
    }
    v
}

/// Build a random satisfying `MultiSet` instance.
fn random_multiset<F, R>(rng: &mut R, num_points: usize) -> MultiSetInstance<F>
where
    F: Field + Zero,
    R: Rng + ?Sized,
{
    let f: Vec<F> = (0..num_points).map(|_| F::rand(rng)).collect();
    let mut g = f.clone();
    g.shuffle(rng);

    // Simulate the verifier-side Fiat-Shamir draw of r.
    let r = F::rand(rng);

    // Leaves of ṽ: (r + f[i]) / (r + g[i]). When `g` is a permutation of `f`
    // (which we ensure by construction), r + g[i] is never zero w.h.p.
    let g_shift_inv: Vec<F> = g
        .iter()
        .map(|gi| (r + *gi).inverse().expect("r + g[i] nonzero"))
        .collect();
    let leaves: Vec<F> = f
        .iter()
        .zip(g_shift_inv.iter())
        .map(|(fi, gi_inv)| (r + *fi) * *gi_inv)
        .collect();
    let v_evs = build_v_tree(&leaves);

    MultiSetInstance {
        f,
        g,
        r,
        v_evs,
        g_shift_inv,
    }
}

fn make_inputs(sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as ArkConfig>::F;
    let s = size(sizes, "S");
    let num_points = 1 << s;

    let mut rng = rand::rngs::OsRng;

    let inst = random_multiset::<F, _>(&mut rng, num_points);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("f_evs".to_string()), Value::vec_scalar(inst.f)),
        (Vid("g_evs".to_string()), Value::vec_scalar(inst.g)),
        (Vid("r".to_string()), Value::Scalar(inst.r)),
        (Vid("v_evs".to_string()), Value::vec_scalar(inst.v_evs)),
        (
            Vid("g_shift_inv".to_string()),
            Value::vec_scalar(inst.g_shift_inv),
        ),
    ])
}

pub fn spec() -> common::ExampleSpec<ArkBls12_381> {
    common::ExampleSpec {
        source: "examples/hyperplonk_multiset/hyperplonk_multiset.zippel",
        run_defaults: &[("S", 17)],
        analysis_defaults: &[("S", 3)],
        validate: Some(|sizes, _analysis| {
            common::check_power_of_two(sizes, "S")?;
            Ok(())
        }),
        make_inputs,
        analyses: &[common::Analysis::Completeness],
    }
}
