// Permutation PIOP example driver.

use ark_ff::{Field, Zero};
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use rand::Rng;
use rand::seq::SliceRandom;
use share::Ctx;

use crate::common;
use crate::common::size;

// The input dimensions follow the resolved S size.

struct PermutationInstance<F> {
    f: Vec<F>,
    g: Vec<F>,
    s_sigma: Vec<F>,
    s_id: Vec<F>,
    r2: F,
    r: F,
    v_evs: Vec<F>,
    g_shift_inv: Vec<F>,
}

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

fn random_permutation<F, R>(rng: &mut R, num_points: usize) -> PermutationInstance<F>
where
    F: Field + Zero,
    R: Rng + ?Sized,
{
    let f: Vec<F> = (0..num_points).map(|_| F::rand(rng)).collect();
    let mut sigma: Vec<usize> = (0..num_points).collect();
    sigma.shuffle(rng);
    let g: Vec<F> = sigma.iter().map(|&j| f[j]).collect();
    let s_sigma: Vec<F> = sigma.iter().map(|&j| F::from(j as u64)).collect();
    let s_id: Vec<F> = (0..num_points).map(|i| F::from(i as u64)).collect();

    // Simulate the verifier-side Fiat-Shamir draws of r2 and r.
    let r2 = F::rand(rng);
    let r = F::rand(rng);

    let f_hat: Vec<F> = (0..num_points).map(|i| s_id[i] + r2 * f[i]).collect();
    let g_hat: Vec<F> = (0..num_points).map(|i| s_sigma[i] + r2 * g[i]).collect();
    let g_shift_inv: Vec<F> = (0..num_points)
        .map(|i| (r + g_hat[i]).inverse().expect("r + g_hat[i] nonzero"))
        .collect();
    let leaves: Vec<F> = (0..num_points)
        .map(|i| (r + f_hat[i]) * g_shift_inv[i])
        .collect();
    let v_evs = build_v_tree(&leaves);

    PermutationInstance {
        f,
        g,
        s_sigma,
        s_id,
        r2,
        r,
        v_evs,
        g_shift_inv,
    }
}

fn prover_create_inputs(sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as ArkConfig>::F;
    let s = size(sizes, "S");
    let num_points = 1 << s;

    let mut rng = rand::rngs::OsRng;

    let inst = random_permutation::<F, _>(&mut rng, num_points);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("f_evs".to_string()), Value::vec_scalar(inst.f)),
        (Vid("g_evs".to_string()), Value::vec_scalar(inst.g)),
        (
            Vid("s_sigma_evs".to_string()),
            Value::vec_scalar(inst.s_sigma),
        ),
        (Vid("s_id_evs".to_string()), Value::vec_scalar(inst.s_id)),
        (Vid("r2".to_string()), Value::Scalar(inst.r2)),
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
        source: "examples/hyperplonk_permutation/hyperplonk_permutation.zippel",
        defaults: &[("S", 3)],
        validate: Some(|sizes, _analysis| {
            common::check_power_of_two(sizes, "S")?;
            Ok(())
        }),
        make_inputs: prover_create_inputs,
        analyses: &[common::Analysis::Completeness, common::Analysis::Zk],
    }
}
