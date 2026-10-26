// ProductCheck PIOP example driver.
//
// Builds a random satisfying instance with num_leaves = 2^s hypercube points
// for f and runs the parametric ProductCheck protocol from
// hyperplonk_productcheck.zippel on it.

use ark_ff::{Field, Zero};
use backend::{ArkBls12_381, Backend, Value};
use lang::id::Vid;
use rand::Rng;
use share::Ctx;

use crate::common;
use crate::common::size;

// ProductCheck dimensions follow the resolved S size.

/// A satisfying `ProductCheck` instance: leaves `f` of length `num_leaves`,
/// the product-tree MLE `v` of length `2·num_leaves` (s+1 variables), and
/// the claimed product `claimed = prod_x f(x)`.
struct ProductCheckInstance<F> {
    f: Vec<F>,
    v: Vec<F>,
    claimed: F,
}

/// Build the product-tree MLE ṽ on B_{s+1} (LSB-first) for the given leaves f.
///
/// Structure:
///   ṽ(0, `x_1`, ..., `x_S`) = `f(x_1`, ..., `x_S`)                    [leaves]
///   ṽ(1, `x_1`, ..., `x_S`) = `ṽ(x_1`, ..., `x_S`, 0) · `ṽ(x_1`, ..., `x_S`, 1)
/// with the self-referential top entry ṽ(1, ..., 1) := 0.
///
/// Layout in v[]: idx = `X_0` + `2·X_1` + ... + `2^s·X_S`. So leaves live at even
/// indices (v[2k] = f[k]); internal nodes live at odd indices.
fn build_product_tree<F: Field + Zero>(f: &[F]) -> Vec<F> {
    let n = f.len();
    assert!(n.is_power_of_two(), "num_leaves must be a power of 2");
    let mut v = vec![F::zero(); 2 * n];

    // Leaves (X_0 = 0 layer).
    for k in 0..n {
        v[2 * k] = f[k];
    }

    // Pin the self-referential top entry.
    v[2 * n - 1] = F::zero();

    // Fixed-point fill of remaining X_0 = 1 layer entries.
    // For each y in [0, n - 1): v[1 + 2y] = v[y] · v[y + n], when both deps
    // are already populated. Repeat passes until no changes.
    let mut done = vec![false; n];
    done[n - 1] = true;
    let mut changed = true;
    while changed {
        changed = false;
        for y in 0..n {
            if done[y] {
                continue;
            }
            // v[y] is ready iff y is even (leaf) or y odd with v[(y-1)/2 + 0]
            // already done... but really we just check if our deps were set.
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

/// Build a random satisfying `ProductCheck` instance.
fn random_productcheck<F, R>(rng: &mut R, num_leaves: usize) -> ProductCheckInstance<F>
where
    F: Field + Zero,
    R: Rng + ?Sized,
{
    let f: Vec<F> = (0..num_leaves).map(|_| F::rand(rng)).collect();
    let v = build_product_tree(&f);
    // Claimed product is ṽ(1, ..., 1, 0) = v[N - 1] where N = num_leaves.
    let claimed = v[num_leaves - 1];
    ProductCheckInstance { f, v, claimed }
}

fn make_inputs(sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as Backend>::F;
    let s = size(sizes, "S");
    let num_leaves = 1 << s;

    let mut rng = rand::rngs::OsRng;

    // -------------------------------------------------------------------
    // Generate a random satisfying ProductCheck instance.
    //
    //   f       (length num_leaves)        — MLE leaves on B_s
    //   v       (length 2·num_leaves)      — product-tree MLE on B_{s+1}
    //   claimed (scalar)                   — the claimed product (= root)
    //
    // Replace `random_productcheck(...)` with explicit constants if you
    // want to pin a specific instance.
    // -------------------------------------------------------------------
    let inst = random_productcheck::<F, _>(&mut rng, num_leaves);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("f_evs".to_string()), Value::vec_scalar(inst.f)),
        (Vid("v_evs".to_string()), Value::vec_scalar(inst.v)),
        (Vid("claimed".to_string()), Value::Scalar(inst.claimed)),
    ])
}

pub fn spec() -> common::ExampleSpec<ArkBls12_381> {
    common::ExampleSpec {
        source: "examples/hyperplonk_productcheck/hyperplonk_productcheck.zippel",
        run_defaults: &[("S", 18)],
        analysis_defaults: &[("S", 3)],
        validate: Some(|sizes, _analysis| {
            common::check_power_of_two(sizes, "S")?;
            Ok(())
        }),
        make_inputs,
        analyses: &[common::Analysis::Completeness],
    }
}
