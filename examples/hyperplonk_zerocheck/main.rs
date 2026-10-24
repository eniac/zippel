// Multivariate ZeroCheck PIOP example driver.
//
// Builds a random satisfying instance with num_points hypercube points and
// runs the ZeroCheck protocol from hyperplonk_zerocheck.zippel on it.

use ark_ff::Field;
use backend::{ArkBls12_381, Backend, Value};
use lang::id::Vid;
use rand::Rng;
use share::Ctx;

use crate::common;
use crate::common::size;

// ZeroCheck dimension. The proto is parametric over s = log2(num_points);
// here we instantiate s = 2 by passing s = 2 into the compile context, and
// num_points = 2^s = 4 follows. Bump s to scale up the example.

/// A satisfying `ZeroCheck` instance: three length-`num_points` MLE evaluation
/// vectors `a`, `b`, `c` with `c = a ⊙ b` (Hadamard) on every hypercube
/// point, so that `f(x) = a(x)·b(x) - c(x)` vanishes on `B_s`.
struct ZeroCheckInstance<F> {
    a: Vec<F>,
    b: Vec<F>,
    c: Vec<F>,
}

/// Build a random satisfying `ZeroCheck` instance: draw `a` and `b` uniformly,
/// set `c[i] = a[i] · b[i]`.
fn random_zerocheck<F, R>(rng: &mut R, num_points: usize) -> ZeroCheckInstance<F>
where
    F: Field,
    R: Rng + ?Sized,
{
    let a: Vec<F> = (0..num_points).map(|_| F::rand(rng)).collect();
    let b: Vec<F> = (0..num_points).map(|_| F::rand(rng)).collect();
    let c: Vec<F> = a.iter().zip(b.iter()).map(|(x, y)| *x * *y).collect();
    ZeroCheckInstance { a, b, c }
}

fn make_inputs(sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as Backend>::F;
    let s = size(sizes, "S");
    let num_points = 1 << s;

    let mut rng = rand::rngs::OsRng;

    // -------------------------------------------------------------------
    // Generate a random satisfying ZeroCheck instance.
    //
    //   a, b, c (length num_points each)  — MLE evaluations with c = a ⊙ b
    //
    // Replace `random_zerocheck(...)` with explicit Vec<F> constants below
    // if you want to pin a specific instance.
    // -------------------------------------------------------------------
    let inst = random_zerocheck::<F, _>(&mut rng, num_points);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("a_evs".to_string()), Value::vec_scalar(inst.a)),
        (Vid("b_evs".to_string()), Value::vec_scalar(inst.b)),
        (Vid("c_evs".to_string()), Value::vec_scalar(inst.c)),
    ])
}

pub fn spec() -> common::ExampleSpec<ArkBls12_381> {
    common::ExampleSpec {
        source: "examples/hyperplonk_zerocheck/hyperplonk_zerocheck.zippel",
        defaults: &[("S", 3)],
        validate: Some(|sizes, _analysis| {
            common::check_power_of_two(sizes, "S")?;
            Ok(())
        }),
        make_inputs,
        analyses: &[common::Analysis::Completeness, common::Analysis::Zk],
    }
}
