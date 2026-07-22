// ProductCheck PIOP example driver.
//
// Builds a random satisfying instance with NUM_LEAVES = 2^S hypercube points
// for f and runs the parametric ProductCheck protocol from
// hyperplonk_productcheck.zippel on it.

use ark_ff::{Field, Zero};
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use rand::Rng;
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

// ProductCheck dimension. Edit S to scale; num_leaves = 2^S follows.
const S: usize = 2;
const NUM_LEAVES: usize = 1 << S; // = 2^S

fn main() {
    let zippel_file = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/hyperplonk_productcheck/hyperplonk_productcheck.zippel");

    println!("=== HyperPlonk ProductCheck PIOP ===");
    println!("num_leaves = {NUM_LEAVES}, s = log num_leaves = {S}");

    let args = ZippelArgs::new(zippel_file.clone());
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &S);
    handler.compile(&sizes);

    let inputs = prover_create_inputs();
    let prover_start = Instant::now();
    let proof = handler.run_prover(&inputs).expect("run_prover failed");
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkBls12_381>(&proof);
    println!("Prover time:    {prover_elapsed:.2?}");
    println!(
        "Proof size:     {proof_bytes} bytes ({} elements)",
        proof.len()
    );
    let verifier_start = Instant::now();
    let verifier_result = handler
        .run_verifier(&proof, &inputs)
        .expect("run_verifier failed");
    let verifier_elapsed = verifier_start.elapsed();
    let passed = check_verification(&verifier_result);
    println!("Verifier time:  {verifier_elapsed:.2?}");
    if passed {
        println!("Verification:   ✓ PASSED");
    } else {
        println!("Verification:   ✗ FAILED");
        std::process::exit(1);
    }

    let analysis_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        println!("\n--- Static Analysis ---");
        let analysis_args = ZippelArgs::new(zippel_file.clone());
        let mut analysis_handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(analysis_args);
        let mut analysis_sizes = Ctx::new();
        analysis_sizes.insert(&Tid::new("S"), &S);
        analysis_handler.compile(&analysis_sizes);

        let completeness_start = Instant::now();
        match analysis_handler.analyze_completeness() {
            Ok(()) => println!("Completeness:    ✓"),
            Err(e) => println!("Completeness:    ✗ {}", e),
        }
        println!("Completeness time: {:.2?}", completeness_start.elapsed());

        let zk_start = Instant::now();
        match analysis_handler.analyze_knowledge() {
            Ok(()) => println!("ZK:              ✓"),
            Err(e) => println!("ZK:              ✗ {}", e),
        }
        println!("ZK time:         {:.2?}", zk_start.elapsed());
    }));
    if analysis_result.is_err() {
        println!("Analysis:        ⚠ not supported (non-polynomial operations)");
    }
}

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
/// Layout in v[]: idx = `X_0` + `2·X_1` + ... + `2^S·X_S`. So leaves live at even
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

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as ArkConfig>::F;
    let mut rng = rand::rngs::OsRng;

    // -------------------------------------------------------------------
    // Generate a random satisfying ProductCheck instance.
    //
    //   f       (length NUM_LEAVES)        — MLE leaves on B_s
    //   v       (length 2·NUM_LEAVES)      — product-tree MLE on B_{s+1}
    //   claimed (scalar)                   — the claimed product (= root)
    //
    // Replace `random_productcheck(...)` with explicit constants if you
    // want to pin a specific instance.
    // -------------------------------------------------------------------
    let inst = random_productcheck::<F, _>(&mut rng, NUM_LEAVES);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("f_evs".to_string()), Value::VecScalar(inst.f)),
        (Vid("v_evs".to_string()), Value::VecScalar(inst.v)),
        (Vid("claimed".to_string()), Value::Scalar(inst.claimed)),
    ])
}
