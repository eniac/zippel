// MultiSet Check PIOP example driver.

use ark_ff::{Field, Zero};
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use rand::Rng;
use rand::seq::SliceRandom;
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

// Edit S to scale; num_points = 2^S follows.
const S: usize = 2;
const NUM_POINTS: usize = 1 << S;

fn main() {
    let zippel_file = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/hyperplonk_multiset/hyperplonk_multiset.zippel");

    println!("=== HyperPlonk MultiSet Check PIOP ===");
    println!("num_points = {NUM_POINTS}, s = log num_points = {S}");

    let args = ZippelArgs::new(zippel_file.clone());
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &S);
    handler.compile(&sizes);

    let inputs = prover_create_inputs();
    let prover_start = Instant::now();
    let proof = handler.run_prover(inputs).expect("run_prover failed");
    let prover_elapsed = prover_start.elapsed();
    let proof_bytes = proof_size_bytes::<ArkBls12_381>(&proof);
    println!("Prover time:    {prover_elapsed:.2?}");
    println!(
        "Proof size:     {proof_bytes} bytes ({} elements)",
        proof.len()
    );
    let verifier_start = Instant::now();
    let verifier_result = handler.run_verifier(proof).expect("run_verifier failed");
    let verifier_elapsed = verifier_start.elapsed();
    let result = check_verification(verifier_result);
    println!("Verifier time:  {verifier_elapsed:.2?}");
    if result.passed {
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

struct MultiSetInstance<F> {
    f: Vec<F>,
    g: Vec<F>,
    r: F,
    v_evs: Vec<F>,
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

/// Build a random satisfying MultiSet instance.
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
    let leaves: Vec<F> = f
        .iter()
        .zip(g.iter())
        .map(|(fi, gi)| (r + *fi) * (r + *gi).inverse().expect("r + g[i] nonzero"))
        .collect();
    let v_evs = build_v_tree(&leaves);

    MultiSetInstance { f, g, r, v_evs }
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as ArkConfig>::F;
    let mut rng = rand::rngs::OsRng;

    let inst = random_multiset::<F, _>(&mut rng, NUM_POINTS);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("f_evs".to_string()), Value::VecScalar(inst.f)),
        (Vid("g_evs".to_string()), Value::VecScalar(inst.g)),
        (Vid("r".to_string()), Value::Scalar(inst.r)),
        (Vid("v_evs".to_string()), Value::VecScalar(inst.v_evs)),
    ])
}
