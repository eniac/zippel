// HyperPlonk example driver.

use ark_ff::{Field, Zero};
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use rand::Rng;
use rand::seq::SliceRandom;
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

// Edit S to scale; num_gates = 2^S follows.
const S: usize = 2;
const NUM_GATES: usize = 1 << S;

fn main() {
    let zippel_file =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/hyperplonk/hyperplonk.zippel");

    println!("=== HyperPlonk (gate identity + wiring) ===");
    println!("num_gates = {NUM_GATES}, s = log num_gates = {S}");

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

struct PlonkishInstance<F> {
    a: Vec<F>,
    b: Vec<F>,
    c: Vec<F>,
    q_l: Vec<F>,
    q_r: Vec<F>,
    q_o: Vec<F>,
    q_m: Vec<F>,
    q_c: Vec<F>,
    s_sigma: Vec<F>,
    s_id: Vec<F>,
    r2: F,
    r: F,
    v_evs: Vec<F>,
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

/// Build a random satisfying Plonkish instance.
fn random_plonkish<F, R>(rng: &mut R, num_gates: usize) -> PlonkishInstance<F>
where
    F: Field + Zero,
    R: Rng + ?Sized,
{
    let q_l: Vec<F> = (0..num_gates).map(|_| F::rand(rng)).collect();
    let q_r: Vec<F> = (0..num_gates).map(|_| F::rand(rng)).collect();
    let q_m: Vec<F> = (0..num_gates).map(|_| F::rand(rng)).collect();
    let q_c: Vec<F> = (0..num_gates).map(|_| F::rand(rng)).collect();
    let q_o: Vec<F> = (0..num_gates)
        .map(|_| {
            let mut v = F::rand(rng);
            while v.is_zero() {
                v = F::rand(rng);
            }
            v
        })
        .collect();

    let a: Vec<F> = (0..num_gates).map(|_| F::rand(rng)).collect();
    let mut sigma: Vec<usize> = (0..num_gates).collect();
    sigma.shuffle(rng);
    let b: Vec<F> = sigma.iter().map(|&j| a[j]).collect();
    let c: Vec<F> = (0..num_gates)
        .map(|i| {
            let lhs = q_l[i] * a[i] + q_r[i] * b[i] + q_m[i] * a[i] * b[i] + q_c[i];
            -lhs * q_o[i].inverse().expect("q_O[i] non-zero")
        })
        .collect();

    let s_sigma: Vec<F> = sigma.iter().map(|&j| F::from(j as u64)).collect();
    let s_id: Vec<F> = (0..num_gates).map(|i| F::from(i as u64)).collect();

    // Simulate verifier-side FS draws of r2 and r for the permutation phase.
    let r2 = F::rand(rng);
    let r = F::rand(rng);

    let f_hat: Vec<F> = (0..num_gates).map(|i| s_id[i] + r2 * a[i]).collect();
    let g_hat: Vec<F> = (0..num_gates).map(|i| s_sigma[i] + r2 * b[i]).collect();
    let leaves: Vec<F> = (0..num_gates)
        .map(|i| (r + f_hat[i]) * (r + g_hat[i]).inverse().expect("r + g_hat[i] nonzero"))
        .collect();
    let v_evs = build_v_tree(&leaves);

    PlonkishInstance {
        a,
        b,
        c,
        q_l,
        q_r,
        q_o,
        q_m,
        q_c,
        s_sigma,
        s_id,
        r2,
        r,
        v_evs,
    }
}

fn prover_create_inputs() -> Ctx<Vid, Value<ArkBls12_381>> {
    type F = <ArkBls12_381 as ArkConfig>::F;
    let mut rng = rand::rngs::OsRng;

    let inst = random_plonkish::<F, _>(&mut rng, NUM_GATES);

    // Sanity check.
    for i in 0..NUM_GATES {
        let gate = inst.q_l[i] * inst.a[i]
            + inst.q_r[i] * inst.b[i]
            + inst.q_o[i] * inst.c[i]
            + inst.q_m[i] * inst.a[i] * inst.b[i]
            + inst.q_c[i];
        assert!(gate.is_zero(), "gate {i} unsatisfied");
    }

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("a_evs".to_string()), Value::VecScalar(inst.a)),
        (Vid("b_evs".to_string()), Value::VecScalar(inst.b)),
        (Vid("c_evs".to_string()), Value::VecScalar(inst.c)),
        (Vid("q_l_evs".to_string()), Value::VecScalar(inst.q_l)),
        (Vid("q_r_evs".to_string()), Value::VecScalar(inst.q_r)),
        (Vid("q_o_evs".to_string()), Value::VecScalar(inst.q_o)),
        (Vid("q_m_evs".to_string()), Value::VecScalar(inst.q_m)),
        (Vid("q_c_evs".to_string()), Value::VecScalar(inst.q_c)),
        (
            Vid("s_sigma_evs".to_string()),
            Value::VecScalar(inst.s_sigma),
        ),
        (Vid("s_id_evs".to_string()), Value::VecScalar(inst.s_id)),
        (Vid("r2".to_string()), Value::Scalar(inst.r2)),
        (Vid("r".to_string()), Value::Scalar(inst.r)),
        (Vid("v_evs".to_string()), Value::VecScalar(inst.v_evs)),
    ])
}
