// HyperPlonk example driver.

use ark_ff::{Field, One, Zero};
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use rand::Rng;
use rand::seq::SliceRandom;
use share::Ctx;
use std::{path::PathBuf, time::Instant};
use zippel::*;

// Edit S to scale; num_gates = 2^S follows.
const S: usize = 3;
const NUM_GATES: usize = 1 << S;

pub fn run(_args: &[String]) {
    let zippel_file =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/hyperplonk/hyperplonk.zippel");

    println!("=== HyperPlonk (gate identity + 3-wire wiring) ===");
    println!("num_gates = {NUM_GATES}, s = log num_gates = {S}");

    let args = ZippelArgs::new(zippel_file.clone());
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("S"), &S);
    sizes.insert(&Tid::new("N"), &NUM_GATES);
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
        analysis_sizes.insert(&Tid::new("N"), &NUM_GATES);
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
    s_id_a: Vec<F>,
    s_id_b: Vec<F>,
    s_id_c: Vec<F>,
    s_sigma_a: Vec<F>,
    s_sigma_b: Vec<F>,
    s_sigma_c: Vec<F>,
    r2: F,
    r: F,
    v_a: Vec<F>,
    v_b: Vec<F>,
    v_c: Vec<F>,
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

/// Build a random satisfying Plonkish instance with a full 3N-cell σ.
fn random_plonkish<F, R>(rng: &mut R, num_gates: usize) -> PlonkishInstance<F>
where
    F: Field + Zero + One,
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

    // a is random; shuffled gives b[i] = a[shuffled[i]].
    let a: Vec<F> = (0..num_gates).map(|_| F::rand(rng)).collect();
    let mut shuffled: Vec<usize> = (0..num_gates).collect();
    shuffled.shuffle(rng);
    let b: Vec<F> = shuffled.iter().map(|&j| a[j]).collect();
    let c: Vec<F> = (0..num_gates)
        .map(|i| {
            let lhs = q_l[i] * a[i] + q_r[i] * b[i] + q_m[i] * a[i] * b[i] + q_c[i];
            -lhs * q_o[i].inverse().expect("q_O[i] non-zero")
        })
        .collect();

    // Build the 3N-cell permutation σ. Cells are indexed
    //   0..N       -> a-cells   (row i -> index i)
    //   N..2N      -> b-cells   (row i -> index N + i)
    //   2N..3N     -> c-cells   (row i -> index 2N + i)
    // For each row i, b[i] == a[shuffled[i]] gives the equivalence class
    //   { a-cell shuffled[i], b-cell i },
    // which we realize as a 2-cycle. All c-cells sit in singleton classes
    // (their values are, w.h.p., distinct from all a/b values), so σ acts
    // as the identity on them. This yields a valid permutation on the 3N
    // slots with w[σ(k)] == w[k] everywhere.
    let mut sigma_a: Vec<usize> = (0..num_gates).collect();
    let mut sigma_b: Vec<usize> = (0..num_gates).map(|i| num_gates + i).collect();
    let sigma_c: Vec<usize> = (0..num_gates).map(|i| 2 * num_gates + i).collect();
    for i in 0..num_gates {
        let j = shuffled[i];
        sigma_a[j] = num_gates + i;
        sigma_b[i] = j;
    }

    let s_id_a: Vec<F> = (0..num_gates).map(|i| F::from(i as u64)).collect();
    let s_id_b: Vec<F> = (0..num_gates)
        .map(|i| F::from((num_gates + i) as u64))
        .collect();
    let s_id_c: Vec<F> = (0..num_gates)
        .map(|i| F::from((2 * num_gates + i) as u64))
        .collect();
    let s_sigma_a: Vec<F> = sigma_a.iter().map(|&j| F::from(j as u64)).collect();
    let s_sigma_b: Vec<F> = sigma_b.iter().map(|&j| F::from(j as u64)).collect();
    let s_sigma_c: Vec<F> = sigma_c.iter().map(|&j| F::from(j as u64)).collect();

    // Simulate verifier-side FS draws of r2 and r for the permutation phase.
    let r2 = F::rand(rng);
    let r = F::rand(rng);

    // Per-column rational leaves and their grand-product trees.
    let build_leaves = |s_id: &[F], s_sigma: &[F], w: &[F]| -> Vec<F> {
        (0..num_gates)
            .map(|i| {
                let num = r + s_id[i] + r2 * w[i];
                let den = r + s_sigma[i] + r2 * w[i];
                num * den.inverse().expect("r + s_sigma + r2*w nonzero")
            })
            .collect()
    };
    let leaves_a = build_leaves(&s_id_a, &s_sigma_a, &a);
    let leaves_b = build_leaves(&s_id_b, &s_sigma_b, &b);
    let leaves_c = build_leaves(&s_id_c, &s_sigma_c, &c);
    let v_a = build_v_tree(&leaves_a);
    let v_b = build_v_tree(&leaves_b);
    let v_c = build_v_tree(&leaves_c);

    // Sanity: the coupling identity that the proto checks.
    let root_prod = v_a[num_gates - 1] * v_b[num_gates - 1] * v_c[num_gates - 1];
    assert_eq!(
        root_prod,
        F::one(),
        "coupling identity v_a[N-1] * v_b[N-1] * v_c[N-1] != 1"
    );

    PlonkishInstance {
        a,
        b,
        c,
        q_l,
        q_r,
        q_o,
        q_m,
        q_c,
        s_id_a,
        s_id_b,
        s_id_c,
        s_sigma_a,
        s_sigma_b,
        s_sigma_c,
        r2,
        r,
        v_a,
        v_b,
        v_c,
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
        (Vid("s_id_a_evs".to_string()), Value::VecScalar(inst.s_id_a)),
        (Vid("s_id_b_evs".to_string()), Value::VecScalar(inst.s_id_b)),
        (Vid("s_id_c_evs".to_string()), Value::VecScalar(inst.s_id_c)),
        (
            Vid("s_sigma_a_evs".to_string()),
            Value::VecScalar(inst.s_sigma_a),
        ),
        (
            Vid("s_sigma_b_evs".to_string()),
            Value::VecScalar(inst.s_sigma_b),
        ),
        (
            Vid("s_sigma_c_evs".to_string()),
            Value::VecScalar(inst.s_sigma_c),
        ),
        (Vid("r2".to_string()), Value::Scalar(inst.r2)),
        (Vid("r".to_string()), Value::Scalar(inst.r)),
        (Vid("v_a_evs".to_string()), Value::VecScalar(inst.v_a)),
        (Vid("v_b_evs".to_string()), Value::VecScalar(inst.v_b)),
        (Vid("v_c_evs".to_string()), Value::VecScalar(inst.v_c)),
    ])
}
