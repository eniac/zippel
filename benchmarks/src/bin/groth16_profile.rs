//! Stage-by-stage profiling of the Groth16 prover, native vs. zippel.
//!
//! Splits each side's prove time into:
//!   - sparse MVMs (A·z, B·z, C·z)
//!   - IFFT + coset FFT + pointwise (h_coeffs minus the MVMs)
//!   - into_bigint conversions
//!   - the 5 MSMs (A, B_g2, B_g1, L, H)
//!   - scalar arithmetic / final adds
//!
//! For the zippel side we instead just time:
//!   - witness_map total (MVM + FFTs)
//!   - `run_prover` total (zippel runtime: all 5 MSMs + scalar arith)
//!
//! Run with `RAYON_NUM_THREADS=N` to control parallelism; `--log-size N`
//! picks the circuit size.

use ark_bls12_381::{Fr as GitFr, G1Projective, G2Projective};
use ark_ec::{CurveGroup, VariableBaseMSM};
use ark_ff::{PrimeField, UniformRand, Zero};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use backend::{ArkBls12_381, Value};
use benchmarks::groth16::{bridge, build_translated, shared};
use clap::Parser;
use lang::id::{Tid, Vid};
use share::Ctx;
use std::path::PathBuf;
use std::time::Instant;
use zippel::{ZippelArgs, ZippelHandler};

#[derive(Parser, Debug)]
struct Args {
    #[arg(long, default_value_t = 10)]
    log_size: usize,
}

fn main() {
    let args = Args::parse();
    let n = 1usize << args.log_size;
    eprintln!("env RAYON_NUM_THREADS = {:?}", std::env::var("RAYON_NUM_THREADS"));
    eprintln!(
        "rayon current_num_threads = {}",
        rayon::current_num_threads()
    );
    // CONTROL: 1 MSM on its own, time it. If RAYON_NUM_THREADS=1 truly
    // limits parallelism, this should scale linearly with thread count.
    {
        use ark_ec::pairing::Pairing;
        let s = shared::build(1usize << 12);
        let t = bridge::translate_shared(&s);
        let q: Vec<<ark_bls12_381::Bls12_381 as Pairing>::G1Affine> =
            G1Projective::normalize_batch(&t.keys.a_query);
        let bi: Vec<<GitFr as PrimeField>::BigInt> =
            t.full_assignment.iter().map(|x| x.into_bigint()).collect();
        // Warm-up.
        let _ = G1Projective::msm_bigint(&q, &bi);
        let tic = Instant::now();
        for _ in 0..3 { let _ = G1Projective::msm_bigint(&q, &bi); }
        eprintln!("CONTROL: 3× single G1 MSM (size {}): {:?}", q.len(), tic.elapsed());
    }
    eprintln!("=== Groth16 prove stage profile (log_size={}, C={}) ===", args.log_size, n);

    let s = shared::build(n);
    let t = bridge::translate_shared(&s);
    let _ = build_translated; // referenced from the public API; just silence unused import.

    eprintln!("dims: M={} L={} H={} num_vars={}", t.m, t.l, t.h_size, t.full_assignment.len());

    // --- NATIVE breakdown ------------------------------------------------
    eprintln!("\n--- NATIVE (vendored) breakdown ---");
    let a_query: Vec<<ark_bls12_381::Bls12_381 as ark_ec::pairing::Pairing>::G1Affine> =
        G1Projective::normalize_batch(&t.keys.a_query);
    let b_g1_query: Vec<_> = G1Projective::normalize_batch(&t.keys.b_g1_query);
    let b_g2_query: Vec<_> = G2Projective::normalize_batch(&t.keys.b_g2_query);
    let h_query: Vec<_> = G1Projective::normalize_batch(&t.keys.h_query);
    let l_query: Vec<_> = G1Projective::normalize_batch(&t.keys.l_query);

    let mut rng = ark_std::test_rng();
    let r = GitFr::rand(&mut rng);
    let s_rand = GitFr::rand(&mut rng);

    // MVM only
    let zero = GitFr::zero();
    let domain_size = GeneralEvaluationDomain::<GitFr>::new(t.num_constraints + t.num_inputs)
        .unwrap()
        .size();
    let mut a_eval = vec![zero; domain_size];
    let mut b_eval = vec![zero; domain_size];
    let mut c_eval = vec![zero; domain_size];
    let tic = Instant::now();
    for (i, row) in t.mat.a.iter().enumerate() {
        for (cc, j) in row {
            a_eval[i] += *cc * t.full_assignment[*j];
        }
    }
    for (i, row) in t.mat.b.iter().enumerate() {
        for (cc, j) in row {
            b_eval[i] += *cc * t.full_assignment[*j];
        }
    }
    for (i, row) in t.mat.c.iter().enumerate() {
        for (cc, j) in row {
            c_eval[i] += *cc * t.full_assignment[*j];
        }
    }
    for i in 0..t.num_inputs {
        a_eval[t.num_constraints + i] = t.full_assignment[i];
    }
    eprintln!("  MVM (A,B,C·z + identity tail):  {:>9.2?}", tic.elapsed());

    let tic = Instant::now();
    let mut h_coeffs = bridge::witness_map(&t.mat, t.num_inputs, t.num_constraints, &t.full_assignment);
    h_coeffs.resize(t.h_size, GitFr::zero());
    eprintln!("  witness_map total (MVM + FFTs): {:>9.2?}", tic.elapsed());

    let tic = Instant::now();
    let full_bi: Vec<<GitFr as PrimeField>::BigInt> = t.full_assignment.iter().map(|x| x.into_bigint()).collect();
    let wit_bi: Vec<<GitFr as PrimeField>::BigInt> = t.witness_assignment.iter().map(|x| x.into_bigint()).collect();
    let h_bi: Vec<<GitFr as PrimeField>::BigInt> = h_coeffs.iter().map(|x| x.into_bigint()).collect();
    eprintln!("  into_bigint x3:                 {:>9.2?}", tic.elapsed());

    let tic = Instant::now();
    let _a = G1Projective::msm_bigint(&a_query, &full_bi);
    eprintln!("  MSM A    (size={}, G1):         {:>9.2?}", a_query.len(), tic.elapsed());
    let tic = Instant::now();
    let _b_g2 = G2Projective::msm_bigint(&b_g2_query, &full_bi);
    eprintln!("  MSM B_g2 (size={}, G2):         {:>9.2?}", b_g2_query.len(), tic.elapsed());
    let tic = Instant::now();
    let _b_g1 = G1Projective::msm_bigint(&b_g1_query, &full_bi);
    eprintln!("  MSM B_g1 (size={}, G1):         {:>9.2?}", b_g1_query.len(), tic.elapsed());
    let tic = Instant::now();
    let _l = G1Projective::msm_bigint(&l_query, &wit_bi);
    eprintln!("  MSM L    (size={}, G1):         {:>9.2?}", l_query.len(), tic.elapsed());
    let tic = Instant::now();
    let _h = G1Projective::msm_bigint(&h_query, &h_bi);
    eprintln!("  MSM H    (size={}, G1):         {:>9.2?}", h_query.len(), tic.elapsed());

    // Variant A: do the 5 MSMs via VariableBaseMSM::msm (the same call
    // zippel ends up at, via G::msm(g, f) in config.rs::vec_dot). This
    // avoids the explicit into_bigint pre-pass; msm() does it internally
    // and may be implemented differently.
    eprintln!("\n--- NATIVE variant A: G::msm(bases, scalars) (no explicit into_bigint) ---");
    let tic = Instant::now();
    let _a2 = <G1Projective as VariableBaseMSM>::msm(&a_query, &t.full_assignment).unwrap();
    let _b1_2 = <G1Projective as VariableBaseMSM>::msm(&b_g1_query, &t.full_assignment).unwrap();
    let _b2_2 = <G2Projective as VariableBaseMSM>::msm(&b_g2_query, &t.full_assignment).unwrap();
    let _l2 = <G1Projective as VariableBaseMSM>::msm(&l_query, &t.witness_assignment).unwrap();
    let _h2 = <G1Projective as VariableBaseMSM>::msm(&h_query, &h_coeffs).unwrap();
    eprintln!("  5 MSMs via G::msm (sequential):  {:>9.2?}", tic.elapsed());

    // Variant B: do all 5 MSMs via msm_bigint, the way the vendored prover does.
    eprintln!("\n--- NATIVE variant B: msm_bigint sequential (mirrors vendored prove) ---");
    let tic = Instant::now();
    let full_bi: Vec<<GitFr as PrimeField>::BigInt> = t.full_assignment.iter().map(|x| x.into_bigint()).collect();
    let wit_bi: Vec<<GitFr as PrimeField>::BigInt> = t.witness_assignment.iter().map(|x| x.into_bigint()).collect();
    let h_bi: Vec<<GitFr as PrimeField>::BigInt> = h_coeffs.iter().map(|x| x.into_bigint()).collect();
    let _a3 = G1Projective::msm_bigint(&a_query, &full_bi);
    let _b1_3 = G1Projective::msm_bigint(&b_g1_query, &full_bi);
    let _b2_3 = G2Projective::msm_bigint(&b_g2_query, &full_bi);
    let _l3 = G1Projective::msm_bigint(&l_query, &wit_bi);
    let _h3 = G1Projective::msm_bigint(&h_query, &h_bi);
    eprintln!("  5 MSMs via msm_bigint (seq):     {:>9.2?}", tic.elapsed());

    // Variant C: do them concurrently via rayon::scope, with per-task timing.
    eprintln!("\n--- NATIVE variant C: rayon::scope to run 5 MSMs concurrently ---");
    use std::sync::Mutex;
    let per_msm = Mutex::new(Vec::<(usize, std::time::Duration, std::time::Duration, std::thread::ThreadId)>::new());
    let scope_start = Instant::now();
    rayon::scope(|s| {
        s.spawn(|_| {
            let started = scope_start.elapsed();
            let tic2 = Instant::now();
            let _ = G1Projective::msm_bigint(&a_query, &full_bi);
            per_msm.lock().unwrap().push((0, started, tic2.elapsed(), std::thread::current().id()));
        });
        s.spawn(|_| {
            let started = scope_start.elapsed();
            let tic2 = Instant::now();
            let _ = G1Projective::msm_bigint(&b_g1_query, &full_bi);
            per_msm.lock().unwrap().push((1, started, tic2.elapsed(), std::thread::current().id()));
        });
        s.spawn(|_| {
            let started = scope_start.elapsed();
            let tic2 = Instant::now();
            let _ = G2Projective::msm_bigint(&b_g2_query, &full_bi);
            per_msm.lock().unwrap().push((2, started, tic2.elapsed(), std::thread::current().id()));
        });
        s.spawn(|_| {
            let started = scope_start.elapsed();
            let tic2 = Instant::now();
            let _ = G1Projective::msm_bigint(&l_query, &wit_bi);
            per_msm.lock().unwrap().push((3, started, tic2.elapsed(), std::thread::current().id()));
        });
        s.spawn(|_| {
            let started = scope_start.elapsed();
            let tic2 = Instant::now();
            let _ = G1Projective::msm_bigint(&h_query, &h_bi);
            per_msm.lock().unwrap().push((4, started, tic2.elapsed(), std::thread::current().id()));
        });
    });
    eprintln!("  5 MSMs via rayon::scope:         {:>9.2?}", scope_start.elapsed());
    let pm = per_msm.into_inner().unwrap();
    for (idx, started_after, dur, tid) in pm {
        eprintln!("    spawn {} started+{:>8.2?}, took {:>9.2?}, tid={:?}", idx, started_after, dur, tid);
    }

    // Variant C2: inside each spawn, also call par_iter and measure
    // how many distinct OS thread IDs actually execute work.
    eprintln!("\n--- NATIVE variant C2: probe how many threads par_iter actually uses inside scope spawn ---");
    let inner_tids = std::sync::Mutex::new(std::collections::HashSet::<std::thread::ThreadId>::new());
    let tic = Instant::now();
    rayon::scope(|s| {
        for _ in 0..5 {
            s.spawn(|_| {
                use rayon::prelude::*;
                let n = 1_000_000usize;
                let v: Vec<u64> = (0..n).map(|i| i as u64).collect();
                let _sum: u64 = v.par_iter().map(|x| {
                    inner_tids.lock().unwrap().insert(std::thread::current().id());
                    x.wrapping_mul(3).wrapping_add(7)
                }).sum();
            });
        }
    });
    let dur = tic.elapsed();
    let s_set = inner_tids.into_inner().unwrap();
    eprintln!("  par_iter inside scope spawn — distinct OS thread IDs: {} (took {:?})", s_set.len(), dur);
    eprintln!("  thread IDs: {:?}", s_set);

    // Variant C': same scope, but inside an explicit 1-thread pool.
    eprintln!("\n--- NATIVE variant C': rayon::scope INSIDE a 1-thread pool ---");
    let pool = rayon::ThreadPoolBuilder::new().num_threads(1).build().unwrap();
    let tic = Instant::now();
    pool.install(|| {
        rayon::scope(|s| {
            s.spawn(|_| { let _ = G1Projective::msm_bigint(&a_query, &full_bi); });
            s.spawn(|_| { let _ = G1Projective::msm_bigint(&b_g1_query, &full_bi); });
            s.spawn(|_| { let _ = G2Projective::msm_bigint(&b_g2_query, &full_bi); });
            s.spawn(|_| { let _ = G1Projective::msm_bigint(&l_query, &wit_bi); });
            s.spawn(|_| { let _ = G1Projective::msm_bigint(&h_query, &h_bi); });
        });
    });
    eprintln!("  pool(1)::scope:                  {:>9.2?}", tic.elapsed());

    // Variant D: also call msm_bigint OUTSIDE any scope, just spawning std::thread.
    eprintln!("\n--- NATIVE variant D: std::thread::spawn (5 native OS threads) ---");
    let tic = Instant::now();
    let handles: Vec<_> = vec![
        {
            let a_query = a_query.clone();
            let full_bi = full_bi.clone();
            std::thread::spawn(move || { let _ = G1Projective::msm_bigint(&a_query, &full_bi); })
        },
        {
            let b_g1_query = b_g1_query.clone();
            let full_bi = full_bi.clone();
            std::thread::spawn(move || { let _ = G1Projective::msm_bigint(&b_g1_query, &full_bi); })
        },
        {
            let b_g2_query = b_g2_query.clone();
            let full_bi = full_bi.clone();
            std::thread::spawn(move || { let _ = G2Projective::msm_bigint(&b_g2_query, &full_bi); })
        },
        {
            let l_query = l_query.clone();
            let wit_bi = wit_bi.clone();
            std::thread::spawn(move || { let _ = G1Projective::msm_bigint(&l_query, &wit_bi); })
        },
        {
            let h_query = h_query.clone();
            let h_bi = h_bi.clone();
            std::thread::spawn(move || { let _ = G1Projective::msm_bigint(&h_query, &h_bi); })
        },
    ];
    for h in handles { h.join().unwrap(); }
    eprintln!("  5 MSMs via std::thread::spawn:   {:>9.2?}", tic.elapsed());

    // --- ZIPPEL breakdown ------------------------------------------------
    eprintln!("\n--- ZIPPEL breakdown ---");
    let args_z = ZippelArgs::new(PathBuf::from("examples/groth16/groth16-opt.zippel"));
    let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args_z);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("M"), &t.m);
    sizes.insert(&Tid::new("L"), &t.l);
    sizes.insert(&Tid::new("H"), &t.h_size);
    handler.compile(&sizes);

    let inputs_base = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("alpha_g1".to_string()), Value::G1(t.keys.alpha_g1)),
        (Vid("beta_g2".to_string()), Value::G2(t.keys.beta_g2)),
        (Vid("gamma_g2".to_string()), Value::G2(t.keys.gamma_g2)),
        (Vid("delta_g2".to_string()), Value::G2(t.keys.delta_g2)),
        (Vid("gamma_abc_g1".to_string()), Value::VecG1(t.keys.gamma_abc_g1.clone())),
        (Vid("beta_g1".to_string()), Value::G1(t.keys.beta_g1)),
        (Vid("delta_g1".to_string()), Value::G1(t.keys.delta_g1)),
        (Vid("a_query".to_string()), Value::VecG1(t.keys.a_query.clone())),
        (Vid("b_g1_query".to_string()), Value::VecG1(t.keys.b_g1_query.clone())),
        (Vid("b_g2_query".to_string()), Value::VecG2(t.keys.b_g2_query.clone())),
        (Vid("h_query".to_string()), Value::VecG1(t.keys.h_query.clone())),
        (Vid("l_query".to_string()), Value::VecG1(t.keys.l_query.clone())),
        (Vid("instance_assignment".to_string()), Value::VecScalar(t.instance_assignment.clone())),
        (Vid("witness_assignment".to_string()), Value::VecScalar(t.witness_assignment.clone())),
    ]);

    let tic = Instant::now();
    let mut h_coeffs = bridge::witness_map(&t.mat, t.num_inputs, t.num_constraints, &t.full_assignment);
    h_coeffs.resize(t.h_size, GitFr::zero());
    let mut inputs = inputs_base.clone();
    inputs.insert(&Vid("h_coeffs".to_string()), &Value::VecScalar(h_coeffs));
    eprintln!("  witness_map + input clone:      {:>9.2?}", tic.elapsed());

    let sched = handler.default_schedule_prover();
    let tic = Instant::now();
    let _proof = handler.run_prover(sched, inputs).expect("zippel prove");
    eprintln!("  run_prover (all 5 MSMs + arith): {:>9.2?}", tic.elapsed());

    // Suppress unused warnings.
    let _ = (r, s_rand, a_eval, b_eval, c_eval);
}
