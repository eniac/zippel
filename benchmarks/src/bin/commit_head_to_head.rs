//! Same-binary, same-run head-to-head of the two witness-commit blocks.
//!
//! Background: the instrumented cross-build comparison recorded zippel's
//! MSM bucket scaling 1.76x from M=17 to 18 while ark-spartan's
//! polycommit timer recorded 1.36x — but the `msm_batch_ceiling` bin
//! showed the shared primitive's intrinsic scaling at these shapes is
//! ~1.73x, which matches zippel and *cannot* be beaten by the same
//! primitive at the same shape. This bin removes every confound: one
//! binary, one process, same witness data, back to back:
//!
//!   Z : zippel's `c_rows` computation — per row i:
//!       `h * r_rows[i] + msm(g_vec, w[i*ncols .. (i+1)*ncols])`
//!   S : ark-spartan's actual `DensePolynomial::commit` (multicore
//!       row par_iter + RandomTape blinds), exactly as R1CSProof calls it.
//!
//! If Z ~= S at every M (the ceiling bin predicts they must be), the
//! "MSM cliff" attribution from the instrumented session was a
//! measurement artifact and the true 17->18 gap lives elsewhere.
//!
//! Run: RAYON_NUM_THREADS=1 cargo run --release --bin commit_head_to_head

use ark_curve25519::{EdwardsAffine, EdwardsProjective, Fr};
use ark_ec::{CurveGroup, VariableBaseMSM};
use ark_ff::UniformRand;
use ark_std::Zero;
use ark_std::rand::SeedableRng;
use ark_std::rand::rngs::StdRng;
use benchmarks::ark_spartan_upstream::dense_mlpoly::{DensePolynomial, PolyCommitmentGens};
use benchmarks::ark_spartan_upstream::random::RandomTape;
use rayon::prelude::*;
use std::time::Instant;

fn mean_ms(samples: &[f64]) -> f64 {
    samples.iter().sum::<f64>() / samples.len() as f64
}

fn main() {
    // H2H_INSTALL=1: run the whole benchmark body inside a 1-thread
    // rayon pool's `install()`. Inside the pool, par_iter cannot recruit
    // the external main thread, so "1 thread" truly means one core. The
    // control for the parallelism-leak hypothesis: if Z_par collapses to
    // Z under install, the leak is confirmed as rayon's external-caller
    // participation.
    let confined = std::env::var("H2H_INSTALL").as_deref() == Ok("1");
    if confined {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .build()
            .expect("pool");
        pool.install(run_all);
    } else {
        run_all();
    }
}

fn run_all() {
    const REPS: usize = 3;
    println!("witness-commit head-to-head (curve25519 / arkworks 0.6)");
    println!(
        "threads: RAYON_NUM_THREADS={}  install-confined: {}",
        std::env::var("RAYON_NUM_THREADS").unwrap_or_else(|_| "default".into()),
        std::env::var("H2H_INSTALL").as_deref() == Ok("1"),
    );
    println!();

    let mut rng = StdRng::from_seed([7u8; 32]);

    for m in [16usize, 17, 18] {
        // Shapes exactly as both provers use them: witness has
        // ell = M-1 variables; hyrax split l = ell/2 rows-log.
        let ell = m - 1;
        let wlen = 1usize << ell;
        let l = ell / 2;
        let nrows = 1usize << l;
        let ncols = wlen / nrows;

        let w: Vec<Fr> = (0..wlen).map(|_| Fr::rand(&mut rng)).collect();

        // Zippel-side inputs (matching spartan.rs prover_create_inputs).
        let g_vec_proj: Vec<EdwardsProjective> =
            (0..ncols).map(|_| EdwardsProjective::rand(&mut rng)).collect();
        let g_vec: Vec<EdwardsAffine> = EdwardsProjective::normalize_batch(&g_vec_proj);
        let h_base = EdwardsProjective::rand(&mut rng);
        let r_rows: Vec<Fr> = (0..nrows).map(|_| Fr::rand(&mut rng)).collect();

        // Ark-spartan-side objects, built exactly as R1CSProof does.
        let gens = PolyCommitmentGens::<EdwardsProjective>::new(ell, b"h2h");
        let poly = DensePolynomial::new(w.clone());

        // H2H_ONLY=Z|ZPAR|S: run just one variant, so each can be
        // measured in its own process without cross-variant cache
        // warming (in the combined run, Z always ran first/cold —
        // an ordering confound worth eliminating).
        let only = std::env::var("H2H_ONLY").unwrap_or_default();

        let mut t_z = Vec::new();
        let mut t_zpar = Vec::new();
        let mut t_s = Vec::new();

        for rep in 0..=REPS {
            let run_z = only.is_empty() || only == "Z";
            let run_zpar = only.is_empty() || only == "ZPAR";
            let run_s = only.is_empty() || only == "S";
            if !run_z && !run_zpar && !run_s {
                panic!("H2H_ONLY must be Z, ZPAR, or S");
            }
            let _ = (run_z, run_zpar, run_s);
            // Z: zippel c_rows pattern (serial row loop, as the graph
            // evaluator runs it today).
            if run_z {
                let t = Instant::now();
                let mut acc = EdwardsProjective::zero();
                for i in 0..nrows {
                    let row = &w[i * ncols..(i + 1) * ncols];
                    let c = h_base * r_rows[i]
                        + EdwardsProjective::msm(&g_vec, row).expect("msm");
                    acc += c;
                }
                let dt = t.elapsed().as_secs_f64() * 1e3;
                std::hint::black_box(acc);
                if rep > 0 {
                    t_z.push(dt);
                }
            }

            // Z_par: identical work, rows via rayon par_iter — the same
            // construction ark's commit_inner uses. If this matches S
            // under RAYON_NUM_THREADS=1, the S advantage is rayon's
            // calling-thread participation (an effective 2nd core), not
            // anything about the MSM itself.
            if run_zpar {
                let t = Instant::now();
                let cs: Vec<EdwardsProjective> = (0..nrows)
                    .into_par_iter()
                    .map(|i| {
                        let row = &w[i * ncols..(i + 1) * ncols];
                        h_base * r_rows[i]
                            + EdwardsProjective::msm(&g_vec, row).expect("msm")
                    })
                    .collect();
                let dt = t.elapsed().as_secs_f64() * 1e3;
                std::hint::black_box(cs);
                if rep > 0 {
                    t_zpar.push(dt);
                }
            }

            // S: ark-spartan DensePolynomial::commit with a blinds tape,
            // exactly as R1CSProof::prove invokes it.
            if run_s {
                let t = Instant::now();
                let mut tape = RandomTape::<EdwardsProjective>::new(b"h2h_tape");
                let (comm, blinds) = poly.commit(&gens, Some(&mut tape));
                let dt = t.elapsed().as_secs_f64() * 1e3;
                std::hint::black_box((comm, blinds));
                if rep > 0 {
                    t_s.push(dt);
                }
            }
        }

        println!(
            "M={m}  (witness 2^{ell}, {nrows} rows x {ncols} cols)"
        );
        if !t_z.is_empty() {
            println!("  Z     (serial row loop)          : {:9.2} ms", mean_ms(&t_z));
        }
        if !t_zpar.is_empty() {
            println!("  Z_par (rows via par_iter)        : {:9.2} ms", mean_ms(&t_zpar));
        }
        if !t_s.is_empty() {
            println!("  S     (ark-spartan poly.commit)  : {:9.2} ms", mean_ms(&t_s));
        }
        if !t_z.is_empty() && !t_s.is_empty() {
            let (z, s) = (mean_ms(&t_z), mean_ms(&t_s));
            let zp = if t_zpar.is_empty() { f64::NAN } else { mean_ms(&t_zpar) };
            println!(
                "  Z vs S: {:+.2} ms ({:+.1}%)   Z_par vs S: {:+.2} ms ({:+.1}%)",
                z - s,
                (z - s) / s * 100.0,
                zp - s,
                (zp - s) / s * 100.0
            );
        }
        println!();
    }
}
