//! Wall-clock timings of `compute_gb` over BLS12-381 Fr in degrevlex,
//! for katsura_n and cyclic_n with n in user-selected sizes.
//!
//! Usage:
//!
//! ```text
//! cargo run --release --example timing_grevlex -- katsura 3 4 5 6
//! cargo run --release --example timing_grevlex -- cyclic 4 5 6
//! ```
//!
//! For each (system, n) pair, runs `compute_gb` `iters` times (env
//! `ARK_GB_TIMING_ITERS`, default 1) and prints the per-run wall time
//! in milliseconds.

use std::env;
use std::sync::Arc;
use std::time::Instant;

use ark_bls12_381::Fr;
use ark_gb::compute_gb;
use ark_gb::monomial::GrevLexTerm;
use ark_gb::poly::Poly;
use ark_gb::ring::Ring;

#[path = "../benches/groebner_shared.rs"]
mod shared;
use shared::{cyclic_polys, grevlex_ring, katsura_polys};

fn time_one(label: &str, ring: &Arc<Ring<Fr>>, input: &[Poly<Fr, GrevLexTerm>], iters: usize) {
    let mut times_ms: Vec<f64> = Vec::with_capacity(iters);
    for _ in 0..iters {
        let r = Arc::clone(ring);
        let i = input.to_vec();
        let t0 = Instant::now();
        let gb = compute_gb(r, i);
        let dt = t0.elapsed().as_secs_f64() * 1000.0;
        times_ms.push(dt);
        // Print GB size on first iteration.
        if times_ms.len() == 1 {
            print!("{label:>14}  |G|={:>3}  ", gb.len());
        }
    }
    let mean = times_ms.iter().sum::<f64>() / times_ms.len() as f64;
    let min = times_ms.iter().cloned().fold(f64::INFINITY, f64::min);
    let max = times_ms.iter().cloned().fold(f64::NEG_INFINITY, f64::max);
    if iters == 1 {
        println!("time={mean:>10.2} ms");
    } else {
        println!("time mean={mean:>10.2} ms  min={min:>10.2}  max={max:>10.2}  (n={iters})");
    }
}

fn main() {
    let mut args = env::args().skip(1);
    let system = args
        .next()
        .expect("usage: timing_grevlex <katsura|cyclic> n1 n2 ...");
    let sizes: Vec<usize> = args
        .map(|s| s.parse().expect("size must be a positive integer"))
        .collect();
    let iters: usize = env::var("ARK_GB_TIMING_ITERS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(1);

    println!("# ark-gb compute_gb wall-clock timings (BLS12-381 Fr, degrevlex)");
    println!(
        "# threads = {} (RUSTGB_THREADS or rayon default)",
        env::var("RUSTGB_THREADS").unwrap_or_else(|_| "default".into())
    );
    println!("# iters per case = {iters}");
    println!();

    for n in sizes {
        let ring = grevlex_ring(n);
        match system.as_str() {
            "katsura" => {
                let input = katsura_polys::<GrevLexTerm>(&ring);
                time_one(&format!("katsura_{n}"), &ring, &input, iters);
            }
            "cyclic" => {
                let input = cyclic_polys::<GrevLexTerm>(&ring);
                time_one(&format!("cyclic_{n}"), &ring, &input, iters);
            }
            other => panic!("unknown system {other:?} (expected katsura|cyclic)"),
        }
    }
}
