//! Long-running cyclic-5 driver, suitable for `perf record`.
//!
//! Runs cyclic-5 over the BLS12-381 scalar field N times (default 200)
//! under whatever RUSTGB_THREADS value the environment carries. Prints
//! the mean and stdev of per-iteration wall time.

use std::sync::Arc;
use std::time::Instant;

use ark_bls12_381::Fr;
use ark_ff::One;
use ark_gb::compute_gb;
use ark_gb::monomial::{GrevLexTerm, MonoTerm};
use ark_gb::poly::Poly;
use ark_gb::ring::Ring;

fn mk_ring(nvars: u32) -> Arc<Ring<Fr>> {
    Arc::new(Ring::<Fr>::new(nvars).unwrap())
}

fn mono(r: &Ring<Fr>, e: &[u32]) -> GrevLexTerm {
    GrevLexTerm::from(MonoTerm::from_exponents(r, e).unwrap())
}

fn cyclic5_input(ring: &Arc<Ring<Fr>>) -> Vec<Poly<Fr, GrevLexTerm>> {
    let m = |e: &[u32]| mono(ring, e);
    let one = Fr::one();
    let neg_one = -Fr::one();
    vec![
        Poly::from_terms(
            ring,
            vec![
                (one, m(&[1, 0, 0, 0, 0])),
                (one, m(&[0, 1, 0, 0, 0])),
                (one, m(&[0, 0, 1, 0, 0])),
                (one, m(&[0, 0, 0, 1, 0])),
                (one, m(&[0, 0, 0, 0, 1])),
            ],
        ),
        Poly::from_terms(
            ring,
            vec![
                (one, m(&[1, 1, 0, 0, 0])),
                (one, m(&[0, 1, 1, 0, 0])),
                (one, m(&[0, 0, 1, 1, 0])),
                (one, m(&[0, 0, 0, 1, 1])),
                (one, m(&[1, 0, 0, 0, 1])),
            ],
        ),
        Poly::from_terms(
            ring,
            vec![
                (one, m(&[1, 1, 1, 0, 0])),
                (one, m(&[0, 1, 1, 1, 0])),
                (one, m(&[0, 0, 1, 1, 1])),
                (one, m(&[1, 0, 0, 1, 1])),
                (one, m(&[1, 1, 0, 0, 1])),
            ],
        ),
        Poly::from_terms(
            ring,
            vec![
                (one, m(&[1, 1, 1, 1, 0])),
                (one, m(&[0, 1, 1, 1, 1])),
                (one, m(&[1, 0, 1, 1, 1])),
                (one, m(&[1, 1, 0, 1, 1])),
                (one, m(&[1, 1, 1, 0, 1])),
            ],
        ),
        Poly::from_terms(
            ring,
            vec![(one, m(&[1, 1, 1, 1, 1])), (neg_one, m(&[0, 0, 0, 0, 0]))],
        ),
    ]
}

fn main() {
    let n_iter: usize = std::env::var("PERF_ITER")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(200);
    let r = mk_ring(5);
    // Warm-up
    let _ = compute_gb(Arc::clone(&r), cyclic5_input(&r));

    let mut times_us: Vec<u64> = Vec::with_capacity(n_iter);
    for _ in 0..n_iter {
        let input = cyclic5_input(&r);
        let t = Instant::now();
        let gb = compute_gb(Arc::clone(&r), input);
        let elapsed = t.elapsed();
        std::hint::black_box(gb);
        times_us.push(elapsed.as_micros() as u64);
    }
    let sum: u64 = times_us.iter().sum();
    let n = times_us.len() as f64;
    let mean = sum as f64 / n;
    let var = times_us
        .iter()
        .map(|&t| {
            let d = t as f64 - mean;
            d * d
        })
        .sum::<f64>()
        / n;
    let stdev = var.sqrt();
    let mut sorted = times_us.clone();
    sorted.sort_unstable();
    let median = sorted[sorted.len() / 2];
    let min = sorted[0];
    println!(
        "cyclic-5 (N={}): mean={:.1}us stdev={:.1}us median={}us min={}us",
        n_iter, mean, stdev, median, min
    );
}
