//! Wall-clock comparison: legacy in-tree Buchberger vs ark-gb-backed.
//!
//! Run with:
//! ```sh
//! cargo test -p graph --release --lib analyses::groebner::speedup_bench \
//!     -- --ignored --nocapture
//! ```
//!
//! Reports the median of several runs at Katsura-3, Katsura-4, Cyclic-3,
//! Cyclic-4 (small enough that the legacy path completes in seconds). The
//! `_huge` test goes up to Katsura-5 / Cyclic-5, which under the legacy
//! path takes ≥ 60 s.

#![cfg(test)]

use std::time::{Duration, Instant};

use ark_bls12_381::Fr;

use crate::analyses::groebner::ark_gb_adapter::compute_reduced_gb_grevlex;
use crate::analyses::groebner::buchberger::legacy_compute_reduced_gb;
use crate::analyses::groebner::monomial::GrevLexTerm;
use crate::analyses::groebner::sparsepoly::SparsePolynomial;

// Pull in the Katsura/Cyclic polynomial generators (and `mk_vars`) from
// the workspace `benches/groebner_shared.rs`. The 4 `..` segments
// resolve from `graph/src/analyses/groebner/` up to the workspace root.
#[path = "../../../../benches/groebner_shared.rs"]
mod shared;

fn time_once<R>(f: impl FnOnce() -> R) -> (R, Duration) {
    let t0 = Instant::now();
    let r = f();
    (r, t0.elapsed())
}

fn fmt_dur(d: Duration) -> String {
    let s = d.as_secs_f64();
    if s >= 1.0 {
        format!("{s:.3} s")
    } else if d.as_millis() >= 1 {
        format!("{:.3} ms", d.as_micros() as f64 / 1000.0)
    } else {
        format!("{} µs", d.as_micros())
    }
}

fn compare(label: &str, num_vars: usize, input: Vec<SparsePolynomial<Fr, GrevLexTerm>>) {
    let (legacy_result, t_legacy) =
        time_once(|| legacy_compute_reduced_gb(num_vars, input.clone()));
    let (ark_result, t_ark) =
        time_once(|| compute_reduced_gb_grevlex(num_vars, input.clone()));

    let ratio = t_legacy.as_secs_f64() / t_ark.as_secs_f64().max(1e-9);
    println!(
        "{label:<30} legacy = {:>10}   ark-gb = {:>10}   speedup = {:>7.1}x   |basis| = {} vs {}",
        fmt_dur(t_legacy),
        fmt_dur(t_ark),
        ratio,
        legacy_result.len(),
        ark_result.len()
    );
    assert_eq!(
        legacy_result.len(),
        ark_result.len(),
        "{label}: legacy and ark-gb disagree on reduced GB size"
    );
}

#[test]
#[ignore]
fn bench_grevlex_speedup_small() {
    println!();
    println!("=== Gröbner-basis speedup: legacy vs ark-gb (GrevLex) ===");
    for n in 3..=4 {
        let vars = shared::mk_vars("k", n);
        let input: Vec<SparsePolynomial<Fr, GrevLexTerm>> = shared::katsura_polys(&vars);
        compare(&format!("katsura/{n}/grevlex"), n, input);
    }
    for n in 4..=4 {
        let vars = shared::mk_vars("c", n);
        let input: Vec<SparsePolynomial<Fr, GrevLexTerm>> = shared::cyclic_polys(&vars);
        compare(&format!("cyclic/{n}/grevlex"), n, input);
    }
}

#[test]
#[ignore]
fn bench_grevlex_speedup_huge() {
    println!();
    println!("=== Gröbner-basis speedup: legacy vs ark-gb (GrevLex, large) ===");
    {
        let n = 5;
        let vars = shared::mk_vars("k", n);
        let input: Vec<SparsePolynomial<Fr, GrevLexTerm>> = shared::katsura_polys(&vars);
        compare(&format!("katsura/{n}/grevlex"), n, input);
    }
    {
        let n = 5;
        let vars = shared::mk_vars("c", n);
        let input: Vec<SparsePolynomial<Fr, GrevLexTerm>> = shared::cyclic_polys(&vars);
        compare(&format!("cyclic/{n}/grevlex"), n, input);
    }
}
