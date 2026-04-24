//! Criterion benchmarks for the Gröbner basis analysis.
//!
//! Measures Buchberger's algorithm under two monomial orderings (elimination
//! and graded reverse-lex) and ideal inclusion (basis containment via
//! [`GroebnerBasis::contains`]) on the two canonical polynomial-system
//! families used by SymbolicData (SD) and the wider CAS ecosystem:
//!
//!   * **Katsura-n** — symmetric system from non-linear wave physics.
//!   * **Cyclic-n**  — cyclic-roots system.
//!
//! # Source of generators
//!
//! The Katsura / Cyclic generators (in `groebner_shared.rs`) are direct ports
//! of the Singular `polylib.lib` procedures that Sage, Macaulay2, and the SD
//! tools (`sdsage`) all invoke via `singular.katsura(n)` / `singular.cyclic(n)`:
//!
//!   * `proc cyclic(int n)`         — polylib.lib line 159
//!   * `proc katsura`               — polylib.lib line 249
//!   * `proc kat_var(int i, int n)` — polylib.lib line 310
//!
//! Upstream reference:
//!   https://github.com/Singular/Singular/blob/spielwiese/Singular/LIB/polylib.lib
//!
//! We port only the algorithmic shape (loop structure) and the standard
//! mathematical definitions; we do not copy source. Correctness is
//! cross-checked against Sage's published small-n examples
//! (`sage.rings.ideal.Katsura` / `sage.rings.ideal.Cyclic`, see
//! `tests/groebner_sage.rs`).
//!
//! Run with: `cargo bench --bench groebner`
//!
//! Note on sizes: Buchberger under ElimTerm on Katsura-5 / Cyclic-5 can take
//! many minutes in debug builds. Filter with e.g.
//! `cargo bench --bench groebner -- gb_katsura_grevlex/3`.

use std::time::Duration;

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use graph::analyses::groebner::{ElimTerm, GrevLexTerm};

#[path = "groebner_shared.rs"]
mod shared;
use shared::{cyclic_basis, katsura_basis};

/// Katsura-n sizes under GrevLex / inclusion (all manageable at release).
const KATSURA_SIZES: &[usize] = &[3, 4, 5];
/// Katsura-n sizes under ElimTerm. Katsura-5 lex is intractable for our
/// pure-Rust Buchberger (multi-hour); cap at 4.
const KATSURA_ELIM_SIZES: &[usize] = &[3, 4];
/// Cyclic-n sizes under GrevLex / inclusion. Cyclic-5 is the classic
/// SymbolicData hard case — intractable even under GrevLex for our
/// implementation — so we cap at 4.
const CYCLIC_SIZES: &[usize] = &[4];
/// Cyclic-n sizes under ElimTerm (same cap as GrevLex).
const CYCLIC_ELIM_SIZES: &[usize] = &[4];

fn bench_gb_katsura_elim(c: &mut Criterion) {
    let mut group = c.benchmark_group("gb_katsura_elim");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(30));
    for &n in KATSURA_ELIM_SIZES {
        let sys = katsura_basis::<ElimTerm>(n);
        group.bench_with_input(BenchmarkId::from_parameter(n), &sys, |b, sys| {
            b.iter(|| sys.clone().buchberger())
        });
    }
    group.finish();
}

fn bench_gb_katsura_grevlex(c: &mut Criterion) {
    let mut group = c.benchmark_group("gb_katsura_grevlex");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(30));
    for &n in KATSURA_SIZES {
        let sys = katsura_basis::<GrevLexTerm>(n);
        group.bench_with_input(BenchmarkId::from_parameter(n), &sys, |b, sys| {
            b.iter(|| sys.clone().buchberger())
        });
    }
    group.finish();
}

fn bench_gb_cyclic_elim(c: &mut Criterion) {
    let mut group = c.benchmark_group("gb_cyclic_elim");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(30));
    for &n in CYCLIC_ELIM_SIZES {
        let sys = cyclic_basis::<ElimTerm>(n);
        group.bench_with_input(BenchmarkId::from_parameter(n), &sys, |b, sys| {
            b.iter(|| sys.clone().buchberger())
        });
    }
    group.finish();
}

fn bench_gb_cyclic_grevlex(c: &mut Criterion) {
    let mut group = c.benchmark_group("gb_cyclic_grevlex");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(30));
    for &n in CYCLIC_SIZES {
        let sys = cyclic_basis::<GrevLexTerm>(n);
        group.bench_with_input(BenchmarkId::from_parameter(n), &sys, |b, sys| {
            b.iter(|| sys.clone().buchberger())
        });
    }
    group.finish();
}

/// Inclusion (basis containment): given a computed Gröbner basis `g` and the
/// original ideal generators `input`, time `g.contains(&input)` (each input
/// generator is reduced modulo `g` and must reduce to zero). This exercises
/// the same `contains_poly` / reduction path Zippel's analysis uses for ideal
/// membership. GrevLex order so the `buchberger()` pre-computation stays
/// cheap relative to the contains call.
fn bench_gb_inclusion_katsura(c: &mut Criterion) {
    let mut group = c.benchmark_group("gb_inclusion_katsura");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(30));
    for &n in KATSURA_SIZES {
        let input = katsura_basis::<GrevLexTerm>(n);
        let g = input.clone().buchberger();
        group.bench_with_input(BenchmarkId::from_parameter(n), &(g, input), |b, (g, i)| {
            b.iter(|| g.contains(i))
        });
    }
    group.finish();
}

fn bench_gb_inclusion_cyclic(c: &mut Criterion) {
    let mut group = c.benchmark_group("gb_inclusion_cyclic");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(30));
    for &n in CYCLIC_SIZES {
        let input = cyclic_basis::<GrevLexTerm>(n);
        let g = input.clone().buchberger();
        group.bench_with_input(BenchmarkId::from_parameter(n), &(g, input), |b, (g, i)| {
            b.iter(|| g.contains(i))
        });
    }
    group.finish();
}

criterion_group!(
    benches,
    bench_gb_katsura_elim,
    bench_gb_katsura_grevlex,
    bench_gb_cyclic_elim,
    bench_gb_cyclic_grevlex,
    bench_gb_inclusion_katsura,
    bench_gb_inclusion_cyclic,
);
criterion_main!(benches);
