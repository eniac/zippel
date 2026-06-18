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
//! The suite reports BOTH raw Buchberger (`gb_*`) and Buchberger-then-reduce
//! (`gb_*_reduced`). Published CAS timings (Singular/Maple/Magma) are for the
//! *reduced* Gröbner basis, so the `_reduced` variants are the right
//! comparison point against the literature; the raw variants are retained to
//! break out where time is spent (main loop vs inter-reduction).
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
//!   <https://github.com/Singular/Singular/blob/spielwiese/Singular/LIB/polylib.lib>
//!
//! We port only the algorithmic shape (loop structure) and the standard
//! mathematical definitions; we do not copy source. Correctness is
//! cross-checked against Sage's published small-n examples
//! (`sage.rings.ideal.Katsura` / `sage.rings.ideal.Cyclic`, see
//! `tests/groebner_sage.rs`).
//!
//! Run with: `cargo bench --bench groebner`
//! Filter  : `cargo bench --bench groebner gb_katsura_grevlex/3`

use std::time::Duration;

use analyses::groebner::{GrevLexTerm, GroebnerBasis, Monomial};
use analyses::knowledge::ElimTerm;
use ark_bls12_381::Fr;
use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};

#[path = "groebner_shared.rs"]
mod shared;
use shared::{
    CYCLIC_SIZES, KATSURA_ELIM_SIZES, KATSURA_GREVLEX_SIZES, cyclic_basis, katsura_basis,
};

// ---------------------------------------------------------------------------
// Criterion knobs.
// ---------------------------------------------------------------------------

const SAMPLE_SIZE: usize = 10;
const MEASUREMENT_TIME: Duration = Duration::from_secs(30);

// ---------------------------------------------------------------------------
// Generic helpers — one per measurement kind.
// ---------------------------------------------------------------------------

/// Time `buchberger()` on bases produced by `build(n)` for each `n` in `sizes`.
/// Uses `iter_batched` so the per-iter `.clone()` (Buchberger consumes `self`)
/// is excluded from the measurement.
fn bench_buchberger<T: Monomial, F>(c: &mut Criterion, group_name: &str, sizes: &[usize], build: F)
where
    F: Fn(usize) -> GroebnerBasis<Fr, T>,
{
    let mut group = c.benchmark_group(group_name);
    group.sample_size(SAMPLE_SIZE);
    group.measurement_time(MEASUREMENT_TIME);
    for &n in sizes {
        let sys = build(n);
        group.bench_with_input(BenchmarkId::from_parameter(n), &sys, |b, sys| {
            b.iter_batched(
                || sys.clone(),
                |s| s.buchberger::<8>(),
                BatchSize::SmallInput,
            )
        });
    }
    group.finish();
}

/// Time `buchberger_and_reduce()` — the *reduced* Gröbner basis, which is
/// what Singular/Maple/Magma benchmarks report. Always ≥ the corresponding
/// raw `bench_buchberger` time (interreduction is non-negative work).
fn bench_buchberger_reduced<T: Monomial, F>(
    c: &mut Criterion,
    group_name: &str,
    sizes: &[usize],
    build: F,
) where
    F: Fn(usize) -> GroebnerBasis<Fr, T>,
{
    let mut group = c.benchmark_group(group_name);
    group.sample_size(SAMPLE_SIZE);
    group.measurement_time(MEASUREMENT_TIME);
    for &n in sizes {
        let sys = build(n);
        group.bench_with_input(BenchmarkId::from_parameter(n), &sys, |b, sys| {
            b.iter_batched(
                || sys.clone(),
                |s| s.buchberger_and_reduce::<8>(),
                BatchSize::SmallInput,
            )
        });
    }
    group.finish();
}

/// Time `contains(&input)` for each `n` in `sizes`. Pre-computes the reduced
/// Gröbner basis once outside the iter loop; each iter reduces every input
/// generator modulo that basis (exercising `contains_poly`).
fn bench_inclusion<T: Monomial, F>(c: &mut Criterion, group_name: &str, sizes: &[usize], build: F)
where
    F: Fn(usize) -> GroebnerBasis<Fr, T>,
{
    let mut group = c.benchmark_group(group_name);
    group.sample_size(SAMPLE_SIZE);
    group.measurement_time(MEASUREMENT_TIME);
    for &n in sizes {
        let input = build(n);
        let g = input.clone().buchberger::<8>();
        group.bench_with_input(BenchmarkId::from_parameter(n), &(g, input), |b, (g, i)| {
            b.iter(|| g.contains(i))
        });
    }
    group.finish();
}

// ---------------------------------------------------------------------------
// Bench entry points — one line of wiring per (family × kind).
// ---------------------------------------------------------------------------

fn bench_gb_katsura_elim(c: &mut Criterion) {
    bench_buchberger(
        c,
        "gb_katsura_elim",
        KATSURA_ELIM_SIZES,
        katsura_basis::<ElimTerm>,
    );
}

fn bench_gb_katsura_grevlex(c: &mut Criterion) {
    bench_buchberger(
        c,
        "gb_katsura_grevlex",
        KATSURA_GREVLEX_SIZES,
        katsura_basis::<GrevLexTerm>,
    );
}

fn bench_gb_cyclic_elim(c: &mut Criterion) {
    bench_buchberger(c, "gb_cyclic_elim", CYCLIC_SIZES, cyclic_basis::<ElimTerm>);
}

fn bench_gb_cyclic_grevlex(c: &mut Criterion) {
    bench_buchberger(
        c,
        "gb_cyclic_grevlex",
        CYCLIC_SIZES,
        cyclic_basis::<GrevLexTerm>,
    );
}

fn bench_gb_katsura_elim_reduced(c: &mut Criterion) {
    bench_buchberger_reduced(
        c,
        "gb_katsura_elim_reduced",
        KATSURA_ELIM_SIZES,
        katsura_basis::<ElimTerm>,
    );
}

fn bench_gb_katsura_grevlex_reduced(c: &mut Criterion) {
    bench_buchberger_reduced(
        c,
        "gb_katsura_grevlex_reduced",
        KATSURA_GREVLEX_SIZES,
        katsura_basis::<GrevLexTerm>,
    );
}

fn bench_gb_cyclic_elim_reduced(c: &mut Criterion) {
    bench_buchberger_reduced(
        c,
        "gb_cyclic_elim_reduced",
        CYCLIC_SIZES,
        cyclic_basis::<ElimTerm>,
    );
}

fn bench_gb_cyclic_grevlex_reduced(c: &mut Criterion) {
    bench_buchberger_reduced(
        c,
        "gb_cyclic_grevlex_reduced",
        CYCLIC_SIZES,
        cyclic_basis::<GrevLexTerm>,
    );
}

fn bench_gb_inclusion_katsura(c: &mut Criterion) {
    bench_inclusion(
        c,
        "gb_inclusion_katsura",
        KATSURA_GREVLEX_SIZES,
        katsura_basis::<GrevLexTerm>,
    );
}

fn bench_gb_inclusion_cyclic(c: &mut Criterion) {
    bench_inclusion(
        c,
        "gb_inclusion_cyclic",
        CYCLIC_SIZES,
        cyclic_basis::<GrevLexTerm>,
    );
}

criterion_group!(
    benches,
    bench_gb_katsura_elim,
    bench_gb_katsura_grevlex,
    bench_gb_cyclic_elim,
    bench_gb_cyclic_grevlex,
    bench_gb_katsura_elim_reduced,
    bench_gb_katsura_grevlex_reduced,
    bench_gb_cyclic_elim_reduced,
    bench_gb_cyclic_grevlex_reduced,
    bench_gb_inclusion_katsura,
    bench_gb_inclusion_cyclic,
);
criterion_main!(benches);
