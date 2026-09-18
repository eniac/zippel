//! Criterion benchmark for `fmt::format_source`, the whole parse →
//! pretty-print round trip of the `zippel-fmt` formatter.
//!
//! Three real `.zippel` sources from `examples/` stand in for the size range
//! the formatter sees in practice: `schnorr` (7 lines), `dory` (301), and
//! `spartan` (590). They are embedded with `include_str!`, so file I/O never
//! enters a measured number.

#![allow(
    missing_docs,
    reason = "criterion_group! synthesises an undocumentable `pub fn benches`"
)]

use criterion::{Criterion, criterion_group, criterion_main};
use fmt::format_source;

fn bench_format(c: &mut Criterion) {
    let small = include_str!("../../examples/schnorr/schnorr.zippel");
    let medium = include_str!("../../examples/dory/dory.zippel");
    let large = include_str!("../../examples/spartan/spartan.zippel");

    c.bench_function("small_7lines", |b| b.iter(|| format_source(small).unwrap()));
    c.bench_function("medium_301lines", |b| {
        b.iter(|| format_source(medium).unwrap())
    });
    c.bench_function("large_590lines", |b| {
        b.iter(|| format_source(large).unwrap())
    });
}

criterion_group!(benches, bench_format);
criterion_main!(benches);
