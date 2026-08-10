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
