//! Criterion benchmarks for `ark_gb::compute_gb`.

use std::sync::Arc;
use std::time::Duration;

use ark_bls12_381::Fr;
use ark_gb::bba::compute_gb_serial;
use ark_gb::monomial::{GrevLexTerm, MonoTerm, Monomial, OddElimTerm};
use ark_gb::poly::Poly;
use ark_gb::ring::Ring;
use ark_gb::validate::is_groebner_basis;
use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};

#[path = "groebner_shared.rs"]
mod shared;
use shared::{
    CYCLIC_SIZES, KATSURA_ELIM_SIZES, KATSURA_GREVLEX_SIZES, cyclic_polys, elim_ring, grevlex_ring,
    katsura_polys,
};

const SAMPLE_SIZE: usize = 10;
const MEASUREMENT_TIME: Duration = Duration::from_secs(30);

fn bench_compute_gb<M: Monomial<Fr> + From<MonoTerm> + 'static>(
    c: &mut Criterion,
    group_name: &str,
    sizes: &[usize],
    ring_builder: fn(usize) -> Arc<Ring<Fr>>,
    input_builder: fn(&Ring<Fr>) -> Vec<Poly<Fr, M>>,
) {
    let mut group = c.benchmark_group(group_name);
    group.sample_size(SAMPLE_SIZE);
    group.measurement_time(MEASUREMENT_TIME);
    for &n in sizes {
        let ring = ring_builder(n);
        let input = input_builder(&ring);
        group.bench_with_input(
            BenchmarkId::from_parameter(n),
            &(ring, input),
            |b, (ring, input)| {
                b.iter_batched(
                    || (Arc::clone(ring), input.clone()),
                    |(r, i)| compute_gb_serial(r, i),
                    BatchSize::SmallInput,
                )
            },
        );
    }
    group.finish();
}

fn bench_validation<M: Monomial<Fr> + From<MonoTerm> + 'static>(
    c: &mut Criterion,
    group_name: &str,
    sizes: &[usize],
    ring_builder: fn(usize) -> Arc<Ring<Fr>>,
    input_builder: fn(&Ring<Fr>) -> Vec<Poly<Fr, M>>,
) {
    let mut group = c.benchmark_group(group_name);
    group.sample_size(SAMPLE_SIZE);
    group.measurement_time(MEASUREMENT_TIME);
    for &n in sizes {
        let ring = ring_builder(n);
        let input = input_builder(&ring);
        let gb = compute_gb_serial(Arc::clone(&ring), input.clone());
        group.bench_with_input(
            BenchmarkId::from_parameter(n),
            &(ring, input, gb),
            |b, (ring, input, gb)| b.iter(|| is_groebner_basis(ring, input, gb).is_ok()),
        );
    }
    group.finish();
}

fn bench_gb_katsura_elim(c: &mut Criterion) {
    bench_compute_gb::<OddElimTerm>(
        c,
        "gb_katsura_elim",
        KATSURA_ELIM_SIZES,
        elim_ring,
        katsura_polys,
    );
}

fn bench_gb_katsura_grevlex(c: &mut Criterion) {
    bench_compute_gb::<GrevLexTerm>(
        c,
        "gb_katsura_grevlex",
        KATSURA_GREVLEX_SIZES,
        grevlex_ring,
        katsura_polys,
    );
}

fn bench_gb_cyclic_elim(c: &mut Criterion) {
    bench_compute_gb::<OddElimTerm>(c, "gb_cyclic_elim", CYCLIC_SIZES, elim_ring, cyclic_polys);
}

fn bench_gb_cyclic_grevlex(c: &mut Criterion) {
    bench_compute_gb::<GrevLexTerm>(
        c,
        "gb_cyclic_grevlex",
        CYCLIC_SIZES,
        grevlex_ring,
        cyclic_polys,
    );
}

fn bench_gb_validate_katsura(c: &mut Criterion) {
    bench_validation::<GrevLexTerm>(
        c,
        "gb_validate_katsura",
        KATSURA_GREVLEX_SIZES,
        grevlex_ring,
        katsura_polys,
    );
}

fn bench_gb_validate_cyclic(c: &mut Criterion) {
    bench_validation::<GrevLexTerm>(
        c,
        "gb_validate_cyclic",
        CYCLIC_SIZES,
        grevlex_ring,
        cyclic_polys,
    );
}

criterion_group!(
    benches,
    bench_gb_katsura_elim,
    bench_gb_katsura_grevlex,
    bench_gb_cyclic_elim,
    bench_gb_cyclic_grevlex,
    bench_gb_validate_katsura,
    bench_gb_validate_cyclic,
);
criterion_main!(benches);
