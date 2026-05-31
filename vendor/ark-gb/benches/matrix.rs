//! Criterion benchmarks for `ark_gb::matrix` (Phase L).
//!
//! Records absolute throughput of the sparse Gaussian eliminator on
//! representative shapes over `ark_bls12_381::Fr`. Phase L only *adds*
//! code, so there is no prior baseline — these numbers establish the
//! reference line `after-l-matrix` referenced from ADR-022.

use std::time::Duration;

use ark_bls12_381::Fr;
use ark_ff::{UniformRand, Zero};
use ark_gb::matrix::{SparseRow, row_echelon, rref};
use ark_std::rand::{SeedableRng, rngs::StdRng};
use criterion::{BatchSize, Criterion, criterion_group, criterion_main};

const SAMPLE_SIZE: usize = 10;
const MEASUREMENT_TIME: Duration = Duration::from_secs(15);

/// Generate a random matrix as `Vec<SparseRow<Fr>>` of shape
/// `rows × cols`, with each entry independently non-zero with
/// probability `1/density_q`.
fn random_rows(rows: usize, cols: usize, density_q: u32, seed: u64) -> Vec<SparseRow<Fr>> {
    let mut rng = StdRng::seed_from_u64(seed);
    (0..rows)
        .map(|_| {
            let dense: Vec<Fr> = (0..cols)
                .map(|_| {
                    if u32::rand(&mut rng) % density_q == 0 {
                        Fr::rand(&mut rng)
                    } else {
                        Fr::zero()
                    }
                })
                .collect();
            SparseRow::from_dense(&dense)
        })
        .collect()
}

fn bench_shape(c: &mut Criterion, name: &str, rows: usize, cols: usize, density_q: u32, seed: u64) {
    let mut group = c.benchmark_group(name);
    group.sample_size(SAMPLE_SIZE);
    group.measurement_time(MEASUREMENT_TIME);

    let template = random_rows(rows, cols, density_q, seed);

    group.bench_function("row_echelon", |b| {
        b.iter_batched_ref(
            || template.clone(),
            |rs| row_echelon(rs.as_mut_slice()),
            BatchSize::LargeInput,
        )
    });
    group.bench_function("rref", |b| {
        b.iter_batched_ref(
            || template.clone(),
            |rs| rref(rs.as_mut_slice()),
            BatchSize::LargeInput,
        )
    });
    group.finish();
}

fn bench_matrix(c: &mut Criterion) {
    // Roughly 1/3 dense (fits in L2 cache, exercises the hot path).
    bench_shape(c, "matrix/square_100_d3", 100, 100, 3, 0x100);
    // 1 % dense, larger — the F4-relevant regime.
    bench_shape(c, "matrix/square_500_d100", 500, 500, 100, 0x500);
    // Tall-thin (more rows than cols → many redundancies).
    bench_shape(c, "matrix/tall_500x100_d10", 500, 100, 10, 0x511);
    // Wide-flat (more cols than rows → low rank).
    bench_shape(c, "matrix/wide_100x500_d10", 100, 500, 10, 0x515);
    // Sparse 1 % at 1000×1000.
    bench_shape(c, "matrix/sparse_1pct_1000", 1000, 1000, 100, 0x1000);
    // Sparse 5 % at 1000×1000 (density a touch above realistic F4).
    bench_shape(c, "matrix/sparse_5pct_1000", 1000, 1000, 20, 0x1005);
}

criterion_group!(benches, bench_matrix);
criterion_main!(benches);
