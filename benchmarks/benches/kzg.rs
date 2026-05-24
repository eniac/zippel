use benchmarks::kzg::{native_side, zippel_side};
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use std::time::Duration;

const N_GRID: &[usize] = &[4, 16, 64, 256];

fn bench_kzg(c: &mut Criterion) {
    let mut group = c.benchmark_group("kzg");
    group.sample_size(10);

    for &n in N_GRID {
        let param = format!("n{n}");
        let mut z = zippel_side::Setup::new(n);
        let np = native_side::Setup::new(n);

        group.bench_with_input(BenchmarkId::new("zippel_prove", &param), &(), |b, _| {
            b.iter_custom(|iters| {
                let mut total = Duration::ZERO;
                for _ in 0..iters {
                    total += z.time_protocol().prove;
                }
                total
            })
        });
        group.bench_with_input(BenchmarkId::new("zippel_verify", &param), &(), |b, _| {
            b.iter_custom(|iters| {
                let mut total = Duration::ZERO;
                for _ in 0..iters {
                    total += z.time_protocol().verify;
                }
                total
            })
        });
        group.bench_with_input(BenchmarkId::new("polycommit_prove", &param), &(), |b, _| {
            b.iter_custom(|iters| {
                let mut total = Duration::ZERO;
                for _ in 0..iters {
                    total += np.time_protocol().prove;
                }
                total
            })
        });
        group.bench_with_input(BenchmarkId::new("polycommit_verify", &param), &(), |b, _| {
            b.iter_custom(|iters| {
                let mut total = Duration::ZERO;
                for _ in 0..iters {
                    total += np.time_protocol().verify;
                }
                total
            })
        });
    }

    group.finish();
}

criterion_group!(benches, bench_kzg);
criterion_main!(benches);
