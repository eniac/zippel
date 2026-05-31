use benchmarks::sumcheck::{native_side, zippel_side};
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use std::time::Duration;

const NUM_VARS_GRID: &[usize] = &[10, 12, 14];
const MAX_DEGREE_GRID: &[usize] = &[2, 4, 8];

fn bench_sumcheck(c: &mut Criterion) {
    let mut group = c.benchmark_group("sumcheck");
    // Full protocol per iteration is expensive; trim sample count so a full
    // sweep finishes in a reasonable time. Bump back up for tighter CIs.
    group.sample_size(10);

    for &nv in NUM_VARS_GRID {
        for &md in MAX_DEGREE_GRID {
            let param = format!("nv{nv}_deg{md}");
            let mut z = zippel_side::Setup::new(nv, md);
            let n = native_side::Setup::new(nv, md);

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
            group.bench_with_input(BenchmarkId::new("hyperplonk_prove", &param), &(), |b, _| {
                b.iter_custom(|iters| {
                    let mut total = Duration::ZERO;
                    for _ in 0..iters {
                        total += n.time_protocol().prove;
                    }
                    total
                })
            });
            group.bench_with_input(
                BenchmarkId::new("hyperplonk_verify", &param),
                &(),
                |b, _| {
                    b.iter_custom(|iters| {
                        let mut total = Duration::ZERO;
                        for _ in 0..iters {
                            total += n.time_protocol().verify;
                        }
                        total
                    })
                },
            );
        }
    }

    group.finish();
}

criterion_group!(benches, bench_sumcheck);
criterion_main!(benches);
