use benchmarks::kzg::{native_side, zippel_side};
use criterion::{BenchmarkId, Criterion, criterion_group};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::time::Duration;

const N_GRID: &[usize] = &[4, 16, 64, 256];

fn time_kzg_arm<F>(n: usize, arm: &'static str, f: F) -> Duration
where
    F: FnOnce() -> Duration,
{
    catch_unwind(AssertUnwindSafe(f)).unwrap_or_else(|payload| {
        let message = if let Some(message) = payload.downcast_ref::<&str>() {
            *message
        } else if let Some(message) = payload.downcast_ref::<String>() {
            message.as_str()
        } else {
            "non-string panic payload"
        };
        panic!("kzg benchmark arm failed (n={n}, arm={arm}): {message}");
    })
}

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
                    total += time_kzg_arm(n, "zippel_prove", || z.time_protocol().prove);
                }
                total
            })
        });
        group.bench_with_input(BenchmarkId::new("zippel_verify", &param), &(), |b, _| {
            b.iter_custom(|iters| {
                let mut total = Duration::ZERO;
                for _ in 0..iters {
                    total += time_kzg_arm(n, "zippel_verify", || z.time_protocol().verify);
                }
                total
            })
        });
        group.bench_with_input(BenchmarkId::new("polycommit_prove", &param), &(), |b, _| {
            b.iter_custom(|iters| {
                let mut total = Duration::ZERO;
                for _ in 0..iters {
                    total += time_kzg_arm(n, "polycommit_prove", || np.time_protocol().prove);
                }
                total
            })
        });
        group.bench_with_input(
            BenchmarkId::new("polycommit_verify", &param),
            &(),
            |b, _| {
                b.iter_custom(|iters| {
                    let mut total = Duration::ZERO;
                    for _ in 0..iters {
                        total +=
                            time_kzg_arm(n, "polycommit_verify", || np.time_protocol().verify);
                    }
                    total
                })
            },
        );
    }

    group.finish();
}

fn running_under_cargo_test() -> bool {
    cfg!(debug_assertions)
        || std::env::args_os().skip(1).any(|arg| {
            matches!(
                arg.to_str(),
                Some(
                    "--nocapture"
                        | "--list"
                        | "--ignored"
                        | "--include-ignored"
                        | "--test"
                        | "--exact"
                )
            ) || arg.to_str().is_some_and(|s| s.starts_with("--format"))
        })
}

criterion_group!(benches, bench_kzg);

fn main() {
    if running_under_cargo_test() {
        eprintln!(
            "skipping kzg Criterion benchmark under cargo test/debug invocation; \
             run `cargo bench --manifest-path benchmarks/Cargo.toml --bench kzg` for full timing"
        );
        return;
    }

    benches();
}
