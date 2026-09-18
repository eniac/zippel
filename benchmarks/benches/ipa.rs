//! Criterion sweep for the Bulletproofs inner-product argument on Secp256k1:
//! the zippel-compiled protocol against the vendored port of
//! `Bp2aryStep` (BCC/BBB+18 Protocol 2).
//!
//! `S` is the folding parameter; the committed vectors have length `2^S`.
//! Computing the initial commitment `P` is setup, not protocol, so it stays
//! outside the timed region on both sides. Timing goes through
//! `Setup::time_protocol`, which splits prove from verify, so the benches use
//! `iter_custom`.

#![allow(
    missing_docs,
    reason = "criterion_group! synthesises an undocumentable `pub fn benches`"
)]

use benchmarks::ipa::{native_side, zippel_side};
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use std::time::Duration;

const S_GRID: &[usize] = &[4, 6, 8];

fn bench_ipa(c: &mut Criterion) {
    let mut group = c.benchmark_group("ipa");
    group.sample_size(10);

    for &s in S_GRID {
        let n = 1usize << s;
        let param = format!("s{s}_n{n}");
        let mut z = zippel_side::Setup::new(s);
        let np = native_side::Setup::new(s);

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
        group.bench_with_input(
            BenchmarkId::new("polycommit_verify", &param),
            &(),
            |b, _| {
                b.iter_custom(|iters| {
                    let mut total = Duration::ZERO;
                    for _ in 0..iters {
                        total += np.time_protocol().verify;
                    }
                    total
                })
            },
        );
    }

    group.finish();
}

criterion_group!(benches, bench_ipa);
criterion_main!(benches);
