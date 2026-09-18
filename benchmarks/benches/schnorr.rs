//! Criterion comparison for the Schnorr identification protocol: the
//! zippel-compiled prover and verifier against `ark-crypto-primitives`'
//! native `Schnorr` signature scheme.
//!
//! Schnorr has no size knob, so this is a single fixed point rather than a
//! sweep. Both sides are sub-millisecond, hence the raised sample count.
//! Timing goes through `Setup::time_protocol`, which splits prove from
//! verify, so the benches use `iter_custom`.

#![allow(
    missing_docs,
    reason = "criterion_group! synthesises an undocumentable `pub fn benches`"
)]

use benchmarks::schnorr::{native_side, zippel_side};
use criterion::{Criterion, criterion_group, criterion_main};
use std::time::Duration;

fn bench_schnorr(c: &mut Criterion) {
    let mut group = c.benchmark_group("schnorr");
    // Schnorr is fast (sub-millisecond on both sides); criterion's default
    // sample size is fine, but allow a slightly larger one for tighter CIs
    // on the very-short verify timings.
    group.sample_size(50);

    let mut z = zippel_side::Setup::new();
    group.bench_function("zippel_prove", |b| {
        b.iter_custom(|iters| {
            let mut total = Duration::ZERO;
            for _ in 0..iters {
                total += z.time_protocol().prove;
            }
            total
        })
    });
    group.bench_function("zippel_verify", |b| {
        b.iter_custom(|iters| {
            let mut total = Duration::ZERO;
            for _ in 0..iters {
                total += z.time_protocol().verify;
            }
            total
        })
    });

    let n = native_side::Setup::new();
    group.bench_function("arkcp_prove", |b| {
        b.iter_custom(|iters| {
            let mut total = Duration::ZERO;
            for _ in 0..iters {
                total += n.time_protocol().prove;
            }
            total
        })
    });
    group.bench_function("arkcp_verify", |b| {
        b.iter_custom(|iters| {
            let mut total = Duration::ZERO;
            for _ in 0..iters {
                total += n.time_protocol().verify;
            }
            total
        })
    });

    group.finish();
}

criterion_group!(benches, bench_schnorr);
criterion_main!(benches);
