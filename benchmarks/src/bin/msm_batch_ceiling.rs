//! Phase-0 ceiling test for a `dot_batch` primitive.
//!
//! Question: at the Spartan row-commit shapes (K MSMs of size N, all
//! against the SAME base vector), how much wall-clock does a
//! shared-setup batched Pippenger save over K independent arkworks
//! `msm` calls?
//!
//! Variants:
//!   A  : K x `<G as VariableBaseMSM>::msm(bases, row_k)` — zippel's
//!        current row-commit pattern (bases pre-normalized to affine,
//!        as `Value::VecG1Affine` already is at runtime).
//!   A' : ark-spartan's actual `batch_commit` pattern — per row:
//!        `normalize_batch(proj_bases)` + `scalars.to_vec()` + push
//!        blind + `msm(N+1)`. Context: what the baseline we're chasing
//!        actually pays per row.
//!   B0 : hand-rolled Pippenger, fresh bucket/bigint buffers per row.
//!        Isolates "hand-rolled vs arkworks msm" implementation
//!        quality from the batching question.
//!   B1 : hand-rolled Pippenger with ONE bucket table and ONE bigint
//!        buffer reused across all K rows — the shared-setup
//!        `dot_batch` candidate.
//!
//! Decision rule (agreed before running): if B1 beats A by less than
//! ~50 ms at the M=18 shape, the `dot_batch` primitive does NOT have
//! the headroom to close the observed MSM cliff, and the cliff's
//! attribution must be re-examined instead of building the primitive.
//!
//! Run single-threaded to match the paper benchmark conditions:
//!   RAYON_NUM_THREADS=1 cargo run --release --bin msm_batch_ceiling

use ark_curve25519::{EdwardsAffine, EdwardsProjective, Fr};
use ark_ec::{CurveGroup, VariableBaseMSM};
use ark_ff::{AdditiveGroup, PrimeField, UniformRand};
use ark_std::Zero;
use ark_std::rand::SeedableRng;
use ark_std::rand::rngs::StdRng;
use std::time::Instant;

/// Same window heuristic as arkworks' Pippenger (`ln_without_floats + 2`).
fn window_size(n: usize) -> usize {
    if n < 32 {
        3
    } else {
        let log2 = (usize::BITS - 1 - n.leading_zeros()) as usize;
        log2 * 69 / 100 + 2
    }
}

/// Extract `c` bits of `big` starting at bit `start` (LSB-first).
/// `c <= 60` so at most two limbs are touched.
#[inline]
fn extract_bits(limbs: &[u64], start: usize, c: usize) -> usize {
    let limb = start / 64;
    let off = start % 64;
    if limb >= limbs.len() {
        return 0;
    }
    let mut v = limbs[limb] >> off;
    if off + c > 64 && limb + 1 < limbs.len() {
        v |= limbs[limb + 1] << (64 - off);
    }
    (v as usize) & ((1usize << c) - 1)
}

/// Hand-rolled Pippenger for one scalar row, writing into caller-provided
/// scratch. `buckets` must have length `2^c - 1`; it is zeroed here (that
/// zeroing is part of the algorithm and paid by every variant), but its
/// ALLOCATION is the caller's, which is what B1 amortizes across rows.
fn pippenger_row(
    bases: &[EdwardsAffine],
    bigints: &[<Fr as PrimeField>::BigInt],
    c: usize,
    num_bits: usize,
    buckets: &mut [EdwardsProjective],
) -> EdwardsProjective {
    let window_starts: Vec<usize> = (0..num_bits).step_by(c).collect();
    let mut window_sums: Vec<EdwardsProjective> = Vec::with_capacity(window_starts.len());
    for &w_start in &window_starts {
        for b in buckets.iter_mut() {
            *b = EdwardsProjective::zero();
        }
        for (i, big) in bigints.iter().enumerate() {
            let digit = extract_bits(big.as_ref(), w_start, c);
            if digit != 0 {
                buckets[digit - 1] += bases[i]; // mixed addition
            }
        }
        // Running-sum bucket aggregation.
        let mut running = EdwardsProjective::zero();
        let mut acc = EdwardsProjective::zero();
        for b in buckets.iter().rev() {
            running += b;
            acc += &running;
        }
        window_sums.push(acc);
    }
    // Combine windows, highest first.
    let mut total = *window_sums.last().expect("at least one window");
    for w in window_sums.iter().rev().skip(1) {
        for _ in 0..c {
            total.double_in_place();
        }
        total += w;
    }
    total
}

/// B1: shared-setup batched MSM — one bucket table + one bigint buffer
/// across all K rows.
fn batched_msm(bases: &[EdwardsAffine], rows: &[&[Fr]]) -> Vec<EdwardsProjective> {
    let n = bases.len();
    let c = window_size(n);
    let num_bits = Fr::MODULUS_BIT_SIZE as usize;
    let mut buckets = vec![EdwardsProjective::zero(); (1 << c) - 1];
    let mut bigints: Vec<<Fr as PrimeField>::BigInt> = Vec::with_capacity(n);
    let mut out = Vec::with_capacity(rows.len());
    for row in rows {
        bigints.clear();
        bigints.extend(row.iter().map(|s| s.into_bigint()));
        out.push(pippenger_row(bases, &bigints, c, num_bits, &mut buckets));
    }
    out
}

/// B0: same Pippenger, but fresh buffers per row (no sharing).
fn unbatched_handrolled(bases: &[EdwardsAffine], rows: &[&[Fr]]) -> Vec<EdwardsProjective> {
    let n = bases.len();
    let c = window_size(n);
    let num_bits = Fr::MODULUS_BIT_SIZE as usize;
    rows.iter()
        .map(|row| {
            let mut buckets = vec![EdwardsProjective::zero(); (1 << c) - 1];
            let bigints: Vec<<Fr as PrimeField>::BigInt> =
                row.iter().map(|s| s.into_bigint()).collect();
            pippenger_row(bases, &bigints, c, num_bits, &mut buckets)
        })
        .collect()
}

fn mean_ms(samples: &[f64]) -> f64 {
    samples.iter().sum::<f64>() / samples.len() as f64
}

fn main() {
    let shapes: &[(usize, usize, &str)] = &[
        (128, 256, "M=16"),
        (256, 256, "M=17"),
        (256, 512, "M=18"),
        (512, 1024, "M=20 trend"),
    ];
    const REPS: usize = 3;

    println!("msm_batch ceiling test (curve25519 / arkworks 0.6)");
    println!(
        "threads: RAYON_NUM_THREADS={}",
        std::env::var("RAYON_NUM_THREADS").unwrap_or_else(|_| "default".into())
    );
    println!();

    let mut rng = StdRng::from_seed([42u8; 32]);

    for &(k, n, label) in shapes {
        // Inputs.
        let bases_proj: Vec<EdwardsProjective> =
            (0..n).map(|_| EdwardsProjective::rand(&mut rng)).collect();
        let bases: Vec<EdwardsAffine> = EdwardsProjective::normalize_batch(&bases_proj);
        let blind_h = EdwardsProjective::rand(&mut rng);
        let scalars_flat: Vec<Fr> = (0..k * n).map(|_| Fr::rand(&mut rng)).collect();
        let rows: Vec<&[Fr]> = (0..k).map(|i| &scalars_flat[i * n..(i + 1) * n]).collect();
        let blinds: Vec<Fr> = (0..k).map(|_| Fr::rand(&mut rng)).collect();

        // Correctness gate before timing: B1 == A on the first 4 rows.
        let check_rows = 4.min(k);
        let expected: Vec<EdwardsProjective> = rows[..check_rows]
            .iter()
            .map(|row| EdwardsProjective::msm(&bases, row).expect("msm"))
            .collect();
        let got = batched_msm(&bases, &rows[..check_rows]);
        for (i, (e, g)) in expected.iter().zip(got.iter()).enumerate() {
            assert_eq!(
                e.into_affine(),
                g.into_affine(),
                "hand-rolled Pippenger mismatch at row {i} (K={k}, N={n})"
            );
        }

        // Timed variants: 1 warmup + REPS timed passes each.
        let mut t_a = Vec::new();
        let mut t_a_prime = Vec::new();
        let mut t_b0 = Vec::new();
        let mut t_b1 = Vec::new();

        for rep in 0..=REPS {
            // A: K independent arkworks msm calls on pre-normalized bases.
            let t = Instant::now();
            let mut acc = EdwardsProjective::zero();
            for row in &rows {
                acc += EdwardsProjective::msm(&bases, row).expect("msm");
            }
            let dt = t.elapsed().as_secs_f64() * 1e3;
            std::hint::black_box(acc);
            if rep > 0 {
                t_a.push(dt);
            }

            // A': ark-spartan batch_commit pattern (normalize + copy +
            // push blind + msm(N+1)) per row.
            let t = Instant::now();
            let mut acc = EdwardsProjective::zero();
            for (row, blind) in rows.iter().zip(blinds.iter()) {
                let mut b: Vec<EdwardsAffine> = EdwardsProjective::normalize_batch(&bases_proj);
                let mut s: Vec<Fr> = row.to_vec();
                b.push(blind_h.into_affine());
                s.push(*blind);
                acc += EdwardsProjective::msm(&b, &s).expect("msm");
            }
            let dt = t.elapsed().as_secs_f64() * 1e3;
            std::hint::black_box(acc);
            if rep > 0 {
                t_a_prime.push(dt);
            }

            // B0: hand-rolled, fresh buffers per row.
            let t = Instant::now();
            let out = unbatched_handrolled(&bases, &rows);
            let dt = t.elapsed().as_secs_f64() * 1e3;
            std::hint::black_box(out);
            if rep > 0 {
                t_b0.push(dt);
            }

            // B1: hand-rolled, shared buffers across rows.
            let t = Instant::now();
            let out = batched_msm(&bases, &rows);
            let dt = t.elapsed().as_secs_f64() * 1e3;
            std::hint::black_box(out);
            if rep > 0 {
                t_b1.push(dt);
            }
        }

        let a = mean_ms(&t_a);
        let ap = mean_ms(&t_a_prime);
        let b0 = mean_ms(&t_b0);
        let b1 = mean_ms(&t_b1);
        let total_muls = (k * n) as f64;

        println!("shape K={k} N={n}  ({label}, {} scalar-muls)", k * n);
        println!("  A  (arkworks msm xK, affine bases)   : {a:9.2} ms  ({:6.1} ns/mul)", a * 1e6 / total_muls);
        println!("  A' (ark-spartan batch_commit pattern): {ap:9.2} ms  ({:6.1} ns/mul)", ap * 1e6 / total_muls);
        println!("  B0 (hand-rolled, fresh buffers)      : {b0:9.2} ms  ({:6.1} ns/mul)", b0 * 1e6 / total_muls);
        println!("  B1 (hand-rolled, shared buffers)     : {b1:9.2} ms  ({:6.1} ns/mul)", b1 * 1e6 / total_muls);
        println!(
            "  B1 vs A: {:+.2} ms ({:+.1}%)   B1 vs B0: {:+.2} ms   A' vs A: {:+.2} ms",
            b1 - a,
            (b1 - a) / a * 100.0,
            b1 - b0,
            ap - a
        );
        println!();
    }
}
