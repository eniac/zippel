//! Simple performance sanity check for `enterpairs` and `LSet::pop`.
//!
//! Reports approximate ms/call numbers for two scenarios:
//!
//! 1. `enterpairs` on a synthetic SBasis of 100 single-term polys
//!    with random sparse LMs, inserting one more element `h`.
//! 2. `LSet::pop` + re-insert cycle, 10 000 iterations.
//!
//! This is a sanity floor, not a benchmark suite. Run with
//! `cargo run --release --example gm_bench`.

use std::time::Instant;

use ark_bls12_381::Fr;
use ark_ff::One;
use ark_gb::gm;
use ark_gb::{GrevLexTerm, LSet, MonoTerm, Pair, Poly, Ring, SBasis};

const NVARS: u32 = 6;

fn mk_ring() -> Ring<Fr> {
    Ring::<Fr>::new(NVARS).unwrap()
}

/// A simple LCG so the example stays dependency-free.
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }
    fn u32_in(&mut self, bound: u32) -> u32 {
        (self.next() >> 32) as u32 % bound.max(1)
    }
}

fn random_lm(r: &Ring<Fr>, rng: &mut Lcg) -> GrevLexTerm {
    let n = r.nvars() as usize;
    let mut exps = vec![0u32; n];
    // Sparse: 2 variables with small exponents.
    for _ in 0..2 {
        let k = rng.u32_in(n as u32) as usize;
        exps[k] = exps[k].saturating_add(rng.u32_in(3) + 1);
        if exps[k] > 6 {
            exps[k] = 6;
        }
    }
    GrevLexTerm::from(MonoTerm::from_exponents(r, &exps).unwrap())
}

fn bench_enterpairs() {
    let r = mk_ring();
    let mut rng = Lcg(0xdead_beef_dead_beef);
    let mut s: SBasis<Fr, GrevLexTerm> = SBasis::new();
    for _ in 0..100 {
        let lm = random_lm(&r, &mut rng);
        s.insert(&r, Poly::monomial(&r, Fr::one(), lm));
    }

    // Reserve an h to enterpairs against.
    let h_lm = random_lm(&r, &mut rng);
    let h = Poly::monomial(&r, Fr::one(), h_lm);
    let h_idx = s.insert(&r, h.clone()) as u32;

    // Call enterpairs many times on successive fresh LSet so the
    // timing isolates enterpairs alone. Each call generates up to
    // 100 candidate pairs.
    const ITERS: u32 = 1000;
    let t0 = Instant::now();
    for _ in 0..ITERS {
        let mut l = LSet::new();
        let _ = gm::enterpairs(&r, &s, h_idx, &h, h.lm_deg(), &mut l, 0);
        std::hint::black_box(l);
    }
    let dt = t0.elapsed();
    println!(
        "enterpairs: {:>7.3} us/call over {} iters (SBasis len = 101)",
        dt.as_secs_f64() * 1e6 / ITERS as f64,
        ITERS
    );
}

fn bench_lset_pop_reinsert() {
    let r = mk_ring();
    let mut l = LSet::new();
    let lcm = MonoTerm::from_exponents(&r, &vec![1u32; r.nvars() as usize]).unwrap();
    // Seed.
    for k in 0u32..256u32 {
        l.insert(Pair::new(0, k + 1, lcm, k % 17, k as u64));
    }

    let t0 = Instant::now();
    const ITERS: u32 = 10_000;
    let mut sugar_cursor: u32 = 0;
    let mut arrival_cursor: u64 = 10_000;
    for _ in 0..ITERS {
        let p = l.pop().unwrap();
        sugar_cursor = sugar_cursor.wrapping_add(1) & 0xff;
        arrival_cursor += 1;
        l.insert(Pair::new(p.i, p.j, lcm, sugar_cursor, arrival_cursor));
    }
    let dt = t0.elapsed();
    println!(
        "LSet pop+insert: {:>7.3} us/cycle over {} cycles",
        dt.as_secs_f64() * 1e6 / ITERS as f64,
        ITERS
    );
}

fn main() {
    bench_enterpairs();
    bench_lset_pop_reinsert();
}
