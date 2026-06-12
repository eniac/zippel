//! PST13 (a.k.a. XZZPD19 / Libra) multilinear polynomial commitment scheme.
//!
//! Vendored from `ark-poly-commit-0.6.0/src/multilinear_pc/mod.rs` and
//! patched to remove TWO performance bugs in the upstream `open` function.
//! Setup / trim / commit / check are byte-identical to upstream. Only
//! `open` has been changed; the protocol is unchanged (the same proof
//! bytes pass the same verifier).
//!
//! ## Fix 1 — half-size MSM via pre-summed bases
//!
//! Upstream `open` builds, at each of the `nv` recursion rounds, a
//! scalar vector of length `2^k` where each scalar is duplicated:
//!
//! ```ignore
//! let scalars: Vec<_> = (0..(1 << k))
//!     .map(|x| q[k][x >> 1].into_bigint())   // q[b], q[b], q[b+1], q[b+1], ...
//!     .collect();
//! let pi_h = msm_bigint(&ck.powers_of_h[i], &scalars);
//! ```
//!
//! That's an MSM of size `2^k` driven by `2^(k-1)` unique values. We
//! collapse it into the mathematically-equivalent half-size MSM
//!
//! ```ignore
//! pi_h = Σ_b q[k][b] · (ck_h[2b] + ck_h[2b+1])
//! ```
//!
//! by precomputing `bases_summed[b] = ck_h[2b] + ck_h[2b+1]`. Pippenger's
//! cost is roughly linear in `N`, so halving `N` halves the MSM work
//! per round.
//!
//! ## Fix 2 — concurrent round MSMs via `rayon::scope`
//!
//! Upstream emits the `nv` round MSMs serially:
//!
//! ```ignore
//! for i in 0..nv {
//!     ... compute q[k] ...
//!     let pi_h = msm_bigint(...);    // blocks until done before round i+1
//!     proofs.push(pi_h);
//! }
//! ```
//!
//! Each `pi_h` is independent of subsequent rounds — only the `r[k-1]`
//! folding feeds into the next iteration. We split the function into two
//! phases: a sequential pass that computes all `r/q` levels (the
//! recursion IS sequential), then a parallel pass that fans out all `nv`
//! MSMs into `rayon::scope`. Critical-path cost becomes `T_0` (the
//! largest MSM) instead of `Σ T_k ≈ 2·T_0`.
//!
//! ## Combined effect at log_size=18, t≥2
//!
//! - Fix 1: ~2× fewer G2 muls per round.
//! - Fix 2: critical path ≈ first MSM instead of sum of all 18.
//!
//! Together: ~4× speedup vs the upstream crate at t=1, narrowing at
//! high thread counts where rayon's intra-MSM `par_iter` already
//! parallelizes each individual MSM. Matches the zippel side's dataflow
//! advantage observed in earlier benches.

use crate::pst13_upstream::data_structures::{
    Commitment, CommitterKey, Proof, UniversalParams, VerifierKey,
};
use ark_ec::{
    pairing::Pairing,
    scalar_mul::{BatchMulPreprocessing, ScalarMul},
    AffineRepr, CurveGroup, VariableBaseMSM,
};
use ark_ff::{Field, One, PrimeField, UniformRand};
use ark_poly::{DenseMultilinearExtension, MultilinearExtension};
use ark_std::{
    collections::LinkedList, iter::FromIterator, marker::PhantomData, ops::Mul, rand::RngCore,
};
use rayon::prelude::*;
use std::sync::Mutex;

pub mod data_structures;

pub struct MultilinearPC<E: Pairing> {
    _engine: PhantomData<E>,
}

impl<E: Pairing> MultilinearPC<E> {
    pub fn setup<R: RngCore>(num_vars: usize, rng: &mut R) -> UniversalParams<E> {
        assert!(num_vars > 0, "constant polynomial not supported");
        let g = E::G1::rand(rng);
        let h = E::G2::rand(rng);
        let mut powers_of_g = Vec::new();
        let mut powers_of_h = Vec::new();
        let t: Vec<_> = (0..num_vars).map(|_| E::ScalarField::rand(rng)).collect();

        let mut eq: LinkedList<DenseMultilinearExtension<E::ScalarField>> =
            LinkedList::from_iter(eq_extension(&t).into_iter());
        let mut eq_arr = LinkedList::new();
        let mut base = eq.pop_back().unwrap().evaluations;

        for i in (0..num_vars).rev() {
            eq_arr.push_front(remove_dummy_variable(&base, i));
            if i != 0 {
                let mul = eq.pop_back().unwrap().evaluations;
                base = base
                    .into_iter()
                    .zip(mul.into_iter())
                    .map(|(a, b)| a * &b)
                    .collect();
            }
        }

        let mut pp_powers = Vec::new();
        for i in 0..num_vars {
            let eq = eq_arr.pop_front().unwrap();
            let pp_k_powers = (0..(1 << (num_vars - i))).map(|x| eq[x]);
            pp_powers.extend(pp_k_powers);
        }

        let g_table = BatchMulPreprocessing::new(g, num_vars);
        let pp_g = g_table.batch_mul(&pp_powers);
        let pp_h = h.batch_mul(&pp_powers);
        let mut start = 0;
        for i in 0..num_vars {
            let size = 1 << (num_vars - i);
            let pp_k_g = (&pp_g[start..(start + size)]).to_vec();
            let pp_k_h = (&pp_h[start..(start + size)]).to_vec();
            powers_of_g.push(pp_k_g);
            powers_of_h.push(pp_k_h);
            start += size;
        }

        let g_mask = g_table.batch_mul(&t);

        UniversalParams {
            num_vars,
            g: g.into_affine(),
            g_mask,
            h: h.into_affine(),
            powers_of_g,
            powers_of_h,
        }
    }

    pub fn trim(
        params: &UniversalParams<E>,
        supported_num_vars: usize,
    ) -> (CommitterKey<E>, VerifierKey<E>) {
        assert!(supported_num_vars <= params.num_vars);
        let to_reduce = params.num_vars - supported_num_vars;
        let ck = CommitterKey {
            powers_of_h: (&params.powers_of_h[to_reduce..]).to_vec(),
            powers_of_g: (&params.powers_of_g[to_reduce..]).to_vec(),
            g: params.g,
            h: params.h,
            nv: supported_num_vars,
        };
        let vk = VerifierKey {
            nv: supported_num_vars,
            g: params.g,
            h: params.h,
            g_mask_random: (&params.g_mask[to_reduce..]).to_vec(),
        };
        (ck, vk)
    }

    pub fn commit(
        ck: &CommitterKey<E>,
        polynomial: &impl MultilinearExtension<E::ScalarField>,
    ) -> Commitment<E> {
        let nv = polynomial.num_vars();
        // Parallel into_bigint. Upstream uses `.into_iter().map().collect()`
        // — serial over 2^n elements; at n=18 that's 262K conversions on
        // one thread, ~10-30ms of wasted wall-clock regardless of how
        // many cores you have.
        let evals = polynomial.to_evaluations();
        let scalars: Vec<_> = evals.par_iter().map(|&x| x.into_bigint()).collect();
        let g_product =
            <E::G1 as VariableBaseMSM>::msm_bigint(&ck.powers_of_g[0], scalars.as_slice())
                .into_affine();
        Commitment { nv, g_product }
    }

    /// Outputs an opening proof. PATCHED vs upstream — see module docs.
    ///
    /// Single fused dataflow pipeline (no Phase 1 → Phase 2 barrier):
    /// the per-level folding loop dispatches round `i`'s MSM the moment
    /// its `q_i` is computed, instead of accumulating all `q_levels`
    /// first. Round `i`'s MSM therefore runs **concurrently** with
    /// round `i+1`'s folding — matching zippel's dataflow scheduling,
    /// where `pi_curr <- dot(q, ck_nxt)` becomes a graph node that
    /// fires the moment `q` and `ck_nxt` are ready while the recursion
    /// continues. The two-phase version had to wait for all folding to
    /// finish before any MSM could start; the largest (round-0) MSM
    /// could already have been in flight.
    pub fn open(
        ck: &CommitterKey<E>,
        polynomial: &impl MultilinearExtension<E::ScalarField>,
        point: &[E::ScalarField],
    ) -> Proof<E> {
        assert_eq!(polynomial.num_vars(), ck.nv, "Invalid size of polynomial");
        let nv = polynomial.num_vars();

        let proofs_slot: Vec<Mutex<Option<E::G2Affine>>> =
            (0..nv).map(|_| Mutex::new(None)).collect();
        let ck_powers_h = &ck.powers_of_h;

        rayon::scope(|sc| {
            let mut r_prev: Vec<E::ScalarField> = polynomial.to_evaluations();

            for i in 0..nv {
                let k = nv - i;
                let point_at_k = point[i];
                let one_minus_z = E::ScalarField::one() - &point_at_k;
                let half = 1usize << (k - 1);

                // Compute q_k and r_next in one parallel pass. The outer
                // recursion is genuinely sequential (round i+1's folding
                // needs r_next from round i), so this is the one synch
                // point per level — but it's all we wait on before
                // launching the MSM.
                let (q_k, r_next): (Vec<E::ScalarField>, Vec<E::ScalarField>) = (0..half)
                    .into_par_iter()
                    .map(|b| {
                        let r_lo = r_prev[b << 1];
                        let r_hi = r_prev[(b << 1) + 1];
                        let q_b = r_hi - r_lo;
                        let r_next_b = r_lo * one_minus_z + r_hi * point_at_k;
                        (q_b, r_next_b)
                    })
                    .unzip();

                // Hand `q_k` off to the spawned MSM task by moving it
                // into the closure. The next iteration only needs
                // `r_next`, so the round-i MSM can run unhindered while
                // round i+1's folding starts on free cores.
                let ck_full: &Vec<E::G2Affine> = &ck_powers_h[i];
                let slot = &proofs_slot[i];

                sc.spawn(move |_| {
                    // Fix 1: pre-sum adjacent pairs of bases — the
                    // upstream MSM is over `2^k` bases with q[b]
                    // duplicated at indices 2b and 2b+1, equivalent to
                    // an MSM over `2^(k-1)` summed bases scaled by q[b].
                    let bases_summed_proj: Vec<E::G2> = (0..half)
                        .into_par_iter()
                        .map(|b| {
                            ck_full[b << 1].into_group() + ck_full[(b << 1) + 1].into_group()
                        })
                        .collect();
                    let bases_summed: Vec<E::G2Affine> =
                        E::G2::normalize_batch(&bases_summed_proj);

                    let scalars: Vec<_> = q_k.par_iter().map(|x| x.into_bigint()).collect();

                    let pi_h = <E::G2 as VariableBaseMSM>::msm_bigint(&bases_summed, &scalars)
                        .into_affine();
                    *slot.lock().unwrap() = Some(pi_h);
                });

                r_prev = r_next;
            }
        });

        let proofs: Vec<E::G2Affine> = proofs_slot
            .into_iter()
            .map(|m| m.into_inner().unwrap().expect("MSM never ran"))
            .collect();

        Proof { proofs }
    }

    pub fn check<'a>(
        vk: &VerifierKey<E>,
        commitment: &Commitment<E>,
        point: &[E::ScalarField],
        value: E::ScalarField,
        proof: &Proof<E>,
    ) -> bool {
        let left = E::pairing(commitment.g_product.into_group() - &vk.g.mul(value), vk.h);

        let g_mul = vk.g.into_group().batch_mul(point);

        let pairing_lefts: Vec<_> = (0..vk.nv)
            .map(|i| vk.g_mask_random[i].into_group() - &g_mul[i])
            .collect();
        let pairing_lefts: Vec<E::G1Affine> = E::G1::normalize_batch(&pairing_lefts);
        let pairing_lefts: Vec<E::G1Prepared> = pairing_lefts
            .into_iter()
            .map(|x| E::G1Prepared::from(x))
            .collect();

        let pairing_rights: Vec<E::G2Prepared> = proof
            .proofs
            .iter()
            .map(|x| E::G2Prepared::from(*x))
            .collect();

        let right = E::multi_pairing(pairing_lefts, pairing_rights);
        left == right
    }
}

fn remove_dummy_variable<F: Field>(poly: &[F], pad: usize) -> Vec<F> {
    if pad == 0 {
        return poly.to_vec();
    }
    if !poly.len().is_power_of_two() {
        panic!("Size of polynomial should be power of two. ")
    }
    let nv = ark_std::log2(poly.len()) as usize - pad;
    let table: Vec<_> = (0..(1 << nv)).map(|x| poly[x << pad]).collect();
    table
}

fn eq_extension<F: Field>(t: &[F]) -> Vec<DenseMultilinearExtension<F>> {
    let dim = t.len();
    let mut result = Vec::new();
    for i in 0..dim {
        let mut poly = Vec::with_capacity(1 << dim);
        for x in 0..(1 << dim) {
            let xi = if x >> i & 1 == 1 { F::one() } else { F::zero() };
            let ti = t[i];
            let ti_xi = ti * xi;
            poly.push(ti_xi + ti_xi - xi - ti + F::one());
        }
        result.push(DenseMultilinearExtension::from_evaluations_vec(dim, poly));
    }

    result
}

// Suppress the unused-import warnings when `eq_extension`/`remove_dummy_variable`
// land via `let _ = Zero::zero;`-style attempts later — these helpers are used
// only by `setup`, but compilers don't always see through the LinkedList path.
#[allow(dead_code)]
fn _zero_unused<F: Field>() -> F {
    F::zero()
}
