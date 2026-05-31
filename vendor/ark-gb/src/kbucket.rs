//! Geobucket reducer (`KBucket`).
//!
//! A [`KBucket`] is a deferred-merge polynomial accumulator. It is the
//! Rust port of Singular's `kBucket` (see
//! `~/Singular/libpolys/polys/kbuckets.{h,cc}`) and serves the same
//! role as FLINT's `nmod_mpoly_geobucket` and mathicgb's
//! `Reducer_Geobucket`. The idea (Yan 1998, "The Geobucket Data
//! Structure for Polynomials") is to scatter the terms of a partial
//! reduction across exponentially-sized slots so that a long sequence
//! of `p ← p − c·m·q` operations costs `O(log n)` amortised per step
//! instead of `O(|p|)` for a single linear merge.
//!
//! ## Slot sizing
//!
//! Slot `i` holds polynomials of length `≤ 4^i`. In Singular's
//! terminology, `pLogLength(l) = ceil(log_4(l))` picks the slot for a
//! polynomial of length `l`. With `MAX_BUCKET = 14` in
//! `kbuckets.h`, the bucket has `15` slots and caps at
//! `4^14 = 2^28` terms.
//!
//! ```text
//! slot 0: length ≤ 1
//! slot 1: length ≤ 4
//! slot 2: length ≤ 16
//! slot 3: length ≤ 64
//! ...
//! slot 14: length ≤ 4^14 = 2^28
//! ```
//!
//! When a `minus_m_mult_p` operation's destination slot is already
//! occupied, we cascade the resulting polynomial into the next slot
//! the merged length picks — which in turn may need to merge with
//! whatever lives there, possibly triggering another cascade, and so
//! on. The cascade is intrinsically bidirectional: lengths typically
//! grow when combining non-overlapping polynomials, but term
//! cancellation can shrink the merged result into a strictly smaller
//! slot. Termination is bounded by `NUM_SLOTS` iterations regardless
//! of direction. This mirrors the
//! `while (bucket->buckets[i] != NULL)` loop in `kBucket_Add_q` and
//! `kBucket_Minus_m_Mult_p` in Singular's `kbuckets.cc`, which
//! likewise allow either direction.
//!
//! ## Threading
//!
//! A `KBucket` is `Send` but **not** `Sync`. Each bucket is owned by
//! exactly one thread at a time (the future `LObject` in the bba
//! driver). There is no locking; no shared concurrent access is
//! supported. Send-only matches Singular's invariant that each
//! `LObject.bucket` is private to the worker reducing it.
//!
//! ## Leading-term cache and dirty slots
//!
//! `leading()` is probed repeatedly by the bba inner loop. The cache
//! stores the `(coeff, monomial, slot)` tuple of the last computed
//! leader; as long as `dirty == 0` subsequent probes return the
//! cached value without re-scanning. Any operation that can change
//! the sum (currently `minus_m_mult_p` and `extract_leading`) sets
//! the relevant bits in `dirty` and clears the cache.
//!
//! ## References
//!
//! * `~/Singular/libpolys/polys/kbuckets.h` (API)
//! * `~/Singular/libpolys/polys/kbuckets.cc` (cascade algorithm)
//! * `~/Singular/libpolys/polys/templates/p_kBucketSetLm__T.cc`
//!   (scan-slots-for-leader algorithm)
//! * `~/mathicgb/src/mathicgb/Reducer_Geobucket.cpp` (same
//!   algorithmic family, different code style)
//! * Yan 1998, "The Geobucket Data Structure for Polynomials".
//!
//! Algorithms re-derived; no code copied.

use std::sync::Arc;

use crate::field::Field;
use crate::monomial::{MonoTerm, Monomial};
use crate::poly::Poly;
use crate::ring::Ring;

/// Number of slots. Matches Singular's `MAX_BUCKET + 1 = 15`.
pub const NUM_SLOTS: usize = 15;

/// Base of the slot length geometry. `SLOT_BASE = 4` means slot `i`
/// holds polys of length `≤ 4^i`; same value Singular uses by default
/// (`BUCKET_TWO_BASE` is a compile-time alternative in `kbuckets.h`
/// that Singular's comments describe as less efficient in practice).
pub const SLOT_BASE: usize = 4;

/// Smallest slot index that can hold a polynomial of length `len`.
///
/// Matches Singular's `pLogLength(l) = ceil(log_4(l))`:
///
/// * `len == 0` → slot 0 (an empty poly fits anywhere; we pick slot 0
///   for determinism).
/// * `len == 1` → slot 0 (`ceil(log_4(1)) = 0`).
/// * `len ∈ 2..=4` → slot 1.
/// * `len ∈ 5..=16` → slot 2.
/// * ... `len ∈ (4^(i-1), 4^i]` → slot `i`.
///
/// Panics in debug builds if `len > 4^(NUM_SLOTS - 1) = 4^14 = 2^28`;
/// in release builds it saturates at `NUM_SLOTS - 1`.
#[inline]
fn slot_for_len(len: usize) -> usize {
    if len <= 1 {
        return 0;
    }
    let mut slot = 0usize;
    let mut cap = 1usize; // 4^0
    while cap < len && slot < NUM_SLOTS - 1 {
        slot += 1;
        cap = cap.saturating_mul(SLOT_BASE);
    }
    debug_assert!(
        cap >= len,
        "kBucket slot overflow: len = {len} > 4^{} = {cap}",
        NUM_SLOTS - 1
    );
    slot
}

/// Maximum number of terms a slot of index `i` can hold. Saturates at
/// `usize::MAX` for very high slots.
#[inline]
fn slot_capacity(i: usize) -> usize {
    debug_assert!(i < NUM_SLOTS);
    SLOT_BASE.checked_pow(i as u32).unwrap_or(usize::MAX)
}

/// A geobucket polynomial accumulator. See module documentation.
///
/// `Send + !Sync`: a single owning thread may mutate freely; shared
/// references across threads are *not* supported. The `!Sync`
/// restriction is documented — transferring ownership across threads
/// is legal (the bba driver will do so when stealing work), but
/// shared access is not.
#[derive(Debug)]
pub struct KBucket<F: Field + Copy, M: Monomial<F, W> + From<MonoTerm<W>>, const W: usize = 4> {
    /// Ring context. Shared via `Arc` so the bucket can outlive the
    /// scope in which it was created without copying ring state.
    ring: Arc<Ring<F, W>>,
    /// Exponentially-sized slots; `slots[i]` holds polys of length
    /// `≤ 4^i`. `None` means the slot is empty.
    slots: [Option<Poly<F, M, W>>; NUM_SLOTS],
    /// Cached leading term: `(coeff, monomial, slot_index)`. The
    /// `slot_index` is which slot currently owns the leading term.
    lm_cache: Option<(F, M, usize)>,
    /// Bitmask of slots changed since the last `leading()` call.
    /// Bit `i` (i < `NUM_SLOTS`) corresponds to slot `i`.
    dirty: u32,
    /// Force `!Sync`: `KBucket` is owned by at most one thread at a
    /// time. `PhantomData<Cell<()>>` is `Send` but not `Sync`.
    _not_sync: std::marker::PhantomData<std::cell::Cell<()>>,
}

impl<F: Field + Copy, M: Monomial<F, W> + From<MonoTerm<W>>, const W: usize> KBucket<F, M, W> {
    // ----- Constructors -----

    /// Empty bucket.
    pub fn new(ring: Arc<Ring<F, W>>) -> Self {
        Self {
            ring,
            slots: std::array::from_fn(|_| None),
            lm_cache: None,
            dirty: 0,
            _not_sync: std::marker::PhantomData,
        }
    }

    /// Seed the bucket from a polynomial. The polynomial is consumed
    /// and placed in whichever slot its length selects.
    pub fn from_poly(ring: Arc<Ring<F, W>>, p: Poly<F, M, W>) -> Self {
        let mut b = Self::new(ring);
        if !p.is_zero() {
            let i = slot_for_len(p.len());
            debug_assert!(i < NUM_SLOTS);
            b.slots[i] = Some(p);
            b.mark_dirty(i);
        }
        b
    }

    // ----- Accessors -----

    /// The ring this bucket lives in.
    #[inline]
    pub fn ring(&self) -> &Arc<Ring<F, W>> {
        &self.ring
    }

    /// Whether every slot is empty. Does *not* mean the algebraic
    /// value is zero: slots may cancel under merge. Callers who want
    /// the true zero test should use [`KBucket::is_zero`].
    #[inline]
    pub fn all_slots_empty(&self) -> bool {
        self.slots.iter().all(Option::is_none)
    }

    // ----- Mutation -----

    fn mark_dirty(&mut self, slot: usize) {
        debug_assert!(slot < NUM_SLOTS);
        self.dirty |= 1u32 << slot;
        self.lm_cache = None;
    }

    /// Absorb a polynomial `q` into the slot hierarchy, cascading if
    /// the destination slot is already occupied. This is the single
    /// merge primitive used by both `minus_m_mult_p` (which hands us
    /// `-c·m·p`) and `from_poly` seeding.
    ///
    /// The cascade may move in either direction: lengths typically
    /// grow when adding non-overlapping polynomials (so `target > i`),
    /// but term cancellation can shrink the merged result into a
    /// strictly smaller slot (`target < i`). Termination is bounded
    /// by `NUM_SLOTS` iterations regardless of direction — each step
    /// either places into an empty slot, returns on full
    /// cancellation, or consumes one more occupied slot.
    ///
    /// Precondition: `q` is already canonical (matches `Poly`
    /// invariants) and nonzero.
    fn absorb(&mut self, mut q: Poly<F, M, W>) {
        debug_assert!(!q.is_zero());
        let mut i = slot_for_len(q.len());
        debug_assert!(i < NUM_SLOTS, "slot overflow: len = {}", q.len());

        // Cascade upward while the chosen slot is already occupied.
        loop {
            match self.slots[i].take() {
                None => {
                    self.slots[i] = Some(q);
                    self.mark_dirty(i);
                    return;
                }
                Some(existing) => {
                    // Both operands are already owned here (existing
                    // via `take()`, q by value), so use the
                    // destructive variant — on the List backend this
                    // splices input nodes into the output chain
                    // instead of allocating a fresh Box<Node> per
                    // output term (ADR-015). On the Vec backend
                    // `add_consuming` is a thin forwarder to `add`.
                    let merged = existing.add_consuming(q, &self.ring);
                    self.mark_dirty(i);
                    if merged.is_zero() {
                        // Accumulated sum cancelled; nothing to place.
                        return;
                    }
                    let target = slot_for_len(merged.len());
                    if target == i {
                        self.slots[i] = Some(merged);
                        return;
                    }
                    // The merge result may land in either a strictly
                    // larger slot (typical case: lengths add) *or*
                    // a strictly smaller one when terms cancel. Both
                    // directions are valid; the cascade re-enters the
                    // loop at the new slot and is bounded by
                    // `NUM_SLOTS` iterations (each step either places
                    // into an empty slot, returns on full
                    // cancellation, or consumes one more occupied
                    // slot).
                    debug_assert!(
                        target < NUM_SLOTS,
                        "bucket overflow: merged length {} > 4^{}",
                        merged.len(),
                        NUM_SLOTS - 1
                    );
                    q = merged;
                    i = target;
                }
            }
        }
    }

    /// Subtract `c * m * p` from this bucket in place, without
    /// materialising `c * m * p` as a standalone polynomial first.
    ///
    /// This is the bucket's bba-hot-path operation. It is the
    /// equivalent of Singular's `kBucket_Minus_m_Mult_p`.
    ///
    /// Per ADR-018, the caller's ring construction must ensure
    /// `m * p_i` products stay in-range. Debug builds catch violations
    /// via `debug_assert!` inside `MonoTerm::mul`; release builds
    /// silently corrupt the monomial (matching Singular's
    /// `p_ExpVectorAdd` release-mode contract).
    pub fn minus_m_mult_p(&mut self, m: &M, c: F, p: &Poly<F, M, W>) {
        if c.is_zero() || p.is_zero() {
            return;
        }

        // Destination slot: pick the slot for a polynomial of length
        // `p.len()`. On the List backend, `sub_mm_mult_qq_consuming`
        // destructively fuses the existing slot's poly with `-c*m*p`
        // in a single splice-based pass — no fresh `-c*m*p`
        // intermediate poly is ever built. On the Vec backend, the
        // call forwards to the non-destructive `sub_mul_term` which
        // is equivalent to the old `build_neg_cmp` + merge pair.
        //
        // If the slot was empty we start from `Poly::zero()`; the
        // resulting poly is `-c*m*p` (the List variant constructs it
        // by splicing fresh nodes from `p` one-at-a-time into the
        // output chain — same allocation budget as the old
        // `build_neg_cmp`, but skips the intermediate poly's own
        // drop traversal afterward).
        let i = slot_for_len(p.len());
        debug_assert!(i < NUM_SLOTS, "slot overflow: p.len() = {}", p.len());

        let existing = self.slots[i].take().unwrap_or_else(Poly::zero);
        // Per ADR-018, the caller's ring construction must ensure
        // that `m * p[i]` products stay in-range; release builds
        // do not check. Debug builds catch violations inside
        // `MonoTerm::mul` via `debug_assert!`.
        let merged = existing.sub_mm_mult_qq_consuming(c, m, p, &self.ring);
        self.mark_dirty(i);
        if merged.is_zero() {
            // Sum cancelled at this slot; no further work.
            return;
        }
        let target = slot_for_len(merged.len());
        if target == i {
            self.slots[i] = Some(merged);
            return;
        }
        // `merged` no longer fits slot `i` exactly; cascade through
        // `absorb`. The new slot can be strictly larger (lengths
        // grew when subtracting a non-overlapping `c·m·p`) or
        // strictly smaller (cancellation shrank the result below
        // `4^(i-1)`). `absorb` recomputes the slot from the actual
        // merged length and handles both directions.
        self.absorb(merged);
    }

    // ----- Leading term -----

    /// Return the leading term of the bucket sum, or `None` if the
    /// sum is zero.
    ///
    /// On first call after a mutation this scans all non-empty slots
    /// to find the slot with the maximum leading monomial; slots that
    /// share that same leading monomial are merged in, possibly
    /// cancelling to zero (in which case the scan repeats on the
    /// remaining slots). The result is cached; repeated probes are
    /// O(1).
    ///
    /// Despite the `&mut self` receiver, this is logically a query:
    /// it leaves the bucket algebraically equal to its old value. The
    /// mutation is only redistributing the representation across slots
    /// (peeling cancelled leaders, refreshing `dirty` / `lm_cache`).
    /// To actually pop the leader, use [`extract_leading`](Self::extract_leading).
    pub fn leading(&mut self) -> Option<(F, &M)> {
        if self.dirty == 0
            && let Some((c, ref m, _)) = self.lm_cache
        {
            return Some((c, m));
        }

        // Re-scan. We use the algorithm behind Singular's
        // p_kBucketSetLm__T template: pick the slot with the largest
        // leading term; merge any slot whose leader matches into it
        // by summing coefficients; if the sum cancels, peel those
        // leaders off and repeat.
        //
        // Combined scan: a single pass tracks `best` (slot with the
        // current running maximum), `total_c` (summed coeff for all
        // slots matching `best`), and `matching` (slot indices whose
        // leaders equal the running maximum). On encountering a new
        // strictly-larger leader we reset total_c and matching.
        loop {
            let mut best: Option<usize> = None;
            let mut total_c: F = F::zero();
            let mut matching_mask: u32 = 0;
            for (i, slot) in self.slots.iter().enumerate() {
                let Some(p) = slot else { continue };
                if p.is_zero() {
                    continue;
                }
                let (c_i, m_i) = p.leading().unwrap();
                match best {
                    None => {
                        best = Some(i);
                        total_c = c_i;
                        matching_mask = 1u32 << i;
                    }
                    Some(j) => {
                        let (_, mj) = self.slots[j].as_ref().unwrap().leading().unwrap();
                        match m_i.cmp(mj) {
                            std::cmp::Ordering::Greater => {
                                best = Some(i);
                                total_c = c_i;
                                matching_mask = 1u32 << i;
                            }
                            std::cmp::Ordering::Equal => {
                                total_c += c_i;
                                matching_mask |= 1u32 << i;
                            }
                            std::cmp::Ordering::Less => {}
                        }
                    }
                }
            }
            let Some(best_slot) = best else {
                self.dirty = 0;
                self.lm_cache = None;
                return None;
            };

            if !total_c.is_zero() {
                self.dirty = 0;
                // Clone the leader monomial only now (once), for the
                // cache. The single clone avoids the earlier
                // scan/rescan pattern that cloned up front.
                let lead_m = *self.slots[best_slot].as_ref().unwrap().leading().unwrap().1;
                self.lm_cache = Some((total_c, lead_m, best_slot));
                let (c, m, _) = self.lm_cache.as_ref().unwrap();
                return Some((*c, m));
            }

            // Cancellation: peel leaders off every matching slot and
            // rescan. Use the in-place variant to avoid cloning the
            // tail.
            for i in 0..NUM_SLOTS {
                if matching_mask & (1u32 << i) == 0 {
                    continue;
                }
                let p = self.slots[i].as_mut().unwrap();
                p.drop_leading_in_place();
                if p.is_zero() {
                    self.slots[i] = None;
                }
            }
            self.lm_cache = None;
            // fall through to repeat the scan
        }
    }

    /// Pop the leading term of the bucket sum.
    ///
    /// Returns `None` if the bucket is zero. Leaves the bucket
    /// algebraically equal to (old value) − (popped term).
    pub fn extract_leading(&mut self) -> Option<(F, M)> {
        let (c, m) = match self.leading() {
            None => return None,
            Some((c, m)) => (c, *m),
        };

        // Drop the leading term from every slot whose leader equals
        // `m`. Because `leading()` returned `(c, m)` with `c` being
        // the *sum* of those slots' leading coefficients, peeling
        // them all off removes exactly `c * m` from the bucket.
        for i in 0..NUM_SLOTS {
            let Some(p) = self.slots[i].as_mut() else {
                continue;
            };
            if p.is_zero() {
                self.slots[i] = None;
                continue;
            }
            let (_, mi) = p.leading().unwrap();
            if mi.cmp(&m).is_eq() {
                p.drop_leading_in_place();
                if p.is_zero() {
                    self.slots[i] = None;
                }
            }
        }

        // Every slot touched; invalidate everything.
        self.dirty = (1u32 << NUM_SLOTS) - 1;
        self.lm_cache = None;
        Some((c, m))
    }

    /// Whether the bucket's algebraic sum is zero. Equivalent to
    /// `self.leading().is_none()` — it probes the leader and runs
    /// the full scan if slots are dirty.
    pub fn is_zero(&mut self) -> bool {
        self.leading().is_none()
    }

    /// Consume the bucket and return the canonical sum as a single
    /// [`Poly`].
    pub fn into_poly(self) -> Poly<F, M, W> {
        let KBucket { ring, slots, .. } = self;
        let mut acc = Poly::zero();
        for s in slots.into_iter().flatten() {
            if !s.is_zero() {
                acc = acc.add(&s, &ring);
            }
        }
        acc
    }

    // ----- Invariants -----

    /// Panic if any internal invariant is violated. Intended for
    /// `debug_assert!` guards and for tests.
    ///
    /// Invariants:
    /// 1. Each non-empty slot `i` contains a canonical `Poly` with
    ///    `slot_for_len(len) ≤ i` — i.e. the poly's length class
    ///    does not exceed the slot's capacity.
    /// 2. The `lm_cache`, if present, points at a slot whose leading
    ///    monomial equals the cache's monomial.
    pub fn assert_canonical(&self) {
        for (i, slot) in self.slots.iter().enumerate() {
            let Some(p) = slot else { continue };
            p.assert_canonical(&self.ring);
            let cls = slot_for_len(p.len());
            assert!(
                cls <= i,
                "slot {i} holds poly of length {} (class {cls}), capacity {}",
                p.len(),
                slot_capacity(i)
            );
            assert!(
                !p.is_zero(),
                "slot {i} holds a zero-length poly; should be None"
            );
        }
        if let Some((c, m, slot)) = &self.lm_cache {
            assert!(!c.is_zero(), "cached leading coeff must be nonzero");
            // The cached slot's leader should share the cached m
            // (the slot's leader monomial == m). We don't verify the
            // coefficient because lm_cache stores the *sum* across
            // matching slots, not the slot's own coefficient.
            let sp = self
                .slots
                .get(*slot)
                .and_then(|s| s.as_ref())
                .expect("lm_cache slot must be populated");
            let (_, sm) = sp.leading().unwrap();
            assert!(
                sm.cmp(m).is_eq(),
                "lm_cache monomial disagrees with its slot's leader"
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::monomial::{GrevLexTerm, MonoTerm};
    use ark_bls12_381::Fr;
    use ark_ff::One;

    fn mk_ring(nvars: u32) -> Arc<Ring<Fr>> {
        Arc::new(Ring::<Fr>::new(nvars).unwrap())
    }

    fn mono(r: &Ring<Fr>, e: &[u32]) -> GrevLexTerm {
        GrevLexTerm::from(MonoTerm::from_exponents(r, e).unwrap())
    }

    #[test]
    fn new_is_zero() {
        let r = mk_ring(3);
        let mut b = KBucket::<Fr, GrevLexTerm>::new(Arc::clone(&r));
        b.assert_canonical();
        assert!(b.all_slots_empty());
        assert!(b.is_zero());
        assert!(b.leading().is_none());
        let poly = b.into_poly();
        assert!(poly.is_zero());
    }

    #[test]
    fn from_poly_preserves_value() {
        let r = mk_ring(3);
        let p = Poly::from_terms(
            &r,
            vec![
                (Fr::from(3u64), mono(&r, &[2, 1, 0])),
                (Fr::from(7u64), mono(&r, &[1, 0, 1])),
                (Fr::from(1u64), mono(&r, &[0, 0, 2])),
            ],
        );
        let mut b = KBucket::from_poly(Arc::clone(&r), p.clone());
        b.assert_canonical();
        let (c, m) = b.leading().unwrap();
        let (pc, pm) = p.leading().unwrap();
        assert_eq!(c, pc);
        assert_eq!(*m, *pm);
        assert_eq!(b.into_poly(), p);
    }

    #[test]
    fn minus_m_mult_p_into_empty_matches_slow_path() {
        let r = mk_ring(3);
        let q = Poly::from_terms(
            &r,
            vec![
                (Fr::from(4u64), mono(&r, &[1, 1, 0])),
                (Fr::from(5u64), mono(&r, &[0, 0, 1])),
            ],
        );
        let m = mono(&r, &[1, 0, 0]);
        let c: Fr = Fr::from(2u64);

        let mut b = KBucket::<Fr, GrevLexTerm>::new(Arc::clone(&r));
        b.minus_m_mult_p(&m, c, &q);
        b.assert_canonical();

        let slow = Poly::<Fr, GrevLexTerm>::zero().sub_mul_term(c, &m, &q, &r);
        let fast = b.into_poly();
        slow.assert_canonical(&r);
        fast.assert_canonical(&r);
        assert_eq!(slow, fast);
    }

    #[test]
    fn add_then_subtract_cancels() {
        let r = mk_ring(3);
        let q = Poly::from_terms(
            &r,
            vec![
                (Fr::from(4u64), mono(&r, &[1, 1, 0])),
                (Fr::from(5u64), mono(&r, &[0, 0, 1])),
            ],
        );
        let m = mono(&r, &[1, 0, 0]);
        let c: Fr = Fr::from(2u64);
        let neg_c = -c;

        let mut b = KBucket::<Fr, GrevLexTerm>::new(Arc::clone(&r));
        // b += c*m*q  i.e. -(-c)*m*q
        b.minus_m_mult_p(&m, neg_c, &q);
        // b -= c*m*q
        b.minus_m_mult_p(&m, c, &q);
        b.assert_canonical();

        assert!(b.is_zero());
        assert!(b.into_poly().is_zero());
    }

    #[test]
    fn leading_cache_is_used_when_not_dirty() {
        let r = mk_ring(2);
        let p = Poly::from_terms(
            &r,
            vec![
                (Fr::from(3u64), mono(&r, &[2, 0])),
                (Fr::from(4u64), mono(&r, &[1, 1])),
            ],
        );
        let mut b = KBucket::from_poly(Arc::clone(&r), p);
        // First call computes.
        let (c1, m1) = {
            let (c, m) = b.leading().unwrap();
            (c, *m)
        };
        // Dirty must now be clear.
        assert_eq!(b.dirty, 0);
        // Second call: cache hit.
        let (c2, m2) = {
            let (c, m) = b.leading().unwrap();
            (c, *m)
        };
        assert_eq!(c1, c2);
        assert_eq!(m1, m2);
    }

    #[test]
    fn minus_m_mult_p_dirties_slot() {
        let r = mk_ring(2);
        let q = Poly::from_terms(&r, vec![(Fr::from(1u64), mono(&r, &[1, 0]))]);
        let m = mono(&r, &[0, 1]);

        let mut b = KBucket::<Fr, GrevLexTerm>::new(Arc::clone(&r));
        b.minus_m_mult_p(&m, Fr::one(), &q);
        assert_ne!(b.dirty, 0);
        // Force cache; dirty clears.
        b.leading();
        assert_eq!(b.dirty, 0);
        // Another op dirties again.
        b.minus_m_mult_p(&m, Fr::one(), &q);
        assert_ne!(b.dirty, 0);
    }

    #[test]
    fn extract_leading_shrinks_bucket() {
        let r = mk_ring(3);
        let p = Poly::from_terms(
            &r,
            vec![
                (Fr::from(3u64), mono(&r, &[2, 0, 0])),
                (Fr::from(5u64), mono(&r, &[1, 0, 0])),
                (Fr::from(1u64), mono(&r, &[0, 0, 1])),
            ],
        );
        let mut b = KBucket::from_poly(Arc::clone(&r), p.clone());
        let (c, m) = b.extract_leading().unwrap();
        assert_eq!(c, Fr::from(3u64));
        assert_eq!(m, mono(&r, &[2, 0, 0]));
        let remainder = b.into_poly();
        let expected = Poly::from_terms(
            &r,
            vec![
                (Fr::from(5u64), mono(&r, &[1, 0, 0])),
                (Fr::from(1u64), mono(&r, &[0, 0, 1])),
            ],
        );
        assert_eq!(remainder, expected);
    }

    #[test]
    fn cascade_up_through_multiple_slots() {
        // Seed with many tiny single-term ops so the cascade fires.
        let r = mk_ring(3);
        let mut b = KBucket::<Fr, GrevLexTerm>::new(Arc::clone(&r));
        // Add 20 distinct one-term polys of length 1 each via
        // minus_m_mult_p. Each goes into slot 0; cascading should
        // push the total up into slot 2 (log4(20) ≈ 2.2 -> slot 3).
        let m_one = GrevLexTerm::one(&r);
        for i in 1u32..=20 {
            let q = Poly::from_terms(
                &r,
                vec![(Fr::from(1u64), mono(&r, &[i % 5, (i / 5) % 5, 0]))],
            );
            // We want to accumulate +q, i.e. -(-1)*1*q.
            b.minus_m_mult_p(&m_one, -Fr::one(), &q);
        }
        b.assert_canonical();
        // The bucket's total must equal the naive sum.
        let mut expected = Poly::<Fr, GrevLexTerm>::zero();
        for i in 1u32..=20 {
            let q = Poly::from_terms(
                &r,
                vec![(Fr::from(1u64), mono(&r, &[i % 5, (i / 5) % 5, 0]))],
            );
            expected = expected.add(&q, &r);
        }
        let got = b.into_poly();
        expected.assert_canonical(&r);
        got.assert_canonical(&r);
        assert_eq!(got, expected);
    }

    #[test]
    fn cascade_shrinks_on_cancel() {
        // Regression for the geobucket cascade invariant: when a
        // `minus_m_mult_p` cancels terms out of slot `i`, the merged
        // result can land in a strictly smaller slot. Prior to the
        // fix, an upward-only `debug_assert!(target > i)` panicked
        // with "sub_mm_mult_qq shrank into smaller slot".
        //
        // Setup: slot 1 holds a length-4 poly (a + b + c + d) where
        // `slot_for_len(4) = 1`. Subtracting (b + c + d) — also a
        // slot-1 poly — leaves length-1 `a`, which belongs in slot 0.
        let r = mk_ring(2);
        let mut b = KBucket::<Fr, GrevLexTerm>::new(Arc::clone(&r));
        let one = GrevLexTerm::one(&r);
        let p1 = Poly::from_terms(
            &r,
            vec![
                (Fr::from(1u64), mono(&r, &[3, 0])),
                (Fr::from(1u64), mono(&r, &[2, 0])),
                (Fr::from(1u64), mono(&r, &[1, 0])),
                (Fr::from(1u64), mono(&r, &[0, 1])),
            ],
        );
        // Bucket += p1 (lands in slot 1).
        b.minus_m_mult_p(&one, -Fr::one(), &p1);
        b.assert_canonical();
        assert!(b.slots[1].is_some(), "p1 (len 4) should populate slot 1");
        // Subtract (x^2 + x + y), also length 3 → slot 1. The merge
        // is `existing.sub_mm_mult_qq(1, 1, p2)` against slot 1's
        // contents. Result: x^3 (length 1) which slot_for_len maps
        // to slot 0. The cascade must place it there.
        let p2 = Poly::from_terms(
            &r,
            vec![
                (Fr::from(1u64), mono(&r, &[2, 0])),
                (Fr::from(1u64), mono(&r, &[1, 0])),
                (Fr::from(1u64), mono(&r, &[0, 1])),
            ],
        );
        b.minus_m_mult_p(&one, Fr::one(), &p2); // bucket -= p2
        b.assert_canonical();
        // Final algebraic value: p1 - p2 = x^3.
        let got = b.into_poly();
        let expected = Poly::from_terms(&r, vec![(Fr::from(1u64), mono(&r, &[3, 0]))]);
        assert_eq!(got, expected);
    }

    #[test]
    fn is_zero_agrees_with_into_poly() {
        let r = mk_ring(2);
        let mut b = KBucket::<Fr, GrevLexTerm>::new(Arc::clone(&r));
        let p = Poly::from_terms(&r, vec![(Fr::from(2u64), mono(&r, &[1, 0]))]);
        b.minus_m_mult_p(&GrevLexTerm::one(&r), Fr::from(3u64), &p); // -3*1*p = -3p
        b.minus_m_mult_p(&GrevLexTerm::one(&r), -Fr::from(3u64), &p); // +3p
        let zero = b.is_zero();
        let poly = b.into_poly();
        assert_eq!(zero, poly.is_zero());
        assert!(zero);
    }

    #[test]
    fn leading_cancels_across_slots() {
        // Force a case where two slots' leading monomials coincide
        // and cancel: slot A has leader c*m, slot B has leader
        // (-c)*m. leading() must peel both off and expose the next
        // monomial.
        let r = mk_ring(2);
        let mut b = KBucket::<Fr, GrevLexTerm>::new(Arc::clone(&r));
        let p1 = Poly::from_terms(
            &r,
            vec![
                (Fr::from(3u64), mono(&r, &[2, 0])),
                (Fr::from(1u64), mono(&r, &[0, 1])),
            ],
        );
        let p2 = Poly::from_terms(
            &r,
            vec![
                (-Fr::from(3u64), mono(&r, &[2, 0])),
                (Fr::from(2u64), mono(&r, &[1, 0])),
            ],
        );
        // Place p1 in slot 1 (len 2 → slot 1), then p2 also wants
        // slot 1. Their sum goes up a level (len probably 2 or 3).
        // Either way the leader `3*x^2` must cancel against the
        // `-3*x^2`. We test by adding both as "minus_m_mult_p" with
        // m = 1 and c = -1 (so -(-1)*1*pk = +pk).
        let one = GrevLexTerm::one(&r);
        let neg1 = -Fr::one();
        b.minus_m_mult_p(&one, neg1, &p1);
        b.minus_m_mult_p(&one, neg1, &p2);
        b.assert_canonical();

        let sum = p1.add(&p2, &r);
        sum.assert_canonical(&r);
        if sum.is_zero() {
            assert!(b.is_zero());
        } else {
            let (exp_c, exp_m) = sum.leading().unwrap();
            let (c, m) = b.leading().unwrap();
            assert_eq!(c, exp_c);
            assert_eq!(*m, *exp_m);
        }
        assert_eq!(b.into_poly(), sum);
    }

    #[test]
    fn slot_for_len_matches_ceil_log4() {
        assert_eq!(slot_for_len(0), 0);
        assert_eq!(slot_for_len(1), 0);
        assert_eq!(slot_for_len(2), 1);
        assert_eq!(slot_for_len(4), 1);
        assert_eq!(slot_for_len(5), 2);
        assert_eq!(slot_for_len(16), 2);
        assert_eq!(slot_for_len(17), 3);
        assert_eq!(slot_for_len(64), 3);
        assert_eq!(slot_for_len(65), 4);
        assert_eq!(slot_for_len(256), 4);
    }
}
