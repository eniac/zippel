//! Heap-based Monagan-Pearce reducer.
//!
//! See `~/ark_gb/docs/design-decisions.md` ADR-008 for the
//! design rationale and the Singular / FLINT / mathicgb
//! comparison that motivated this architecture.
//!
//! # Status — Phase 1 (scaffold only)
//!
//! This module currently contains only the data-structure
//! definitions for the reducer:
//!
//! * [`Reducer`] — one in-flight reducer (a polynomial `g_i`,
//!   the multiplier monomial `m_i`, the pre-negated
//!   coefficient `c_i`, the current term index `j_i`, and the
//!   sugar contribution).
//! * [`HeapNode`] — a max-heap entry by degrevlex, carrying
//!   the cached comparison key and a back-reference to the
//!   reducer slab index. The cached key is the packed
//!   monomial `m_i * g_i.terms[j_i]` already XOR'd against
//!   the ring's `cmp_flip_mask`, so plain lex compare on
//!   `[u64; 4]` is the correct max-heap ordering and the
//!   comparator needs no `&Ring` indirection.
//! * [`ReducerHeap`] — the full reducer state for one in-progress
//!   reduction: a slab of [`Reducer`]s plus a max-heap of
//!   [`HeapNode`]s. Public API is just construction at this
//!   phase.
//!
//! Phases 2-7 (per ADR-008's migration plan) will land the
//! actual reduction algorithm: heap operations, pop-with-
//! cancellation, lazy divisor addition, survivor materialisation,
//! integration into [`crate::bba::reduce_lobject`] behind a
//! feature flag, staging-validation, and (if successful)
//! retirement of the geobucket reducer.

use crate::field::Field;
use crate::monomial::{MonoTerm, Monomial};
use crate::poly::{Poly, PolyCursor};
use crate::ring::Ring;
use std::collections::BinaryHeap;
use std::sync::Arc;

/// One in-flight reducer in a [`ReducerHeap`].
///
/// Represents the pending product `coeff * multiplier * poly`,
/// of which the heap currently has term `index` queued. A new
/// reducer is added with `index = 0` (its leading term, which
/// by construction matches and cancels the partial reduction's
/// current leader); subsequent pops advance `index` past the
/// emitted term so the next term is queued for ordering.
///
/// `coeff` is **pre-negated** at insertion time so that when
/// the heap pops the chain `(old_leader, new_reducer.term_0)`
/// and sums their coefficients, the cancellation drops out
/// naturally without sign tracking inside the heap.
///
/// The `Reducer` borrows its source `poly` from the [`SBasis`];
/// lifetime `'a` ties the heap to the borrow of that basis for
/// the duration of one reduction.
#[derive(Debug)]
pub struct Reducer<'a, F: Field + Copy, M: Monomial<F, W>, const W: usize = 4> {
    /// Source polynomial `g_i`. Borrowed from the basis for
    /// the reduction's lifetime.
    pub poly: &'a Poly<F, M, W>,
    /// Multiplier monomial `m_i = lm(LObject) / lm(g_i)` at the
    /// time this reducer was added.
    pub multiplier: MonoTerm<W>,
    /// Pre-negated multiplier coefficient
    /// `c_i = -leader_coeff(LObject) / lc(g_i)`. With monic
    /// basis elements `lc(g_i) == 1`, this simplifies to
    /// `-leader_coeff`.
    pub coeff: F,
    /// Cursor into `poly` positioned at the next term not yet
    /// queued in the heap. Built from `poly.cursor()` (optionally
    /// pre-advanced, e.g. when a freshly added divisor skips its
    /// leading term — see the `index = 1` trick in
    /// [`ReducerHeap::reduce_to_normal_form`]). Advances by one
    /// for every term of this reducer popped off the heap.
    ///
    /// Replaces the pre-cursor `index: usize` field — see ADR-014.
    /// Using a cursor instead of a random-access index makes the
    /// reducer oblivious to `Poly`'s backing storage (parallel
    /// vectors vs. linked list).
    pub cursor: PolyCursor<'a, F, M, W>,
    /// Sugar contribution: `g_i.lm_deg() + multiplier.total_deg()`.
    /// Used to compute the LObject's running sugar as the
    /// max over all in-flight reducers (plus the initial sugar).
    pub sugar: u32,
}

/// A node in the max-heap by degrevlex.
///
/// Two fields:
/// * `cmp_key` is the packed monomial of the currently-queued
///   term `multiplier * g_i.terms[index]`, **already XOR'd
///   against the ring's `cmp_flip_mask`**. Lex compare of the
///   four `u64` words (MSB first) is the correct degrevlex max
///   ordering, so `Ord` on `HeapNode` reduces to a plain `cmp`
///   on the `[u64; 4]` cmp_key. This eliminates the need to
///   pass `&Ring` into the heap's internal comparator.
/// * `reducer_idx` is an index into the [`ReducerHeap`]'s
///   slab of [`Reducer`]s, identifying which in-flight reducer
///   this term belongs to.
///
/// At most one `HeapNode` per `Reducer` lives in the heap at
/// any time (FLINT's invariant): when we pop a node, we either
/// advance the source's `index` and push the next term back,
/// or the source has been exhausted and no new node is pushed.
#[derive(Debug, Clone)]
pub struct HeapNode<const W: usize = 4> {
    /// Order-prefix returned by `M::cmp_key`. Lex-compared first.
    /// For DegRevLex this is `0`; for orders that prepend a block
    /// metric (e.g. `OddElimTerm`'s elim-block-sum) this carries
    /// the block metric. See `Monomial::cmp_key`.
    pub pre_key: u64,
    /// Packed monomial transformed by `M::cmp_key` so that lex
    /// compare matches `M::cmp` (after `pre_key` resolves any
    /// block metric). For DegRevLex this is `packed XOR
    /// ring.cmp_flip_mask`.
    pub cmp_key: [u64; W],
    /// Index into the slab of [`Reducer`]s.
    pub reducer_idx: usize,
}

impl<const W: usize> PartialEq for HeapNode<W> {
    fn eq(&self, other: &Self) -> bool {
        self.pre_key == other.pre_key && self.cmp_key == other.cmp_key
    }
}

impl<const W: usize> Eq for HeapNode<W> {}

impl<const W: usize> PartialOrd for HeapNode<W> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<const W: usize> Ord for HeapNode<W> {
    /// Lex compare on `(pre_key, cmp_key)`. The `Monomial::cmp_key`
    /// contract guarantees this matches `M::cmp` on the underlying
    /// monomials (DegRevLex for `GrevLexTerm`; elim-block then
    /// DegRevLex for `OddElimTerm`).
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.pre_key
            .cmp(&other.pre_key)
            .then_with(|| self.cmp_key.iter().rev().cmp(other.cmp_key.iter().rev()))
    }
}

/// The state of one in-progress polynomial reduction.
///
/// Holds the slab of in-flight reducers and the max-heap of
/// pending product terms. One `ReducerHeap` is created per
/// LObject being reduced; it lives for the duration of that
/// reduction and is dropped (or consumed into a survivor `Poly`)
/// when the reduction terminates.
///
/// Lifetime `'a` ties this state to the borrow of the
/// [`SBasis`] whose polynomials the [`Reducer`]s reference.
#[derive(Debug)]
pub struct ReducerHeap<
    'a,
    F: Field + Copy + Send + Sync,
    M: Monomial<F, W> + From<MonoTerm<W>>,
    const W: usize = 4,
> {
    /// Owning ring reference. All monomials in the heap belong
    /// to this ring.
    ring: Arc<Ring<F, W>>,
    /// Slab of in-flight reducers. Indexed by [`HeapNode::reducer_idx`].
    /// Grows monotonically — a reducer is never removed from the
    /// slab once added (its tail may be exhausted, in which case
    /// no `HeapNode` references it any more, but its slot stays).
    reducers: Vec<Reducer<'a, F, M, W>>,
    /// Max-heap of pending product terms, ordered by degrevlex
    /// via [`HeapNode::cmp_key`]. The std-library `BinaryHeap` is
    /// a max-heap and our [`HeapNode::cmp`] implements degrevlex
    /// via lex compare on the cached `cmp_key`, so push/pop/peek
    /// give the right semantics directly.
    heap: BinaryHeap<HeapNode<W>>,
    /// Running sugar. Initialised at construction; updated to
    /// `max(self.sugar, reducer.sugar)` on each `push_reducer`.
    sugar: u32,
}

impl<'a, F: Field + Copy + Send + Sync, M: Monomial<F, W> + From<MonoTerm<W>>, const W: usize>
    ReducerHeap<'a, F, M, W>
{
    /// Construct an empty reducer state for a reduction starting
    /// at `initial_sugar`. Adding the LObject's polynomial as the
    /// first reducer (with `multiplier = 1`, `coeff = 1`) is the
    /// caller's responsibility (deferred to phase 4).
    pub fn new(ring: Arc<Ring<F, W>>, initial_sugar: u32) -> Self {
        Self {
            ring,
            reducers: Vec::new(),
            heap: BinaryHeap::new(),
            sugar: initial_sugar,
        }
    }

    /// Borrow the ring this heap operates over.
    #[inline]
    pub fn ring(&self) -> &Arc<Ring<F, W>> {
        &self.ring
    }

    /// Current sugar of the in-progress reduction. Equal to
    /// `max(initial_sugar, max over reducers of reducer.sugar)`.
    #[inline]
    pub fn sugar(&self) -> u32 {
        self.sugar
    }

    /// Number of in-flight reducers currently in the slab. Equal
    /// to the number of `push_reducer` calls so far (no removal).
    #[inline]
    pub fn reducer_count(&self) -> usize {
        self.reducers.len()
    }

    /// Number of heap nodes currently in flight. Each in-flight
    /// reducer contributes at most one node (FLINT's invariant);
    /// a node may be missing if the reducer's tail has been
    /// exhausted by repeated pop+advance.
    #[inline]
    pub fn heap_len(&self) -> usize {
        self.heap.len()
    }

    /// Whether the heap is empty. Equivalent to `self.heap_len() == 0`.
    /// When this returns true the reduction has terminated; either
    /// the LObject reduced to zero (no survivor), or the survivor
    /// has already been fully drained into a `Poly`.
    #[inline]
    pub fn heap_is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    // ----- Heap operations (phase 2) -----
    //
    // The heap is a max-heap by degrevlex via HeapNode::cmp on the
    // cached cmp_key. The underlying BinaryHeap is std-library;
    // these methods are thin wrappers that document the role of
    // each operation in the Monagan-Pearce reducer's lifecycle.

    /// Push a heap node. The node carries the pre-XOR'd cmp_key
    /// for the term `multiplier * g.terms[index]` for some reducer
    /// in the slab; the caller is responsible for constructing it
    /// (typically `Self::push_term`, deferred to phase 4 where the
    /// reducer-construction surface lands).
    #[inline]
    pub fn push_node(&mut self, node: HeapNode<W>) {
        self.heap.push(node);
    }

    /// Look at the maximum heap node without removing it. Returns
    /// `None` if the heap is empty.
    ///
    /// Used by [`pop_with_cancellation`](Self::pop_with_cancellation)
    /// (phase 3) to peek at successive max entries and detect
    /// whether they share the leading `cmp_key` — the signal that
    /// terms cancel and need to be summed.
    #[inline]
    pub fn peek_max(&self) -> Option<&HeapNode<W>> {
        self.heap.peek()
    }

    /// Remove and return the maximum heap node. Returns `None`
    /// if the heap is empty.
    ///
    /// In Monagan-Pearce, this corresponds to taking the next
    /// pending product to consider for emission. The caller must
    /// then either advance the source reducer's index (and push
    /// the next term back onto the heap) or, if the source's
    /// tail is exhausted, leave the slot vacant.
    #[inline]
    pub fn pop_max(&mut self) -> Option<HeapNode<W>> {
        self.heap.pop()
    }

    // ----- Reducer management + cancellation pop (phase 3) -----

    /// Add a reducer to the slab and queue its leading term onto
    /// the heap. Returns the slab index of the new reducer.
    ///
    /// If `reducer.poly` is the zero polynomial (no terms past
    /// `index`), the reducer is added to the slab but no heap node
    /// is pushed — the reducer is effectively dead on arrival.
    /// This is consistent with FLINT's "at most one heap node per
    /// reducer" invariant: an exhausted reducer has zero in flight.
    ///
    /// Updates the running sugar to `max(self.sugar, reducer.sugar)`.
    pub fn push_reducer(&mut self, reducer: Reducer<'a, F, M, W>) -> usize {
        let idx = self.reducers.len();
        self.sugar = self.sugar.max(reducer.sugar);
        self.reducers.push(reducer);
        // Queue the leading term if non-empty.
        self.push_current_term(idx);
        idx
    }

    /// Compute the cmp_key of the term currently at the front of
    /// `reducers[reducer_idx]` (i.e. `multiplier * poly.terms[index]`
    /// XOR'd against the ring's cmp_flip_mask) and push a HeapNode
    /// for it. No-op if the reducer is exhausted (`index >= poly.len`).
    ///
    /// Per ADR-018, the caller's ring construction must ensure
    /// `multiplier * poly.terms[index]` products stay in-range;
    /// release builds of `MonoTerm::mul` do not check.
    fn push_current_term(&mut self, reducer_idx: usize) {
        let r = &self.reducers[reducer_idx];
        let Some((_c, m)) = r.cursor.term() else {
            return;
        };
        let term_mono = r.multiplier.mul(m.as_mono_term(), &self.ring);
        let (pre_key, cmp_key) = M::cmp_key(&term_mono, &self.ring);
        self.heap.push(HeapNode {
            pre_key,
            cmp_key,
            reducer_idx,
        });
    }

    /// Advance the named reducer past its current term and queue
    /// the next term onto the heap (if any).
    fn advance_reducer(&mut self, reducer_idx: usize) {
        self.reducers[reducer_idx].cursor.advance();
        self.push_current_term(reducer_idx);
    }

    /// Drive a full reduction to normal form against an arbitrary
    /// divisor-source.
    ///
    /// Repeatedly pops the next non-cancelled leader; for each
    /// leader, calls `find_divisor` with the leader's monomial.
    /// If `find_divisor` returns `Some((g, g_sugar))`, that
    /// polynomial's leading monomial divides the leader (the
    /// callback's contract), so we add `g` as a new reducer with
    /// `multiplier = leader_mono / lm(g)` and pre-negated coeff
    /// `-leader_coeff / lc(g)`. The next pop will (by construction)
    /// cancel the leader against the new reducer's first term and
    /// drive the reduction forward. If `find_divisor` returns
    /// `None`, the leader is irreducible and joins the survivor
    /// poly's term sequence.
    ///
    /// Assumes basis polynomials are monic (lc = 1), per
    /// ark_gb's bba convention. With this assumption `lc(g) = 1`,
    /// so the new reducer's coeff is just `-leader_coeff`.
    ///
    /// Consumes self and returns `(survivor_poly, final_sugar)`.
    /// `survivor_poly` is `Poly::zero()` if the LObject reduced
    /// to zero. `final_sugar` is the running sugar after all
    /// reducers were added, useful for the caller to update the
    /// LObject's sugar metadata.
    pub fn reduce_to_normal_form<DF>(mut self, mut find_divisor: DF) -> (Poly<F, M, W>, u32)
    where
        DF: FnMut(&MonoTerm<W>) -> Option<(&'a Poly<F, M, W>, u32)>,
    {
        let mut survivor_terms: Vec<(F, M)> = Vec::new();

        while let Some((c, m)) = self.pop_with_cancellation() {
            match find_divisor(&m) {
                Some((g, g_sugar)) => {
                    let g_lm = g
                        .leading()
                        .expect("find_divisor returned non-zero divisor")
                        .1;
                    let multiplier = m
                        .div(g_lm.as_mono_term(), &self.ring)
                        .expect("find_divisor's contract: lm(g) divides m");
                    debug_assert_eq!(g.lm_coeff(), F::one(), "basis polynomials must be monic");
                    let coeff = -c;
                    let m_deg = multiplier.total_deg();
                    let new_sugar = g_sugar.saturating_add(m_deg);
                    // **Cursor pre-advanced by one**, not at leading:
                    // the divisor's leading term is implicitly
                    // cancelled by the act of emitting `(c, m)` from
                    // pop_with_cancellation and then choosing to
                    // reduce by g. The leading term
                    // `coeff * multiplier * g.terms[0]` would equal
                    // `-c * m`, exactly the inverse of the popped
                    // leader. Starting the cursor at the leading
                    // term and letting the heap cancel it would
                    // require us to NOT have popped the leader in
                    // the first place, which is incompatible with
                    // the streaming pop-emit semantics. Instead, we
                    // skip the implicit-cancellation leading term
                    // and only queue the divisor's tail contribution
                    // `coeff * multiplier * g.terms[1..]`. This is
                    // the same trick FLINT uses in
                    // `divrem_monagan_pearce.c` (the new heap node
                    // for a freshly-found divisor is inserted with
                    // `j = 1`, not `j = 0`).
                    let mut tail_cursor = g.cursor();
                    tail_cursor.advance();
                    self.push_reducer(Reducer {
                        poly: g,
                        multiplier,
                        coeff,
                        cursor: tail_cursor,
                        sugar: new_sugar,
                    });
                    // Loop continues with the divisor's tail merged
                    // into the heap.
                }
                None => {
                    // Irreducible leader: emit into the survivor.
                    survivor_terms.push((c, M::from(m)));
                }
            }
        }

        let survivor = if survivor_terms.is_empty() {
            Poly::zero()
        } else {
            Poly::from_descending_terms_unchecked(&self.ring, survivor_terms)
        };
        (survivor, self.sugar)
    }

    /// Pop the next non-cancelled (coefficient, monomial) leader.
    /// Returns `None` when the heap is empty (the reduction has
    /// terminated; if the LObject's poly was the only reducer,
    /// then we've drained it; if reducers were added along the
    /// way and the chain cancelled to zero everywhere, the LObject
    /// reduced to zero).
    ///
    /// Algorithm: pop the max; if the next pops share the same
    /// `cmp_key`, they're contributing to the same monomial and
    /// their coefficients sum. Each contributing reducer's index
    /// is advanced past its emitted term. If the resulting sum is
    /// zero, the chain cancelled and we recurse on the next leader;
    /// if non-zero, that's the leader the caller wants.
    pub fn pop_with_cancellation(&mut self) -> Option<(F, MonoTerm<W>)> {
        loop {
            let max_node = self.heap.pop()?;
            // Collect the contributing reducer indices and compute
            // the monomial value (the same for all contributors,
            // by the same-key invariant).
            let chain_pre = max_node.pre_key;
            let chain_key = max_node.cmp_key;
            let max_idx = max_node.reducer_idx;
            let r = &self.reducers[max_idx];
            // Recover the actual monomial and its coefficient from the
            // reducer's cursor. The cmp_key is `M::cmp_key`-derived,
            // so unpacking could get us back, but reading through the
            // cursor is simpler and works on both Poly backends.
            let (r_c, r_m) = r.cursor.term().expect("just pushed; live cursor");
            let mono = r.multiplier.mul(r_m.as_mono_term(), &self.ring);
            let mut total_coeff = r.coeff * r_c;

            // Advance the max contributor.
            let mut to_advance: Vec<usize> = Vec::with_capacity(2);
            to_advance.push(max_idx);

            // Drain any equal-key entries.
            while let Some(next) = self.heap.peek() {
                if next.pre_key != chain_pre || next.cmp_key != chain_key {
                    break;
                }
                let next_node = self.heap.pop().unwrap();
                let nr = &self.reducers[next_node.reducer_idx];
                let (nr_c, _nr_m) = nr.cursor.term().expect("just pushed; live cursor");
                let next_coeff = nr.coeff * nr_c;
                total_coeff += next_coeff;
                to_advance.push(next_node.reducer_idx);
            }

            // Advance every contributor past its emitted term.
            for &idx in &to_advance {
                self.advance_reducer(idx);
            }

            if !total_coeff.is_zero() {
                return Some((total_coeff, mono));
            }
            // total_coeff == 0: complete cancellation; loop and
            // try the next leader.
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

    #[test]
    fn empty_reducer_heap_constructs() {
        let r = mk_ring(3);
        let h = ReducerHeap::<Fr, GrevLexTerm>::new(Arc::clone(&r), 0);
        assert_eq!(h.reducer_count(), 0);
        assert_eq!(h.heap_len(), 0);
        assert_eq!(h.sugar(), 0);
    }

    #[test]
    fn initial_sugar_is_preserved() {
        let r = mk_ring(3);
        let h = ReducerHeap::<Fr, GrevLexTerm>::new(Arc::clone(&r), 17);
        assert_eq!(h.sugar(), 17);
    }

    #[test]
    fn heap_node_ord_matches_lex_on_cmp_key() {
        // cmp_key is the XOR-flipped packed monomial; lex compare
        // on the four u64 words MSB-first IS the degrevlex order.
        // Verify our Ord impl on HeapNode produces the right result
        // on hand-crafted keys.
        let a = HeapNode {
            pre_key: 0,
            cmp_key: [0, 0, 0, 0xFF_00_00_00_00_00_00_00],
            reducer_idx: 0,
        };
        let b = HeapNode {
            pre_key: 0,
            cmp_key: [0, 0, 0, 0x80_00_00_00_00_00_00_00],
            reducer_idx: 1,
        };
        // a's top byte is 0xFF, b's is 0x80 → a > b.
        assert!(a > b);
        assert!(b < a);
        assert_ne!(a, b);
    }

    #[test]
    fn heap_node_ord_walks_words_msb_first() {
        // Two nodes where word 3 differs: that's the only word
        // that should matter.
        let a = HeapNode {
            pre_key: 0,
            cmp_key: [0xFFFF, 0, 0, 0x10_00_00_00_00_00_00_00],
            reducer_idx: 0,
        };
        let b = HeapNode {
            pre_key: 0,
            cmp_key: [0, 0, 0, 0x20_00_00_00_00_00_00_00],
            reducer_idx: 1,
        };
        // word 3: a=0x10... < b=0x20...; lower words don't matter
        assert!(a < b);
    }

    #[test]
    fn heap_node_ord_falls_through_to_lower_words() {
        // word 3 equal; difference in word 0.
        let a = HeapNode {
            pre_key: 0,
            cmp_key: [5, 0, 0, 0x42_00_00_00_00_00_00_00],
            reducer_idx: 0,
        };
        let b = HeapNode {
            pre_key: 0,
            cmp_key: [3, 0, 0, 0x42_00_00_00_00_00_00_00],
            reducer_idx: 1,
        };
        assert!(a > b);
    }

    #[test]
    fn heap_node_eq_ignores_reducer_idx() {
        // Two nodes with the same cmp_key but different
        // reducer_idx are PartialEq-equal (same monomial, two
        // reducers contributing). This is the condition that
        // pop-with-cancellation will look for to chain entries.
        let a = HeapNode {
            pre_key: 0,
            cmp_key: [1, 2, 3, 4],
            reducer_idx: 0,
        };
        let b = HeapNode {
            pre_key: 0,
            cmp_key: [1, 2, 3, 4],
            reducer_idx: 7,
        };
        assert_eq!(a, b);
    }

    // ----- Phase 2: heap operations -----

    /// Helper: build a deterministic pseudo-random sequence of
    /// HeapNodes with diverse cmp_keys for property testing.
    /// Keys are spread across all four words to exercise the
    /// MSB-first lex-compare path.
    fn pseudo_random_nodes(n: usize, seed: u64) -> Vec<HeapNode> {
        let mut state = seed;
        let mut step = || {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            state
        };
        (0..n)
            .map(|i| HeapNode {
                pre_key: 0,
                cmp_key: [step(), step(), step(), step()],
                reducer_idx: i,
            })
            .collect()
    }

    /// Slow reference: pop the max repeatedly via sort.
    fn slow_drain_descending(mut nodes: Vec<HeapNode>) -> Vec<HeapNode> {
        nodes.sort();
        nodes.reverse();
        nodes
    }

    #[test]
    fn empty_heap_pop_and_peek_return_none() {
        let r = mk_ring(3);
        let mut h = ReducerHeap::<Fr, GrevLexTerm>::new(Arc::clone(&r), 0);
        assert!(h.heap_is_empty());
        assert!(h.peek_max().is_none());
        assert!(h.pop_max().is_none());
        assert!(h.heap_is_empty());
    }

    #[test]
    fn push_then_pop_single_node() {
        let r = mk_ring(3);
        let mut h = ReducerHeap::<Fr, GrevLexTerm>::new(Arc::clone(&r), 0);
        let n = HeapNode {
            pre_key: 0,
            cmp_key: [1, 2, 3, 4],
            reducer_idx: 42,
        };
        h.push_node(n.clone());
        assert_eq!(h.heap_len(), 1);
        assert!(!h.heap_is_empty());
        assert_eq!(h.peek_max(), Some(&n));
        assert_eq!(h.pop_max(), Some(n));
        assert!(h.heap_is_empty());
    }

    #[test]
    fn push_pop_drains_in_descending_order() {
        // Property test against the slow sort-based reference.
        // For each seed, push N nodes onto the heap and verify
        // that draining pops them in descending degrevlex order
        // (the same order the slow reference produces).
        let r = mk_ring(3);
        for &seed in &[
            0x1234_5678_9abc_def0u64,
            0xdead_beef_cafe_babe,
            1,
            2,
            0xff_ff,
        ] {
            for &n in &[1usize, 2, 5, 16, 64, 200] {
                let nodes = pseudo_random_nodes(n, seed);
                let mut h = ReducerHeap::<Fr, GrevLexTerm>::new(Arc::clone(&r), 0);
                for node in &nodes {
                    h.push_node(node.clone());
                }
                assert_eq!(h.heap_len(), n);
                let mut got = Vec::with_capacity(n);
                while let Some(top) = h.pop_max() {
                    got.push(top);
                }
                assert!(h.heap_is_empty());
                let expected = slow_drain_descending(nodes);
                assert_eq!(
                    got.iter().map(|n| n.cmp_key).collect::<Vec<_>>(),
                    expected.iter().map(|n| n.cmp_key).collect::<Vec<_>>(),
                    "drain order mismatch for seed {seed:#x}, n = {n}"
                );
            }
        }
    }

    #[test]
    fn peek_matches_pop() {
        // After every push, peek_max should report the same cmp_key
        // that the next pop_max returns.
        let r = mk_ring(3);
        let nodes = pseudo_random_nodes(50, 0xfeed_face);
        let mut h = ReducerHeap::<Fr, GrevLexTerm>::new(Arc::clone(&r), 0);
        for node in &nodes {
            h.push_node(node.clone());
            let peek_key = h.peek_max().unwrap().cmp_key;
            // Don't actually pop — instead, verify that on the
            // *next* pop later we'd see this key. Take a snapshot
            // by cloning the heap state for the check.
            let mut h2 = ReducerHeap::<Fr, GrevLexTerm>::new(Arc::clone(&r), 0);
            // Re-build h2 from the underlying BinaryHeap's iterator
            // to avoid moving h.
            for n2 in h.heap.iter() {
                h2.push_node(n2.clone());
            }
            let popped = h2.pop_max().unwrap();
            assert_eq!(popped.cmp_key, peek_key);
        }
    }

    #[test]
    fn interleaved_push_and_pop_drains_correctly() {
        // Push some, pop some, push more, drain — verifies the
        // heap can absorb pops in the middle of building (the
        // lifecycle that pop-with-cancellation will exercise).
        let r = mk_ring(3);
        let nodes = pseudo_random_nodes(30, 0xa1b2_c3d4);
        let mut h = ReducerHeap::<Fr, GrevLexTerm>::new(Arc::clone(&r), 0);

        // Push first 20.
        for n in &nodes[..20] {
            h.push_node(n.clone());
        }
        // Pop 5 (saving them).
        let mut popped: Vec<HeapNode> = (0..5).map(|_| h.pop_max().unwrap()).collect();
        // Push remaining 10.
        for n in &nodes[20..30] {
            h.push_node(n.clone());
        }
        // Drain.
        while let Some(top) = h.pop_max() {
            popped.push(top);
        }

        // Total nodes seen = 30; their cmp_keys, when sorted
        // descending, should match the input sorted descending.
        assert_eq!(popped.len(), 30);
        let mut got_keys: Vec<[u64; 4]> = popped.iter().map(|n| n.cmp_key).collect();
        got_keys.sort();
        let mut want_keys: Vec<[u64; 4]> = nodes.iter().map(|n| n.cmp_key).collect();
        want_keys.sort();
        assert_eq!(got_keys, want_keys);
    }

    // ----- Phase 3: push_reducer + pop_with_cancellation -----

    use crate::monomial::Monomial;
    use crate::poly::Poly;

    fn mono(r: &Ring<Fr>, e: &[u32]) -> GrevLexTerm {
        GrevLexTerm::from(MonoTerm::from_exponents(r, e).unwrap())
    }

    /// Helper: collect the full output of pop_with_cancellation
    /// into a Vec until the heap drains. Used as a "drive the
    /// reducer to completion" pattern in tests.
    fn drain_with_cancellation<'a>(
        h: &mut ReducerHeap<'a, Fr, GrevLexTerm>,
    ) -> Vec<(Fr, MonoTerm)> {
        let mut out = Vec::new();
        while let Some(pair) = h.pop_with_cancellation() {
            out.push(pair);
        }
        out
    }

    #[test]
    fn single_reducer_no_cancellation_emits_all_terms() {
        // Push one reducer (multiplier=1, coeff=1) over a 3-term
        // poly. Drain pop_with_cancellation; should emit each term
        // in descending order with coeff matching the source.
        let r = mk_ring(3);
        let one = MonoTerm::one(&r);
        let p = Poly::from_terms(
            &r,
            vec![
                (Fr::from(5u64), mono(&r, &[3, 0, 0])), // x_0^3
                (Fr::from(2u64), mono(&r, &[1, 1, 0])), // x_0 x_1
                (Fr::from(1u64), mono(&r, &[0, 0, 2])), // x_2^2
            ],
        );
        let mut h = ReducerHeap::<Fr, GrevLexTerm>::new(Arc::clone(&r), 0);
        h.push_reducer(Reducer {
            poly: &p,
            multiplier: one,
            coeff: Fr::one(),
            cursor: p.cursor(),
            sugar: 3,
        });
        assert_eq!(h.sugar(), 3);

        let out = drain_with_cancellation(&mut h);
        assert_eq!(out.len(), 3);
        // Terms emerge in descending degrevlex order — same as the
        // source polynomial's canonical order.
        assert_eq!(out[0].0, Fr::from(5u64));
        assert_eq!(out[0].1, mono(&r, &[3, 0, 0]).0);
        assert_eq!(out[1].0, Fr::from(2u64));
        assert_eq!(out[1].1, mono(&r, &[1, 1, 0]).0);
        assert_eq!(out[2].0, Fr::from(1u64));
        assert_eq!(out[2].1, mono(&r, &[0, 0, 2]).0);
    }

    #[test]
    fn two_reducers_complete_cancellation_drains_to_zero() {
        // Two copies of the same poly with opposite-sign coeffs:
        // 1 * p + (-1) * p should cancel everywhere.
        let r = mk_ring(3);
        let p = Poly::from_terms(
            &r,
            vec![
                (Fr::from(5u64), mono(&r, &[2, 0, 0])),
                (Fr::from(3u64), mono(&r, &[0, 1, 0])),
            ],
        );
        let one = MonoTerm::one(&r);
        let neg_one = -Fr::one();

        let mut h = ReducerHeap::<Fr, GrevLexTerm>::new(Arc::clone(&r), 0);
        h.push_reducer(Reducer {
            poly: &p,
            multiplier: one,
            coeff: Fr::one(),
            cursor: p.cursor(),
            sugar: 2,
        });
        h.push_reducer(Reducer {
            poly: &p,
            multiplier: one,
            coeff: neg_one,
            cursor: p.cursor(),
            sugar: 2,
        });

        // Every leader cancels; pop_with_cancellation should
        // return None right away after eating all the cancelled
        // chains.
        let out = drain_with_cancellation(&mut h);
        assert!(out.is_empty(), "everything should cancel; got {out:?}");
        assert!(h.heap_is_empty());
    }

    #[test]
    fn partial_cancellation_yields_remainder() {
        // p = 5*x^2 + 3*y, q = 2*x^2 + 7*z.
        // 1 * p + 1 * q  →  (5+2)*x^2 + 3*y + 7*z
        let r = mk_ring(3);
        let p = Poly::from_terms(
            &r,
            vec![
                (Fr::from(5u64), mono(&r, &[2, 0, 0])),
                (Fr::from(3u64), mono(&r, &[0, 1, 0])),
            ],
        );
        let q = Poly::from_terms(
            &r,
            vec![
                (Fr::from(2u64), mono(&r, &[2, 0, 0])),
                (Fr::from(7u64), mono(&r, &[0, 0, 1])),
            ],
        );
        let one = MonoTerm::one(&r);
        let mut h = ReducerHeap::<Fr, GrevLexTerm>::new(Arc::clone(&r), 0);
        h.push_reducer(Reducer {
            poly: &p,
            multiplier: one,
            coeff: Fr::one(),
            cursor: p.cursor(),
            sugar: 2,
        });
        h.push_reducer(Reducer {
            poly: &q,
            multiplier: one,
            coeff: Fr::one(),
            cursor: q.cursor(),
            sugar: 2,
        });
        let out = drain_with_cancellation(&mut h);
        assert_eq!(out.len(), 3);
        assert_eq!(out[0].0, Fr::from(7u64));
        assert_eq!(out[0].1, mono(&r, &[2, 0, 0]).0);
        assert_eq!(out[1].0, Fr::from(3u64));
        assert_eq!(out[1].1, mono(&r, &[0, 1, 0]).0);
        assert_eq!(out[2].0, Fr::from(7u64));
        assert_eq!(out[2].1, mono(&r, &[0, 0, 1]).0);
    }

    #[test]
    fn matches_poly_add_on_random_pairs() {
        // Property: pushing two reducers (1*p, 1*q) into the heap
        // and draining via pop_with_cancellation must yield the
        // same term sequence as p.add(q) does via poly::merge.
        let r = mk_ring(4);
        #[allow(clippy::type_complexity)]
        let pairs: Vec<(Vec<(u64, Vec<u32>)>, Vec<(u64, Vec<u32>)>)> = vec![
            (
                vec![(3, vec![2, 1, 0, 0]), (5, vec![1, 0, 1, 0])],
                vec![(2, vec![2, 1, 0, 0]), (4, vec![0, 1, 1, 0])],
            ),
            (
                vec![(7, vec![3, 0, 0, 0]), (1, vec![0, 0, 0, 1])],
                vec![(2, vec![1, 2, 0, 0])],
            ),
            (vec![], vec![(11, vec![1, 1, 1, 0])]),
        ];
        for (p_terms, q_terms) in pairs {
            let p = Poly::from_terms(
                &r,
                p_terms
                    .into_iter()
                    .map(|(c, e)| (Fr::from(c), mono(&r, &e)))
                    .collect(),
            );
            let q = Poly::from_terms(
                &r,
                q_terms
                    .into_iter()
                    .map(|(c, e)| (Fr::from(c), mono(&r, &e)))
                    .collect(),
            );

            // Reference: Poly::add via the geobucket-friendly merge.
            let want = p.add(&q, &r);
            let want_terms: Vec<(Fr, MonoTerm)> = want.iter().map(|(c, m)| (c, m.0)).collect();

            // Heap reducer: 1*p + 1*q.
            let one = MonoTerm::one(&r);
            let mut h = ReducerHeap::<Fr, GrevLexTerm>::new(Arc::clone(&r), 0);
            h.push_reducer(Reducer {
                poly: &p,
                multiplier: one,
                coeff: Fr::one(),
                cursor: p.cursor(),
                sugar: 0,
            });
            h.push_reducer(Reducer {
                poly: &q,
                multiplier: one,
                coeff: Fr::one(),
                cursor: q.cursor(),
                sugar: 0,
            });
            let got = drain_with_cancellation(&mut h);

            assert_eq!(got, want_terms);
        }
    }

    // ----- Phase 4: reduce_to_normal_form -----

    /// Reference reduction using Poly::sub_mul_term in a loop.
    /// Equivalent to the heap reducer but algorithmically distinct;
    /// used as the property-test oracle.
    fn reference_reduce(
        ring: &Ring<Fr>,
        f: Poly<Fr, GrevLexTerm>,
        basis: &[Poly<Fr, GrevLexTerm>],
    ) -> Poly<Fr, GrevLexTerm> {
        let mut current = f;
        loop {
            if current.is_zero() {
                return current;
            }
            let lm = *current.leading().unwrap().1;
            let lc = current.lm_coeff();

            // Find the first basis element whose lm divides current's lm.
            let divisor_idx = basis
                .iter()
                .position(|g| !g.is_zero() && g.leading().unwrap().1.divides(&lm, ring));
            let Some(idx) = divisor_idx else {
                // Irreducible leader: pop it off, recurse on the tail.
                // Easier: just emit the head into a survivor and
                // continue with the tail.
                let mut survivor_terms: Vec<(Fr, GrevLexTerm)> = Vec::new();
                let mut working = current;
                'outer: loop {
                    if working.is_zero() {
                        break;
                    }
                    let lm2 = *working.leading().unwrap().1;
                    let lc2 = working.lm_coeff();
                    let new_idx = basis
                        .iter()
                        .position(|g| !g.is_zero() && g.leading().unwrap().1.divides(&lm2, ring));
                    if let Some(j) = new_idx {
                        let g = &basis[j];
                        let g_lm = g.leading().unwrap().1;
                        let multiplier = lm2.div(g_lm, ring).unwrap();
                        debug_assert_eq!(g.lm_coeff(), Fr::one(), "basis must be monic");
                        // working -= lc2 * multiplier * g
                        working = working.sub_mul_term(lc2, &multiplier, g, ring);
                        continue 'outer;
                    } else {
                        // Move head to survivor and continue with tail.
                        survivor_terms.push((lc2, lm2));
                        working = working.drop_leading();
                    }
                }
                if survivor_terms.is_empty() {
                    return Poly::<Fr, GrevLexTerm>::zero();
                }
                return Poly::from_descending_terms_unchecked(ring, survivor_terms);
            };
            // Reducible: subtract.
            let g = &basis[idx];
            let g_lm = g.leading().unwrap().1;
            let multiplier = lm.div(g_lm, ring).unwrap();
            debug_assert_eq!(g.lm_coeff(), Fr::one(), "basis must be monic");
            current = current.sub_mul_term(lc, &multiplier, g, ring);
        }
    }

    /// Helper: run the heap reducer to normal form against a basis,
    /// using the same first-divisor-found policy as the reference.
    fn heap_reduce<'a>(
        ring: Arc<Ring<Fr>>,
        f: &'a Poly<Fr, GrevLexTerm>,
        basis: &'a [Poly<Fr, GrevLexTerm>],
        sugars: &[u32],
    ) -> Poly<Fr, GrevLexTerm> {
        let mut h = ReducerHeap::<Fr, GrevLexTerm>::new(Arc::clone(&ring), f.lm_deg());
        let one = MonoTerm::one(&ring);
        h.push_reducer(Reducer {
            poly: f,
            multiplier: one,
            coeff: Fr::one(),
            cursor: f.cursor(),
            sugar: f.lm_deg(),
        });
        let basis_owned: Vec<&Poly<Fr, GrevLexTerm>> = basis.iter().collect();
        let (out, _sugar) = h.reduce_to_normal_form(|leader| {
            for (idx, g) in basis_owned.iter().enumerate() {
                if g.is_zero() {
                    continue;
                }
                let g_lm = g.leading().unwrap().1;
                if g_lm.0.divides(leader, &ring) {
                    return Some((*g, sugars[idx]));
                }
            }
            None
        });
        out
    }

    #[test]
    fn no_divisors_returns_input_verbatim() {
        // If no basis element divides any term of f, normal form == f.
        let r = mk_ring(3);
        let f = Poly::from_terms(
            &r,
            vec![
                (Fr::from(5u64), mono(&r, &[1, 0, 0])),
                (Fr::from(3u64), mono(&r, &[0, 1, 0])),
                (Fr::from(2u64), mono(&r, &[0, 0, 1])),
            ],
        );
        let basis: Vec<Poly<Fr, GrevLexTerm>> = vec![]; // empty basis
        let got = heap_reduce(Arc::clone(&r), &f, &basis, &[]);
        assert_eq!(got, f);
    }

    #[test]
    fn single_step_reduction_matches_reference() {
        let r = mk_ring(3);
        let g = Poly::from_terms(&r, vec![(Fr::one(), mono(&r, &[1, 0, 0]))]);
        let f = Poly::from_terms(
            &r,
            vec![
                (Fr::one(), mono(&r, &[1, 0, 0])),
                (Fr::one(), mono(&r, &[0, 1, 0])),
                (Fr::one(), mono(&r, &[0, 0, 1])),
            ],
        );
        let basis = vec![g];
        let got = heap_reduce(Arc::clone(&r), &f, &basis, &[1]);
        let want = reference_reduce(&r, f.clone(), &basis);
        assert_eq!(got, want);
        // Also spot-check the answer: should be y + z.
        let expected = Poly::from_terms(
            &r,
            vec![
                (Fr::one(), mono(&r, &[0, 1, 0])),
                (Fr::one(), mono(&r, &[0, 0, 1])),
            ],
        );
        assert_eq!(got, expected);
    }

    #[test]
    fn multi_step_reduction_matches_reference() {
        // basis = { g0 = x - y, g1 = y - z }
        let r = mk_ring(3);
        // g0 = x - y. lm = x, lc = 1; tail = -y.
        let neg_one = -Fr::one();
        let g0 = Poly::from_terms(
            &r,
            vec![
                (Fr::one(), mono(&r, &[1, 0, 0])),
                (neg_one, mono(&r, &[0, 1, 0])),
            ],
        );
        // g1 = y - z.
        let g1 = Poly::from_terms(
            &r,
            vec![
                (Fr::one(), mono(&r, &[0, 1, 0])),
                (neg_one, mono(&r, &[0, 0, 1])),
            ],
        );
        let f = Poly::from_terms(&r, vec![(Fr::one(), mono(&r, &[1, 0, 0]))]);
        let basis = vec![g0, g1];
        let got = heap_reduce(Arc::clone(&r), &f, &basis, &[1, 1]);
        let want = reference_reduce(&r, f, &basis);
        assert_eq!(got, want);
        let expected = Poly::from_terms(&r, vec![(Fr::one(), mono(&r, &[0, 0, 1]))]);
        assert_eq!(got, expected);
    }

    #[test]
    fn reduces_to_zero_when_input_is_in_ideal() {
        // basis = { g = x - 1 } in k[x] (1 var).
        // f = x^3 - 1.
        let r = mk_ring(1);
        let neg_one = -Fr::one();
        let g = Poly::from_terms(
            &r,
            vec![(Fr::one(), mono(&r, &[1])), (neg_one, mono(&r, &[0]))],
        );
        let f = Poly::from_terms(
            &r,
            vec![(Fr::one(), mono(&r, &[3])), (neg_one, mono(&r, &[0]))],
        );
        let basis = vec![g];
        let got = heap_reduce(Arc::clone(&r), &f, &basis, &[1]);
        let want = reference_reduce(&r, f, &basis);
        assert_eq!(got, want);
        assert!(got.is_zero(), "expected reduction to zero, got {got:?}");
    }

    #[test]
    fn matches_reference_on_random_basis_and_input() {
        // Strong correctness witness: for several hand-crafted
        // (basis, input) pairs that mirror the shapes the bba
        // driver produces, verify the heap reducer's output
        // exactly matches the reference reducer's output.
        let r = mk_ring(3);
        let neg_one = -Fr::one();

        type TermSpec = (Fr, Vec<u32>);
        type PolySpec = Vec<TermSpec>;
        type Case = (Vec<PolySpec>, PolySpec);

        let cases: Vec<Case> = vec![
            // basis = { x - y, y^2 - 1 }, f = x^2
            (
                vec![
                    vec![(Fr::one(), vec![1, 0, 0]), (neg_one, vec![0, 1, 0])],
                    vec![(Fr::one(), vec![0, 2, 0]), (neg_one, vec![0, 0, 0])],
                ],
                vec![(Fr::one(), vec![2, 0, 0])],
            ),
            // basis = { x*y - z }, f = x*y*z
            (
                vec![vec![(Fr::one(), vec![1, 1, 0]), (neg_one, vec![0, 0, 1])]],
                vec![(Fr::one(), vec![1, 1, 1])],
            ),
            // Empty basis: f reduces to itself.
            (
                vec![],
                vec![
                    (Fr::from(3u64), vec![2, 0, 1]),
                    (Fr::from(5u64), vec![0, 1, 1]),
                ],
            ),
            // basis = { x }, f = x^3 + x*y + 7  →  survivor = 7
            (
                vec![vec![(Fr::one(), vec![1, 0, 0])]],
                vec![
                    (Fr::one(), vec![3, 0, 0]),
                    (Fr::one(), vec![1, 1, 0]),
                    (Fr::from(7u64), vec![0, 0, 0]),
                ],
            ),
        ];

        for (basis_terms, f_terms) in cases {
            let basis: Vec<Poly<Fr, GrevLexTerm>> = basis_terms
                .into_iter()
                .map(|terms| {
                    Poly::from_terms(
                        &r,
                        terms.into_iter().map(|(c, e)| (c, mono(&r, &e))).collect(),
                    )
                })
                .collect();
            let sugars: Vec<u32> = basis.iter().map(|p| p.lm_deg()).collect();
            let f = Poly::from_terms(
                &r,
                f_terms
                    .into_iter()
                    .map(|(c, e)| (c, mono(&r, &e)))
                    .collect(),
            );
            let got = heap_reduce(Arc::clone(&r), &f, &basis, &sugars);
            let want = reference_reduce(&r, f.clone(), &basis);
            assert_eq!(
                got, want,
                "heap reducer disagrees with reference for f = {f:?}"
            );
        }
    }

    #[test]
    fn sugar_is_max_over_pushed_reducers() {
        let r = mk_ring(2);
        let p = Poly::from_terms(&r, vec![(Fr::one(), mono(&r, &[1, 0]))]);
        let one = MonoTerm::one(&r);
        let mut h = ReducerHeap::<Fr, GrevLexTerm>::new(Arc::clone(&r), 7);
        assert_eq!(h.sugar(), 7);
        h.push_reducer(Reducer {
            poly: &p,
            multiplier: one,
            coeff: Fr::one(),
            cursor: p.cursor(),
            sugar: 3,
        });
        // 7 still wins over 3.
        assert_eq!(h.sugar(), 7);
        h.push_reducer(Reducer {
            poly: &p,
            multiplier: one,
            coeff: Fr::one(),
            cursor: p.cursor(),
            sugar: 12,
        });
        // 12 takes over.
        assert_eq!(h.sugar(), 12);
    }

    #[test]
    fn duplicate_cmp_keys_both_pop() {
        // Two nodes with the same cmp_key but different
        // reducer_idx should both be poppable. Order between
        // them is unspecified, but neither should be lost.
        let r = mk_ring(3);
        let mut h = ReducerHeap::<Fr, GrevLexTerm>::new(Arc::clone(&r), 0);
        let a = HeapNode {
            pre_key: 0,
            cmp_key: [9, 0, 0, 0],
            reducer_idx: 1,
        };
        let b = HeapNode {
            pre_key: 0,
            cmp_key: [9, 0, 0, 0],
            reducer_idx: 2,
        };
        let c = HeapNode {
            pre_key: 0,
            cmp_key: [5, 0, 0, 0],
            reducer_idx: 3,
        };
        h.push_node(a.clone());
        h.push_node(c.clone());
        h.push_node(b.clone());
        let p1 = h.pop_max().unwrap();
        assert_eq!(p1.cmp_key, [9, 0, 0, 0]);
        let p2 = h.pop_max().unwrap();
        assert_eq!(p2.cmp_key, [9, 0, 0, 0]);
        let idxs = [p1.reducer_idx, p2.reducer_idx];
        assert!(idxs.contains(&1) && idxs.contains(&2));
        let p3 = h.pop_max().unwrap();
        assert_eq!(p3.cmp_key, [5, 0, 0, 0]);
        assert_eq!(p3.reducer_idx, 3);
        assert!(h.heap_is_empty());
    }

    /// B2: same `cmp_key` but different `pre_key` must NOT be
    /// equal. Pairs with `duplicate_cmp_keys_both_pop`: there
    /// the chain check should *unify* (so cancellation can sum
    /// coeffs); here it must *split* (different orbit blocks).
    #[test]
    fn pre_key_distinguishes_chains() {
        let a = HeapNode::<4> {
            pre_key: 7,
            cmp_key: [1, 2, 3, 4],
            reducer_idx: 0,
        };
        let b = HeapNode::<4> {
            pre_key: 9,
            cmp_key: [1, 2, 3, 4],
            reducer_idx: 1,
        };
        assert_ne!(a, b);
        assert!(b > a);
        // pre_key dominates over cmp_key word 3.
        let c = HeapNode::<4> {
            pre_key: 1,
            cmp_key: [0, 0, 0, u64::MAX],
            reducer_idx: 2,
        };
        let d = HeapNode::<4> {
            pre_key: 2,
            cmp_key: [0, 0, 0, 0],
            reducer_idx: 3,
        };
        assert!(d > c);
    }

    /// B1: end-to-end heap pop order matches `M::cmp` desc on the
    /// same monomials. Validates `M::cmp_key` ⇄ `M::cmp` contract
    /// via the actual `BinaryHeap<HeapNode>` consumer for both
    /// `GrevLexTerm` and `OddElimTerm`.
    fn heap_pop_order_matches_m_cmp<M>(nvars: u32)
    where
        M: Monomial<Fr, 4> + From<MonoTerm<4>>,
    {
        use crate::monomial::Monomial as _;
        let r = mk_ring(nvars);
        let mut s: u64 = 0xC0FFEE_BADC0DE;
        let mut step = || {
            s = s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            s
        };
        let n = nvars as usize;
        let mut samples: Vec<MonoTerm<4>> = Vec::with_capacity(48);
        while samples.len() < 48 {
            let exps: Vec<u32> = (0..n).map(|_| (step() % 6) as u32).collect();
            if let Some(m) = MonoTerm::from_exponents(&r, &exps) {
                samples.push(m);
            }
        }

        // Build a heap via M::cmp_key.
        let mut heap = BinaryHeap::<HeapNode<4>>::new();
        for (i, t) in samples.iter().enumerate() {
            let (pre_key, cmp_key) = M::cmp_key(t, &r);
            heap.push(HeapNode {
                pre_key,
                cmp_key,
                reducer_idx: i,
            });
        }

        // Expected order: sort samples by M::cmp descending.
        let mut expected: Vec<usize> = (0..samples.len()).collect();
        expected.sort_by(|&i, &j| M::from(samples[j]).cmp(&M::from(samples[i])));

        // Pop and zip — equal-key ties may permute reducer_idx, so
        // group expected by M::cmp class and check set membership
        // within each tie group.
        let mut popped: Vec<usize> = Vec::with_capacity(samples.len());
        while let Some(n) = heap.pop() {
            popped.push(n.reducer_idx);
        }

        // Walk both, grouping by M::cmp equivalence.
        let mut i = 0;
        while i < expected.len() {
            let mut j = i + 1;
            while j < expected.len()
                && M::from(samples[expected[j]]).cmp(&M::from(samples[expected[i]]))
                    == std::cmp::Ordering::Equal
            {
                j += 1;
            }
            let exp_set: std::collections::BTreeSet<usize> =
                expected[i..j].iter().copied().collect();
            let got_set: std::collections::BTreeSet<usize> = popped[i..j].iter().copied().collect();
            assert_eq!(
                exp_set, got_set,
                "heap pop order disagrees with M::cmp at position {} (nvars={})",
                i, nvars
            );
            i = j;
        }
    }

    #[test]
    fn heap_pop_matches_grevlex_cmp() {
        use crate::monomial::GrevLexTerm;
        for nvars in [1u32, 3, 7, 15, 31] {
            heap_pop_order_matches_m_cmp::<GrevLexTerm>(nvars);
        }
    }

    #[test]
    fn heap_pop_matches_oddelim_cmp() {
        use crate::monomial::OddElimTerm;
        for nvars in [1u32, 3, 7, 15, 31] {
            heap_pop_order_matches_m_cmp::<OddElimTerm>(nvars);
        }
    }
}
