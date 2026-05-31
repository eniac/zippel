//! Shared state for the parallel bba driver.
//!
//! This module defines three concurrent-friendly data structures:
//!
//! * [`SharedSBasis`]: the append-only basis. `polys` is an
//!   `RwLock<Vec<Arc<Poly>>>` — readers take a read lock long enough
//!   to clone out the `Arc<Poly>` values they want, then release the
//!   lock. `sevs` and `lm_degs` live inside the same RwLock since
//!   they are appended atomically with `polys`. `redundant` uses
//!   `AtomicBool` per index, so workers can mark / read flags
//!   without touching the RwLock.
//!
//! * [`SharedLSet`]: the pair queue. `Mutex<LSet>`. Per the task
//!   prompt: the C++ branch measured L-lock contention under 0.3% of
//!   wall time, so a plain mutex is fine for v1.
//!
//! * [`Computation`]: the coordinator. Owns `Arc<Ring>`, the
//!   `SharedSBasis`, the `SharedLSet`, the cancellation flag, the
//!   sweep cursor, and the `next_arrival` counter.
//!
//! All three are used by the parallel driver in [`crate::parallel`].
//! The serial driver in [`crate::bba`] continues to use the simpler
//! [`crate::SBasis`] / [`crate::LSet`] types unchanged.

use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize};
use std::sync::{Arc, Mutex, RwLock};

use crate::field::Field;
use crate::lset::LSet;
use crate::monomial::Monomial;
use crate::poly::Poly;
use crate::ring::Ring;

/// Concurrent, append-only basis.
///
/// Invariants:
/// - The three `Vec`s inside `inner` always have the same length.
///   Appenders take the write lock to enforce this.
/// - `redundant[i]` is always in sync with `inner.polys[i]` (same
///   number of entries, pushed under the same write lock).
/// - `Arc<Poly>` addresses are stable across pushes (Vec growth
///   reallocates the `Arc<Poly>` slots, but the `Poly` bodies live
///   behind `Arc` so the pointers the `Arc`s wrap are stable).
#[derive(Debug)]
pub struct SharedSBasis<F: Field + Copy + Send + Sync, M: Monomial<F, W>, const W: usize = 4> {
    /// The three parallel arrays, protected by a single RwLock. On
    /// read-heavy workloads (reduction inner loop) many readers
    /// coexist; append takes exclusive.
    pub inner: RwLock<SharedSBasisInner<F, M, W>>,
    /// Redundancy flags. One `AtomicBool` per basis element. Readers
    /// use `load(Relaxed)`; writers use `store(Relaxed)`. The length
    /// of this vector is synchronised with `inner` via the RwLock —
    /// a worker that reads `inner.polys.len()` and then reads
    /// `redundant[i]` for `i < len` is safe because only write-lock
    /// holders can grow either one.
    pub redundant: RwLock<Vec<AtomicBool>>,
}

/// The parallel arrays behind `SharedSBasis::inner`. Grouped so a
/// single RwLock guards their consistency.
#[derive(Debug)]
pub struct SharedSBasisInner<F: Field + Copy + Send + Sync, M: Monomial<F, W>, const W: usize = 4> {
    /// Polynomials, owned via `Arc<Poly>` so a reader can clone-out
    /// a handle and drop the RwLock immediately.
    pub polys: Vec<Arc<Poly<F, M, W>>>,
    /// Leading short-exponent vectors.
    pub sevs: Vec<u64>,
    /// Leading total degrees.
    pub lm_degs: Vec<u32>,
    /// Insertion arrival IDs (per-element, for lookup by index).
    pub arrivals: Vec<u64>,
}

impl<F: Field + Copy + Send + Sync, M: Monomial<F, W>, const W: usize> SharedSBasis<F, M, W> {
    /// Empty basis.
    pub fn new() -> Self {
        Self {
            inner: RwLock::new(SharedSBasisInner::default()),
            redundant: RwLock::new(Vec::new()),
        }
    }

    /// Snapshot of the current length. The length is monotonically
    /// increasing, so a subsequent read that sees a larger length
    /// just means new elements were appended between the two
    /// observations — which is fine for enterpairs (G-M symmetry
    /// handles the "new elements pair against me later" case).
    #[inline]
    pub fn len(&self) -> usize {
        self.inner.read().unwrap().polys.len()
    }

    /// Whether the basis has no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Append `h` to the basis. Returns the index at which `h` was
    /// placed. Takes both write locks in a consistent order
    /// (`inner` first, `redundant` second) to avoid deadlock.
    pub fn push(&self, h: Arc<Poly<F, M, W>>, arrival: u64) -> usize {
        let lm_sev = h.lm_sev();
        let lm_deg = h.lm_deg();
        let mut inner = self.inner.write().unwrap();
        let mut redundant = self.redundant.write().unwrap();
        let idx = inner.polys.len();
        inner.polys.push(h);
        inner.sevs.push(lm_sev);
        inner.lm_degs.push(lm_deg);
        inner.arrivals.push(arrival);
        redundant.push(AtomicBool::new(false));
        idx
    }

    /// Read-only snapshot of `(polys, sevs, lm_degs)` up to
    /// `len`-many. The returned tuple holds the read guard for the
    /// lifetime of the borrow; drop it quickly.
    pub fn read_snapshot(&self) -> std::sync::RwLockReadGuard<'_, SharedSBasisInner<F, M, W>> {
        self.inner.read().unwrap()
    }

    /// Read the redundancy flag for `idx`. Returns `true` if the
    /// index is marked redundant. Panics if `idx` is out of range —
    /// the caller must have a valid snapshot length.
    pub fn is_redundant(&self, idx: usize) -> bool {
        let r = self.redundant.read().unwrap();
        r[idx].load(std::sync::atomic::Ordering::Relaxed)
    }

    /// Read a batch of redundancy flags. More cache-friendly than
    /// looping through `is_redundant`.
    pub fn redundant_snapshot(&self, len: usize) -> Vec<bool> {
        let r = self.redundant.read().unwrap();
        (0..len)
            .map(|i| r[i].load(std::sync::atomic::Ordering::Relaxed))
            .collect()
    }

    /// Set the redundancy flag for `idx` to `flag`.
    pub fn set_redundant(&self, idx: usize, flag: bool) {
        let r = self.redundant.read().unwrap();
        r[idx].store(flag, std::sync::atomic::Ordering::Relaxed);
    }

    /// Clone-out an `Arc<Poly>` for index `idx`. Cheap (one atomic
    /// ref-count bump). Callers use this to hold a stable handle on
    /// a basis element after dropping the read lock.
    pub fn poly(&self, idx: usize) -> Arc<Poly<F, M, W>> {
        Arc::clone(&self.inner.read().unwrap().polys[idx])
    }

    /// Mark older elements (`i < idx`) whose leading monomial is
    /// divisible by `polys[idx]`'s leading monomial as redundant.
    ///
    /// Called by the driver after appending and running enterpairs.
    /// Matches the serial `SBasis::clear_redundant_for` semantics.
    ///
    /// Takes an `inner` read-guard implicitly to walk the arrays.
    /// Writes redundancy flags via their atomics (no lock needed).
    pub fn clear_redundant_for(&self, ring: &Ring<F, W>, idx: usize) {
        let inner = self.inner.read().unwrap();
        let polys = &inner.polys;
        let sevs = &inner.sevs;
        debug_assert!(idx < polys.len());
        let h_lm_sev = sevs[idx];
        let h_lm = *polys[idx].leading().expect("non-zero basis element").1;
        // Grab redundant-read-lock to index into the flag array.
        let r = self.redundant.read().unwrap();
        for i in 0..idx {
            if r[i].load(std::sync::atomic::Ordering::Relaxed) {
                continue;
            }
            if (h_lm_sev & !sevs[i]) != 0 {
                continue;
            }
            let s_i_lm = polys[i]
                .leading()
                .expect("non-redundant basis element is nonzero")
                .1;
            if h_lm.divides(s_i_lm, ring) {
                r[i].store(true, std::sync::atomic::Ordering::Relaxed);
            }
        }
    }
}

impl<F: Field + Copy + Send + Sync, M: Monomial<F, W>, const W: usize> Default
    for SharedSBasis<F, M, W>
{
    fn default() -> Self {
        Self::new()
    }
}

/// Concurrent S-pair queue.
///
/// Trivially `Mutex<LSet>` — the serial `LSet` already has the
/// right API; we just ensure all accesses go through the lock.
#[derive(Debug)]
pub struct SharedLSet<const W: usize = 4> {
    inner: Mutex<LSet<W>>,
}

impl<const W: usize> SharedLSet<W> {
    /// Empty queue.
    pub fn new() -> Self {
        Self {
            inner: Mutex::new(LSet::new()),
        }
    }

    /// Pop the next pair, if any.
    pub fn pop(&self) -> Option<crate::pair::Pair<W>> {
        self.inner.lock().unwrap().pop()
    }

    /// Lock for read/write access. Used by the enterpairs merge
    /// phase which needs to hold the lock across a "drop pairs, then
    /// insert new pairs" sequence (phase iii of enterpairs per
    /// rust-bba-port-plan.md §10.2).
    pub fn lock(&self) -> std::sync::MutexGuard<'_, LSet<W>> {
        self.inner.lock().unwrap()
    }

    /// Number of live pairs (under a lock acquisition).
    pub fn len(&self) -> usize {
        self.inner.lock().unwrap().len()
    }

    /// Whether the queue is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<const W: usize> Default for SharedLSet<W> {
    fn default() -> Self {
        Self::new()
    }
}

/// The parallel computation's coordinator.
///
/// Every worker thread holds an `Arc<Computation>`. The struct owns
/// the ring, the shared basis, the shared L-set, the cancellation
/// flag, the sweep cursor, and the arrival counter.
///
/// After the computation completes (all workers exit and the main
/// thread observes an empty L-set), the caller extracts the basis
/// via `into_basis`, which unwraps the inner `Arc` (cheap because
/// no worker is holding it any more).
#[derive(Debug)]
pub struct Computation<F: Field + Copy + Send + Sync, M: Monomial<F, W>, const W: usize = 4> {
    /// The ring — immutable, shared by all workers.
    pub ring: Arc<Ring<F, W>>,
    /// The growing basis.
    pub basis: SharedSBasis<F, M, W>,
    /// The pair queue.
    pub l_set: SharedLSet<W>,
    /// Cancellation flag. Workers poll at cursor boundaries.
    pub cancel: Arc<AtomicBool>,
    /// Monotonic "arrival" counter for the pair queue. Each new
    /// pair's `arrival` field is fetched from this atomic via
    /// `fetch_add`. Preserves the "older pair breaks sugar tie"
    /// contract across threads, modulo the usual caveat that at
    /// parallel workloads the sugar tie-break is non-deterministic.
    pub next_arrival: AtomicU64,
    /// How many surviving S-polynomials are currently being reduced
    /// across all workers. Used to decide when the computation is
    /// actually done: L may be empty for a moment because a worker
    /// just popped the last pair but hasn't finished reducing it yet.
    pub in_flight: AtomicUsize,
    /// Serializer for the "final divisor check + push + enterpairs"
    /// critical section. Held for the duration of `insert_and_
    /// enterpairs`, which has two components:
    ///
    /// 1. A "final divisor check" that re-reduces a survivor
    ///    against the live basis. This closes the stale-snapshot
    ///    race where a worker's reducer finished before another
    ///    worker inserted a new element that would have divided
    ///    the survivor's LM.
    /// 2. The basis-append itself.
    ///
    /// Holding this lock during both means the basis-append sees a
    /// basis that is guaranteed to not divide h's LM, which in turn
    /// means `clear_redundant_for` (which only marks *older*
    /// elements, never the newcomer) correctly captures all
    /// redundancy. Without this lock, a worker could push an
    /// already-reducible element, leaving the final basis with
    /// redundant survivors.
    ///
    /// The critical section is short: divisor check against the
    /// basis sevs (fast scan), then a push (O(1) amortised), then
    /// enterpairs. Other workers continue reducing lock-free.
    pub insert_mutex: Mutex<()>,
}

impl<F: Field + Copy + Send + Sync, M: Monomial<F, W>, const W: usize> Computation<F, M, W> {
    /// Fresh computation.
    pub fn new(ring: Arc<Ring<F, W>>) -> Self {
        Self {
            ring,
            basis: SharedSBasis::new(),
            l_set: SharedLSet::new(),
            cancel: Arc::new(AtomicBool::new(false)),
            next_arrival: AtomicU64::new(0),
            in_flight: AtomicUsize::new(0),
            insert_mutex: Mutex::new(()),
        }
    }

    /// Allocate a block of `count` arrival IDs. Returns the first
    /// ID; IDs `first..first+count` are reserved for the caller.
    /// Used by the enterpairs merge phase: it knows how many pairs
    /// it's about to insert and wants them stamped with contiguous
    /// arrival IDs.
    #[inline]
    pub fn alloc_arrivals(&self, count: u64) -> u64 {
        self.next_arrival
            .fetch_add(count, std::sync::atomic::Ordering::Relaxed)
    }

    /// Allocate one arrival ID.
    #[inline]
    pub fn alloc_one_arrival(&self) -> u64 {
        self.next_arrival
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    }

    /// Request cancellation. Workers will exit at the next cursor
    /// boundary.
    pub fn cancel(&self) {
        self.cancel.store(true, std::sync::atomic::Ordering::SeqCst);
    }

    /// Whether cancellation has been requested.
    #[inline]
    pub fn is_cancelled(&self) -> bool {
        self.cancel.load(std::sync::atomic::Ordering::Relaxed)
    }
}

impl<F: Field + Copy + Send + Sync, M: Monomial<F, W>, const W: usize> Default
    for SharedSBasisInner<F, M, W>
{
    fn default() -> Self {
        Self {
            polys: Vec::new(),
            sevs: Vec::new(),
            lm_degs: Vec::new(),
            arrivals: Vec::new(),
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
    fn push_and_snapshot() {
        let r = mk_ring(3);
        let b = SharedSBasis::new();
        let p1 = Arc::new(Poly::<Fr, GrevLexTerm>::monomial(
            &r,
            Fr::one(),
            GrevLexTerm::from(MonoTerm::from_exponents(&r, &[2, 0, 0]).unwrap()),
        ));
        let p2 = Arc::new(Poly::<Fr, GrevLexTerm>::monomial(
            &r,
            Fr::one(),
            GrevLexTerm::from(MonoTerm::from_exponents(&r, &[0, 1, 0]).unwrap()),
        ));
        let i1 = b.push(p1, 0);
        let i2 = b.push(p2, 1);
        assert_eq!((i1, i2), (0, 1));
        assert_eq!(b.len(), 2);
        let snap = b.read_snapshot();
        assert_eq!(snap.polys.len(), 2);
        assert_eq!(snap.sevs.len(), 2);
    }

    #[test]
    fn redundant_atomic() {
        let r = mk_ring(3);
        let b = SharedSBasis::new();
        let p = Arc::new(Poly::<Fr, GrevLexTerm>::monomial(
            &r,
            Fr::one(),
            GrevLexTerm::from(MonoTerm::from_exponents(&r, &[1, 0, 0]).unwrap()),
        ));
        b.push(p, 0);
        assert!(!b.is_redundant(0));
        b.set_redundant(0, true);
        assert!(b.is_redundant(0));
    }

    #[test]
    fn cancel_flag_round_trips() {
        let r = mk_ring(3);
        let c = Computation::<Fr, GrevLexTerm>::new(r);
        assert!(!c.is_cancelled());
        c.cancel();
        assert!(c.is_cancelled());
    }

    #[test]
    fn alloc_arrivals_is_monotonic() {
        let r = mk_ring(3);
        let c = Computation::<Fr, GrevLexTerm>::new(r);
        let a = c.alloc_one_arrival();
        let b = c.alloc_arrivals(3);
        let d = c.alloc_one_arrival();
        assert_eq!(a, 0);
        assert_eq!(b, 1);
        assert_eq!(d, 4);
    }
}
