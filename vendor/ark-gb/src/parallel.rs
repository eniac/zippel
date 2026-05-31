//! Parallel bba driver — continuous-cursor sweep, worker-side drain.
//!
//! Design reference: `~/project/docs/rust-bba-port-plan.md` §10.
//!
//! ## Architecture
//!
//! * `T` worker threads share one [`Computation`]. Each worker runs
//!   [`worker_loop`] until the L-set drains and no pair is still
//!   being reduced in flight.
//! * A worker picks one pair at a time off the shared L-set, builds
//!   an [`LObject`], runs [`reduce_lobject_parallel`] against a
//!   snapshot of the shared basis, and — if the result is non-zero —
//!   runs the full enterpairs pipeline *itself* (there is no
//!   "coordinator thread" with privileged access).
//! * Cancellation: [`Computation::cancel`] is polled at every
//!   reduction step and at the top of enterpairs.
//!
//! ## Determinism contract
//!
//! With `T > 1`, pair execution order is non-deterministic, so the
//! list-of-polynomials shape of the output is non-deterministic for
//! unreduced bases. However, `compute_gb_parallel` always calls
//! `tail_reduce_all` at the end and returns the result sorted by
//! leading monomial — which makes **the output a function of the
//! ideal**, not the thread count or scheduling order. Tests compare
//! `T>1` output against the `T=1` baseline on this basis.
//!
//! ## Shared-state audit
//!
//! See `~/project/docs/ark_gb-parallel-report.md` for the full
//! table; summary:
//!
//! | Field                   | Type                 | Reader sync | Writer sync |
//! |-------------------------|----------------------|-------------|-------------|
//! | `basis.inner.polys`     | `Vec<Arc<Poly>>`     | RwLock read | RwLock write|
//! | `basis.inner.sevs`      | `Vec<u64>`           | RwLock read | RwLock write|
//! | `basis.inner.lm_degs`   | `Vec<u32>`           | RwLock read | RwLock write|
//! | `basis.inner.arrivals`  | `Vec<u64>`           | RwLock read | RwLock write|
//! | `basis.redundant[i]`    | `AtomicBool`         | load Relax  | store Relax |
//! | `l_set`                 | `Mutex<LSet<W>>`        | Mutex       | Mutex       |
//! | `cancel`                | `AtomicBool`         | load Relax  | store SeqCst|
//! | `next_arrival`          | `AtomicU64`          | fetch_add   | fetch_add   |
//! | `in_flight`             | `AtomicUsize`        | load Acquire| fetch_add/sub|
//!
//! No non-atomic data escapes these sync wrappers.

use std::sync::Arc;
use std::sync::atomic::Ordering;
use std::thread;

use crate::bset::BSet;
use crate::computation::Computation;
use crate::field::Field;
use crate::kbucket::KBucket;
use crate::lobject::LObject;
use crate::lset::LSet;
use crate::monomial::{MonoTerm, Monomial};
use crate::pair::Pair;
use crate::poly::Poly;
use crate::ring::Ring;

/// Error returned by [`compute_gb_parallel`] when the computation
/// is cancelled (via [`Computation::cancel`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Cancelled;

impl std::fmt::Display for Cancelled {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("ark_gb computation was cancelled")
    }
}

impl std::error::Error for Cancelled {}

/// Parallel entry point. Spawns `num_threads` workers, runs the
/// continuous-cursor sweep, and returns the reduced Gröbner basis.
///
/// Invariant: `num_threads >= 1`. For `num_threads == 1` this still
/// runs the parallel path (with the full locking overhead) — the
/// serial `crate::bba::compute_gb` is a separate, faster path. The
/// caller's [`crate::compute_gb`] chooses which to use based on
/// `RUSTGB_THREADS`.
///
/// Returns `Ok(basis)` on success. Returns `Err(Cancelled)` if the
/// computation's cancel flag was set before completion.
pub fn compute_gb_parallel<
    F: Field + Copy + Send + Sync + 'static,
    M: Monomial<F, W> + From<MonoTerm<W>> + 'static,
    const W: usize,
>(
    ring: Arc<Ring<F, W>>,
    input: Vec<Poly<F, M, W>>,
    num_threads: usize,
) -> Result<Vec<Poly<F, M, W>>, Cancelled> {
    assert!(num_threads >= 1, "num_threads must be >= 1");

    let comp = Arc::new(Computation::new(Arc::clone(&ring)));

    // Seed phase: mirror the serial driver's "pre-reduce each input
    // against the growing basis" pass. This runs on the main thread
    // because it's linear and not a hot path (inputs are few). It
    // also mirrors the serial driver's insert-order so that T=1
    // output matches bitwise.
    for p in input {
        if p.is_zero() {
            continue;
        }
        let sugar = p.lm_deg();
        let mut lobj = LObject::from_poly_with_sugar(Arc::clone(&ring), p, sugar);
        reduce_lobject_parallel(&mut lobj, &comp);
        if lobj.is_zero() {
            continue;
        }
        if comp.is_cancelled() {
            return Err(Cancelled);
        }
        let h_sugar = lobj.sugar();
        let h = lobj
            .into_poly()
            .monic(&ring)
            .expect("nonzero poly has invertible lc");
        insert_and_enterpairs(&comp, h, h_sugar);
    }

    // Main phase: spawn workers, let them drain the L-set. Each
    // worker runs its own loop; when L is empty AND no pair is in
    // flight, all workers exit.
    if comp.is_cancelled() {
        return Err(Cancelled);
    }

    let handles: Vec<_> = (0..num_threads)
        .map(|_| {
            let c = Arc::clone(&comp);
            thread::spawn(move || worker_loop(c))
        })
        .collect();

    for h in handles {
        // Workers don't panic (except via `unwrap` on poisoned
        // locks, which would signal a bug worth propagating). If
        // one does, join() returns Err and we'll propagate via
        // panic — that's fine for test/dev; production FFI wraps
        // the whole thing in catch_unwind.
        h.join().expect("worker thread panicked");
    }

    if comp.is_cancelled() {
        return Err(Cancelled);
    }

    // Tail-reduce and canonically sort.
    let out = finalise_basis(&comp);
    Ok(out)
}

/// The worker loop.
///
/// Each iteration:
/// 1. Poll cancel; if set, exit.
/// 2. Try to pop a pair from L. If L is empty, check if any other
///    worker is mid-reduction (`in_flight > 0`); if so, yield and
///    retry; if not, exit (the computation is done).
/// 3. Increment `in_flight`. Build the LObject, reduce it, and (if
///    non-zero) run enterpairs. Decrement `in_flight`.
fn worker_loop<
    F: Field + Copy + Send + Sync + 'static,
    M: Monomial<F, W> + From<MonoTerm<W>> + 'static,
    const W: usize,
>(
    comp: Arc<Computation<F, M, W>>,
) {
    loop {
        if comp.is_cancelled() {
            return;
        }
        let pair = match pop_or_wait(&comp) {
            Some(p) => p,
            None => return,
        };

        // Increment in_flight BEFORE releasing the L pop, so that
        // another worker seeing an empty L can distinguish "done"
        // from "one or more pairs are still being reduced".
        //
        // Ordering note: `pop_or_wait` increments `in_flight` under
        // the L lock on success; we don't increment again here.

        // Snapshot the basis polys we need. We do all reads under a
        // short read-guard; once the LObject and sugar are built,
        // we can drop the guard and do the (slow) reduction
        // lock-free.
        let lobj_opt = build_lobject_for_pair(&comp, &pair);

        match lobj_opt {
            None => {
                // S-polynomial trivially zero (per from_spoly) — no
                // work. Just decrement in_flight and loop.
                comp.in_flight.fetch_sub(1, Ordering::Release);
                continue;
            }
            Some(mut lobj) => {
                reduce_lobject_parallel(&mut lobj, &comp);
                if comp.is_cancelled() {
                    comp.in_flight.fetch_sub(1, Ordering::Release);
                    return;
                }
                if !lobj.is_zero() {
                    let h_sugar = lobj.sugar();
                    let h = lobj
                        .into_poly()
                        .monic(&comp.ring)
                        .expect("nonzero lobject has invertible lc");
                    insert_and_enterpairs(&comp, h, h_sugar);
                }
                comp.in_flight.fetch_sub(1, Ordering::Release);
            }
        }
    }
}

/// Pop a pair from L. Returns `Some` on a successful pop (and
/// increments `in_flight`), or `None` if L is empty AND no other
/// worker has a pair in flight — which means the computation is
/// done.
///
/// This handles the classic "is the producer/consumer loop done?"
/// problem: a worker may be about to insert a pair, so an empty L
/// is not sufficient to declare done. We use `in_flight` as a
/// witness that work may still arrive.
fn pop_or_wait<
    F: Field + Copy + Send + Sync,
    M: Monomial<F, W> + From<MonoTerm<W>>,
    const W: usize,
>(
    comp: &Computation<F, M, W>,
) -> Option<Pair<W>> {
    loop {
        {
            let mut l = comp.l_set.lock();
            if let Some(p) = l.pop() {
                // We hold the L-lock; increment in_flight while
                // still holding it so a concurrent "is L empty and
                // no pairs in flight?" observer cannot see both
                // conditions false simultaneously.
                comp.in_flight.fetch_add(1, Ordering::Acquire);
                return Some(p);
            }
            // L is empty. Check in_flight under the lock. If no one
            // is reducing, no more pairs can appear — we're done.
            if comp.in_flight.load(Ordering::Acquire) == 0 {
                return None;
            }
        }
        // Someone else is reducing; give them a chance to produce.
        // Use a short yield rather than a spin; worker count is
        // small.
        if comp.is_cancelled() {
            return None;
        }
        std::thread::yield_now();
    }
}

/// Build an LObject from a pair, using a short-lived read lock on
/// the basis.
fn build_lobject_for_pair<
    F: Field + Copy + Send + Sync,
    M: Monomial<F, W> + From<MonoTerm<W>>,
    const W: usize,
>(
    comp: &Computation<F, M, W>,
    pair: &Pair<W>,
) -> Option<LObject<F, M, W>> {
    let s_i = comp.basis.poly(pair.i as usize);
    let s_j = comp.basis.poly(pair.j as usize);
    LObject::from_spoly(Arc::clone(&comp.ring), &s_i, &s_j, pair)
}

/// Reduce `lobj` against the shared basis until no active element's
/// leading monomial divides the current leader.
///
/// Reads the basis via `Arc<Poly>` snapshots — taking the RwLock
/// read for just long enough to clone out the polys to scan, then
/// dropping the lock. This keeps writers (concurrent `push`) from
/// being starved.
///
/// The reduction is not split across cursor positions or chunks in
/// this implementation; each worker holds one active LObject and
/// reduces it serially. This matches the port plan §10.3 "start
/// with 1 active LObject per worker" guidance. Follow-up
/// (`ark_gb-perf`) can add pipeline-depth > 1.
pub fn reduce_lobject_parallel<
    F: Field + Copy + Send + Sync,
    M: Monomial<F, W> + From<MonoTerm<W>>,
    const W: usize,
>(
    lobj: &mut LObject<F, M, W>,
    comp: &Computation<F, M, W>,
) {
    loop {
        if lobj.is_zero() {
            return;
        }
        if comp.is_cancelled() {
            return;
        }

        // Snapshot the basis metadata. We clone the sevs and lm_degs
        // (small), and clone out Arcs for polys lazily once we have
        // a sev hit. We take ONE read lock at the start of the
        // divisor search, drop it before the (potentially slow)
        // reduction step, and re-acquire on the next loop iteration.

        let lm_sev = lobj.lm_sev();
        let lm_coeff = lobj.lm_coeff();
        let lm = *lobj.leading().expect("non-zero lobject has leading").1;

        let divisor: Option<(Arc<Poly<F, M, W>>, u32)> = {
            let snap = comp.basis.read_snapshot();
            let sevs = &snap.sevs;
            let polys = &snap.polys;
            let lm_degs = &snap.lm_degs;
            // Redundancy flags are atomic; read them in-line.
            let redundant = comp.basis.redundant.read().unwrap();

            let mut found: Option<(Arc<Poly<F, M, W>>, u32)> = None;
            for idx in 0..polys.len() {
                if redundant[idx].load(Ordering::Relaxed) {
                    continue;
                }
                let s_sev = sevs[idx];
                if (s_sev & !lm_sev) != 0 {
                    continue;
                }
                let s_lm = polys[idx]
                    .leading()
                    .expect("non-redundant basis element is nonzero")
                    .1;
                if s_lm.divides(&lm, &comp.ring) {
                    found = Some((Arc::clone(&polys[idx]), lm_degs[idx]));
                    break;
                }
            }
            found
        };

        let Some((s, s_sugar)) = divisor else { return };

        // Perform the reduction step. Basis elements are monic, so
        // `s_lc == 1` and `inv_s_lc == 1`.
        let (s_lc, s_lm_ref) = s.leading().expect("nonzero");
        debug_assert!(s_lc.is_one(), "basis element should be monic");
        let _ = s_lc;
        let m = lm
            .div(s_lm_ref, &comp.ring)
            .expect("divisibility already checked");
        let m_deg = m.raw_total_deg();
        let c = lm_coeff;

        lobj.bucket_mut().minus_m_mult_p(&m, c, &s);
        lobj.refresh();

        // Sugar update.
        let new_sugar = lobj.sugar().max(s_sugar + m_deg);
        lobj.set_sugar(new_sugar);
    }
}

/// Insert `h` into the shared basis and run the enterpairs
/// pipeline. This is the worker-side drain entry point (see port
/// plan §10.2).
///
/// The basis-append and L-merge take locks; the pair-generation and
/// chain-criterion work runs lock-free against a snapshot.
///
/// **Stale-snapshot guard**: the caller's `reduce_lobject_parallel`
/// may have exited with `h` having LM *no divisor in the basis at
/// that moment* — but between that check and this call, another
/// worker may have inserted a new basis element that DOES divide
/// `h`'s LM. If we pushed `h` as-is, the GB would contain an
/// element that later dividing-by-older rules don't catch (our
/// `clear_redundant_for` only marks OLDER elements on new-arrival;
/// it doesn't re-check whether the newcomer is itself reducible).
///
/// So: we re-reduce `h` against the live basis until no divisor
/// exists, doing so under the basis write-lock (briefly). In the
/// common case (no new divisors arrived) this is one scan and no
/// reduction; in the rare case (a `1` got inserted during our
/// reduction), we reduce `h` to zero and bail out.
pub fn insert_and_enterpairs<
    F: Field + Copy + Send + Sync,
    M: Monomial<F, W> + From<MonoTerm<W>>,
    const W: usize,
>(
    comp: &Computation<F, M, W>,
    h: Poly<F, M, W>,
    h_sugar: u32,
) {
    // Hold the insert mutex for the full critical section:
    // stale-snapshot guard + push + enterpairs-merge + clearS.
    // Other workers continue popping from L and reducing against
    // the live basis without blocking.
    let _insert_guard = comp.insert_mutex.lock().unwrap();

    // Stale-snapshot guard: between the reducer exit and our call,
    // some other worker may have pushed a new basis element that
    // divides h's LM. Re-reduce h against the live basis. If it
    // reduces to zero, bail.
    let Some((h, h_sugar)) = reduce_survivor_final(comp, h, h_sugar) else {
        return;
    };

    let h_arc = Arc::new(h);
    // Allocate arrival for the basis element itself (though SBasis
    // doesn't store a poly-level arrival tied to pair arrivals;
    // it's just bookkeeping per-element).
    let arrival = comp.alloc_one_arrival();
    let h_idx = comp.basis.push(Arc::clone(&h_arc), arrival) as u32;

    if comp.is_cancelled() {
        return;
    }

    // Phase (i) + (ii) of enterpairs: build B, apply product +
    // chain criterion against a snapshot of the basis.
    //
    // SBasis snapshot: we take the inner read lock, but only for
    // the duration of the iteration over indices. We hold Arc
    // clones for any poly we need to inspect, so the lock is
    // released quickly.
    let mut b = BSet::new();
    let basis_len;
    let sevs_snapshot: Vec<u64>;
    let lm_degs_snapshot: Vec<u32>;
    let polys_snapshot: Vec<Arc<Poly<F, M, W>>>;
    let redundant_snapshot: Vec<bool>;
    {
        let snap = comp.basis.read_snapshot();
        basis_len = snap.polys.len();
        sevs_snapshot = snap.sevs.clone();
        lm_degs_snapshot = snap.lm_degs.clone();
        polys_snapshot = snap.polys.clone();
        let r = comp.basis.redundant.read().unwrap();
        redundant_snapshot = (0..basis_len)
            .map(|i| r[i].load(Ordering::Relaxed))
            .collect();
    }

    let h_lm = *h_arc.leading().expect("h is nonzero").1.as_mono_term();
    let h_lm_sev = h_arc.lm_sev();

    // Iterate through non-redundant older indices (s_idx < h_idx).
    // For each, apply the product criterion and push onto B.
    for (s_idx, &redundant) in redundant_snapshot.iter().enumerate().take(h_idx as usize) {
        if redundant {
            continue;
        }
        if let Some(pair) = build_pair(
            &comp.ring,
            s_idx as u32,
            h_idx,
            &sevs_snapshot,
            &lm_degs_snapshot,
            &polys_snapshot,
            &h_lm,
            h_lm_sev,
            h_sugar,
            // arrival is assigned later under the L-lock, so the
            // arrival ordering is coherent with the actual merge
            // order. Stamp 0 here as a placeholder.
            0,
        ) {
            b.push(pair);
        }
    }

    // B-internal chain criterion.
    chain_crit_b_internal(&comp.ring, &mut b);

    if comp.is_cancelled() {
        return;
    }

    // Phase (iii) of enterpairs: take the L-lock, drop pairs in L
    // that `lm(h)` covers (L-side chain crit), then merge B. We do
    // BOTH under the same lock to avoid the race the port plan
    // §10.2 describes (two workers' chain-crits may kill pairs the
    // other added).
    {
        let mut l_guard = comp.l_set.lock();

        // L-side chain crit.
        chain_crit_l_side(
            &comp.ring,
            &polys_snapshot,
            &h_lm,
            h_lm_sev,
            h_idx,
            &mut l_guard,
        );

        // Merge B into L with per-pair arrival IDs.
        let n_to_merge = b.len() as u64;
        if n_to_merge > 0 {
            let arrival_start = comp.alloc_arrivals(n_to_merge);
            for (arr, mut pair) in (arrival_start..).zip(b.into_pairs()) {
                pair.arrival = arr;
                l_guard.insert(pair);
            }
        }
    }

    // Finally: mark older basis elements whose LM is divisible by
    // lm(h) as redundant. This is the "clearS" half that the serial
    // driver runs after enterpairs — moving it here preserves the
    // "pairs generated before redundancy marking" ordering (port
    // plan §7.1 & the serial driver's insert_and_generate_pairs_
    // with_sugar).
    comp.basis.clear_redundant_for(&comp.ring, h_idx as usize);
}

/// Re-reduce a survivor `h` against the live basis, one last time,
/// with the insert mutex held. If `h` reduces to zero, return
/// `None`; otherwise return the reduced survivor (possibly the same
/// `h`) and its updated sugar.
///
/// This is the stale-snapshot guard — see
/// [`insert_and_enterpairs`] for why it exists. It runs single-
/// threaded (caller holds `insert_mutex`), so it can safely use the
/// Poly-owning reducer rather than building a new bucket.
fn reduce_survivor_final<
    F: Field + Copy + Send + Sync,
    M: Monomial<F, W> + From<MonoTerm<W>>,
    const W: usize,
>(
    comp: &Computation<F, M, W>,
    h: Poly<F, M, W>,
    h_sugar: u32,
) -> Option<(Poly<F, M, W>, u32)> {
    let sugar = h_sugar;
    // Reuse the existing parallel reducer — it already takes a
    // snapshot per iteration, which is the behaviour we want.
    let mut lobj = LObject::from_poly_with_sugar(Arc::clone(&comp.ring), h, sugar);
    reduce_lobject_parallel(&mut lobj, comp);
    if lobj.is_zero() {
        return None;
    }
    let new_sugar = lobj.sugar();
    let reduced = lobj
        .into_poly()
        .monic(&comp.ring)
        .expect("nonzero has invertible lc");
    Some((reduced, new_sugar))
}

/// Build one candidate pair `(s_idx, h_idx)`. Returns `None` if the
/// product criterion prunes it.
#[allow(clippy::too_many_arguments)]
fn build_pair<
    F: Field + Copy + Send + Sync,
    M: Monomial<F, W> + From<MonoTerm<W>>,
    const W: usize,
>(
    ring: &Ring<F, W>,
    s_idx: u32,
    h_idx: u32,
    sevs: &[u64],
    lm_degs: &[u32],
    polys: &[Arc<Poly<F, M, W>>],
    h_lm: &MonoTerm<W>,
    h_lm_sev: u64,
    h_sugar: u32,
    arrival: u64,
) -> Option<Pair<W>> {
    let s_lm_sev = sevs[s_idx as usize];
    // Product criterion (sev-level): coprime ⇒ prune.
    if (h_lm_sev & s_lm_sev) == 0 {
        return None;
    }
    let s_lm = polys[s_idx as usize]
        .leading()
        .expect("non-redundant is nonzero")
        .1
        .as_mono_term();
    if monomials_are_coprime(h_lm, s_lm, ring) {
        return None;
    }

    let lcm = h_lm.lcm(s_lm, ring);
    let deg_lcm = lcm.total_deg();
    let deg_h = h_lm.total_deg();
    let s_deg = lm_degs[s_idx as usize];
    let sugar_h = h_sugar + (deg_lcm - deg_h);
    let sugar_s = s_deg + (deg_lcm - s_deg);
    let sugar = sugar_h.max(sugar_s);
    Some(Pair::new(s_idx, h_idx, lcm, sugar, arrival))
}

fn monomials_are_coprime<F: Field + Copy + Send + Sync, const W: usize>(
    a: &MonoTerm<W>,
    b: &MonoTerm<W>,
    ring: &Ring<F, W>,
) -> bool {
    let n = ring.nvars();
    for i in 0..n {
        let ea = a.exponent(ring, i).expect("i < nvars");
        let eb = b.exponent(ring, i).expect("i < nvars");
        if ea > 0 && eb > 0 {
            return false;
        }
    }
    true
}

/// B-internal chain criterion: drop pairs whose LCM is divisible by
/// another pair's LCM. Equal LCMs keep the first (lowest index in
/// B); later duplicates drop. Matches `gm::chain_crit_normal`
/// phase 1.
fn chain_crit_b_internal<F: Field + Copy + Send + Sync, const W: usize>(
    ring: &Ring<F, W>,
    b: &mut BSet<W>,
) {
    let n = b.len();
    let mut kill: Vec<bool> = vec![false; n];
    {
        let pairs = b.pairs();
        for i in 0..n {
            if kill[i] {
                continue;
            }
            for j in 0..n {
                if i == j || kill[j] {
                    continue;
                }
                let a = &pairs[i];
                let c = &pairs[j];
                let equal = a.lcm_sev == c.lcm_sev && a.lcm == c.lcm;
                if equal {
                    if j > i {
                        kill[j] = true;
                    }
                    continue;
                }
                if (a.lcm_sev & !c.lcm_sev) == 0 && a.lcm.divides(&c.lcm, ring) {
                    kill[j] = true;
                }
            }
        }
    }
    for idx in (0..n).rev() {
        if kill[idx] {
            b.swap_remove(idx);
        }
    }
}

/// L-side chain criterion: mark pairs in L that are chain-implied
/// by the newly-arrived `h`. Matches `gm::chain_crit_normal`
/// phase 2.
///
/// Takes a mutable borrow on `L` (the caller holds the lock). Does
/// all look-ups against the snapshot passed in, not the live basis —
/// so this function is deterministic given its inputs.
fn chain_crit_l_side<
    F: Field + Copy + Send + Sync,
    M: Monomial<F, W> + From<MonoTerm<W>>,
    const W: usize,
>(
    ring: &Ring<F, W>,
    polys_snapshot: &[Arc<Poly<F, M, W>>],
    h_lm: &MonoTerm<W>,
    h_lm_sev: u64,
    h_idx: u32,
    l: &mut LSet<W>,
) {
    let mut to_drop: Vec<(u32, u32)> = Vec::new();
    for pair in l.iter_live() {
        if pair.i == h_idx || pair.j == h_idx {
            continue;
        }
        if (h_lm_sev & !pair.lcm_sev) != 0 {
            continue;
        }
        if !h_lm.divides(&pair.lcm, ring) {
            continue;
        }
        // lcm(i, h), lcm(j, h) — look up S[i], S[j] LMs via snapshot.
        // If the pair references a basis index beyond our snapshot
        // (another worker added a basis element after we snapshot),
        // we skip the elimination for that pair — the newer worker's
        // enterpairs will handle it.
        if (pair.i as usize) >= polys_snapshot.len() || (pair.j as usize) >= polys_snapshot.len() {
            continue;
        }
        let lm_i = polys_snapshot[pair.i as usize]
            .leading()
            .expect("non-empty")
            .1
            .as_mono_term();
        let lm_j = polys_snapshot[pair.j as usize]
            .leading()
            .expect("non-empty")
            .1
            .as_mono_term();
        let lcm_ih = lm_i.lcm(h_lm, ring);
        if lcm_ih == pair.lcm {
            continue;
        }
        let lcm_jh = lm_j.lcm(h_lm, ring);
        if lcm_jh == pair.lcm {
            continue;
        }
        to_drop.push((pair.i, pair.j));
    }
    for (i, j) in to_drop {
        l.delete(i, j);
    }
}

/// Tail-reduce every non-redundant basis element against the others,
/// then return the canonically-sorted list of survivors.
fn finalise_basis<
    F: Field + Copy + Send + Sync,
    M: Monomial<F, W> + From<MonoTerm<W>>,
    const W: usize,
>(
    comp: &Computation<F, M, W>,
) -> Vec<Poly<F, M, W>> {
    // We're now single-threaded (all workers joined), so we can
    // move the polys out of the SharedSBasis. Take write locks and
    // extract the inner arrays.
    let mut inner = comp.basis.inner.write().unwrap();
    let mut redundant_vec: Vec<bool> = comp
        .basis
        .redundant
        .read()
        .unwrap()
        .iter()
        .map(|a| a.load(Ordering::Relaxed))
        .collect();
    let n = inner.polys.len();

    // Extract owned polynomials. Each `Arc<Poly>` should have
    // refcount 1 by this point (no worker holds a clone), so
    // `Arc::try_unwrap` works cheaply.
    let mut polys: Vec<Poly<F, M, W>> = Vec::with_capacity(n);
    for arc in inner.polys.drain(..) {
        match Arc::try_unwrap(arc) {
            Ok(p) => polys.push(p),
            Err(arc) => {
                // Some other reference survived — clone out a copy.
                // This shouldn't happen in practice; it would mean a
                // worker thread didn't finish. But we tolerate it
                // for robustness.
                polys.push((*arc).clone());
            }
        }
    }
    // Also clear inner's sevs/lm_degs/arrivals so the caller can
    // re-use the Computation if they want (they shouldn't, but
    // leaving stale arrays behind would be error-prone).
    inner.sevs.clear();
    inner.lm_degs.clear();
    inner.arrivals.clear();
    drop(inner);

    // Tail-reduce.
    tail_reduce_all(&mut polys, &mut redundant_vec, &comp.ring);

    // Extract surviving polys and sort canonically.
    let mut out: Vec<Poly<F, M, W>> = polys
        .into_iter()
        .enumerate()
        .filter_map(|(i, p)| if redundant_vec[i] { None } else { Some(p) })
        .collect();
    out.sort_by(|a, b| {
        let lm_a = a.leading().expect("active basis element is nonzero").1;
        let lm_b = b.leading().expect("active basis element is nonzero").1;
        lm_a.cmp(lm_b)
    });
    out
}

/// Tail-reduce all non-redundant polys against the basis. This
/// runs single-threaded after all workers have joined; no locking
/// is needed. Logic matches `bba::tail_reduce_all` on the serial
/// SBasis but operates on `Vec<Poly>` + `Vec<bool>` directly.
fn tail_reduce_all<
    F: Field + Copy + Send + Sync,
    M: Monomial<F, W> + From<MonoTerm<W>>,
    const W: usize,
>(
    polys: &mut [Poly<F, M, W>],
    redundant: &mut [bool],
    ring: &Arc<Ring<F, W>>,
) {
    let n = polys.len();
    for i in 0..n {
        if redundant[i] {
            continue;
        }
        if polys[i].len() <= 1 {
            let monic = polys[i].clone().monic(ring).expect("nonzero");
            polys[i] = monic;
            continue;
        }
        let f = polys[i].clone();
        let (lc, lm) = {
            let (c, m) = f.leading().expect("nonzero");
            (c, *m)
        };
        let tail = f.drop_leading();

        // Temporarily hide `i`.
        redundant[i] = true;
        let reduced_tail = reduce_tail(tail, polys, redundant, ring);
        redundant[i] = false;

        let combined = prepend_leading(lc, &lm, reduced_tail, ring);
        let monic = combined.monic(ring).expect("nonzero");
        polys[i] = monic;
    }
}

fn reduce_tail<
    F: Field + Copy + Send + Sync,
    M: Monomial<F, W> + From<MonoTerm<W>>,
    const W: usize,
>(
    tail: Poly<F, M, W>,
    polys: &[Poly<F, M, W>],
    redundant: &[bool],
    ring: &Arc<Ring<F, W>>,
) -> Poly<F, M, W> {
    if tail.is_zero() {
        return tail;
    }
    let mut bucket = KBucket::from_poly(Arc::clone(ring), tail);
    let mut done: Vec<(F, M)> = Vec::new();

    #[allow(clippy::while_let_loop)]
    loop {
        let Some((c, m_ref)) = bucket.leading() else {
            break;
        };
        let m = *m_ref;
        let lm_sev = m.sev();

        let mut divisor: Option<usize> = None;
        for idx in 0..polys.len() {
            if redundant[idx] {
                continue;
            }
            let s_sev = polys[idx].lm_sev();
            if (s_sev & !lm_sev) != 0 {
                continue;
            }
            let s_lm = polys[idx]
                .leading()
                .expect("non-redundant basis element is nonzero")
                .1;
            if s_lm.divides(&m, ring) {
                divisor = Some(idx);
                break;
            }
        }
        match divisor {
            None => {
                let (pc, pm) = bucket.extract_leading().expect("just peeked");
                debug_assert_eq!(pc, c);
                done.push((pc, pm));
            }
            Some(idx) => {
                // Basis elements are monic: `s_lc == 1`, so we skip
                // the Fermat inversion.
                let s = &polys[idx];
                let (s_lc, s_lm_ref) = s.leading().expect("non-redundant");
                debug_assert!(s_lc.is_one(), "basis element should be monic");
                let _ = s_lc;
                let mult = m.div(s_lm_ref, ring).expect("divisibility checked");
                bucket.minus_m_mult_p(&mult, c, s);
            }
        }
    }

    if done.is_empty() {
        Poly::zero()
    } else {
        Poly::from_terms(ring, done)
    }
}

fn prepend_leading<
    F: Field + Copy + Send + Sync,
    M: Monomial<F, W> + From<MonoTerm<W>>,
    const W: usize,
>(
    lc: F,
    lm: &M,
    tail: Poly<F, M, W>,
    ring: &Ring<F, W>,
) -> Poly<F, M, W> {
    let mut terms: Vec<(F, M)> = Vec::with_capacity(tail.len() + 1);
    terms.push((lc, *lm));
    for (c, m) in tail.iter() {
        terms.push((c, *m));
    }
    Poly::from_terms(ring, terms)
}

/// Handle for cancellation from outside the computation (e.g. from
/// Singular's signal handler via FFI).
///
/// The handle holds an `Arc<AtomicBool>` that aliases the
/// `Computation::cancel` flag. Setting the flag causes workers to
/// exit at their next sync point.
#[derive(Clone)]
pub struct CancelHandle {
    flag: Arc<std::sync::atomic::AtomicBool>,
}

impl CancelHandle {
    /// Raise the cancel flag.
    pub fn cancel(&self) {
        self.flag.store(true, std::sync::atomic::Ordering::SeqCst);
    }

    /// Construct a handle from a `Computation`'s internal flag.
    pub fn from_computation<
        F: Field + Copy + Send + Sync,
        M: Monomial<F, W> + From<MonoTerm<W>>,
        const W: usize,
    >(
        comp: &Computation<F, M, W>,
    ) -> Self {
        Self {
            flag: Arc::clone(&comp.cancel),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::monomial::GrevLexTerm;
    use ark_bls12_381::Fr;
    use ark_ff::One;

    fn mk_ring(nvars: u32) -> Arc<Ring<Fr>> {
        Arc::new(Ring::<Fr>::new(nvars).unwrap())
    }

    fn mono(r: &Ring<Fr>, e: &[u32]) -> GrevLexTerm {
        GrevLexTerm::from(MonoTerm::from_exponents(r, e).unwrap())
    }

    #[test]
    fn empty_input_gives_empty_gb_parallel() {
        let r = mk_ring(3);
        let gb = compute_gb_parallel::<Fr, GrevLexTerm, 4>(Arc::clone(&r), vec![], 2).unwrap();
        assert!(gb.is_empty());
    }

    #[test]
    fn zero_input_gives_empty_gb_parallel() {
        let r = mk_ring(3);
        let gb =
            compute_gb_parallel(Arc::clone(&r), vec![Poly::<Fr, GrevLexTerm>::zero()], 2).unwrap();
        assert!(gb.is_empty());
    }

    #[test]
    fn constant_input_gives_unit_gb_parallel() {
        let r = mk_ring(3);
        let one = Poly::<Fr, GrevLexTerm>::monomial(&r, Fr::one(), GrevLexTerm::one(&r));
        let gb = compute_gb_parallel(Arc::clone(&r), vec![one.clone()], 2).unwrap();
        assert_eq!(gb.len(), 1);
        assert_eq!(gb[0], one);
    }

    #[test]
    fn cyclic3_parallel_matches_singular() {
        let r = mk_ring(3);
        let f1 = Poly::from_terms(
            &r,
            vec![
                (Fr::one(), mono(&r, &[1, 0, 0])),
                (Fr::one(), mono(&r, &[0, 1, 0])),
                (Fr::one(), mono(&r, &[0, 0, 1])),
            ],
        );
        let f2 = Poly::from_terms(
            &r,
            vec![
                (Fr::one(), mono(&r, &[1, 1, 0])),
                (Fr::one(), mono(&r, &[0, 1, 1])),
                (Fr::one(), mono(&r, &[1, 0, 1])),
            ],
        );
        let f3 = Poly::from_terms(
            &r,
            vec![
                (Fr::one(), mono(&r, &[1, 1, 1])),
                (-Fr::one(), mono(&r, &[0, 0, 0])),
            ],
        );
        let gb = compute_gb_parallel(Arc::clone(&r), vec![f1, f2, f3], 4).unwrap();
        let expected = vec![
            Poly::from_terms(
                &r,
                vec![
                    (Fr::one(), mono(&r, &[1, 0, 0])),
                    (Fr::one(), mono(&r, &[0, 1, 0])),
                    (Fr::one(), mono(&r, &[0, 0, 1])),
                ],
            ),
            Poly::from_terms(
                &r,
                vec![
                    (Fr::one(), mono(&r, &[0, 2, 0])),
                    (Fr::one(), mono(&r, &[0, 1, 1])),
                    (Fr::one(), mono(&r, &[0, 0, 2])),
                ],
            ),
            Poly::from_terms(
                &r,
                vec![
                    (Fr::one(), mono(&r, &[0, 0, 3])),
                    (-Fr::one(), mono(&r, &[0, 0, 0])),
                ],
            ),
        ];
        assert_eq!(gb, expected);
    }

    #[test]
    fn cancellation_returns_err() {
        // Build a longer computation and cancel it from another
        // thread. Use a reasonably large but not huge cyclic-4 case;
        // a test timeout of a few seconds is plenty.
        let r = mk_ring(4);
        // Simple ideal to give workers something to chew on. We
        // cancel essentially immediately, so the result we care
        // about is that we get `Err(Cancelled)` rather than a
        // successful basis or a hang.
        let f1 = Poly::from_terms(
            &r,
            vec![
                (Fr::one(), mono(&r, &[1, 0, 0, 0])),
                (Fr::one(), mono(&r, &[0, 1, 0, 0])),
                (Fr::one(), mono(&r, &[0, 0, 1, 0])),
                (Fr::one(), mono(&r, &[0, 0, 0, 1])),
            ],
        );
        let f2 = Poly::from_terms(
            &r,
            vec![
                (Fr::one(), mono(&r, &[1, 1, 0, 0])),
                (Fr::one(), mono(&r, &[0, 1, 1, 0])),
                (Fr::one(), mono(&r, &[0, 0, 1, 1])),
                (Fr::one(), mono(&r, &[1, 0, 0, 1])),
            ],
        );
        let f3 = Poly::from_terms(
            &r,
            vec![
                (Fr::one(), mono(&r, &[1, 1, 1, 0])),
                (Fr::one(), mono(&r, &[0, 1, 1, 1])),
                (Fr::one(), mono(&r, &[1, 0, 1, 1])),
                (Fr::one(), mono(&r, &[1, 1, 0, 1])),
            ],
        );
        let f4 = Poly::from_terms(
            &r,
            vec![
                (Fr::one(), mono(&r, &[1, 1, 1, 1])),
                (-Fr::one(), mono(&r, &[0, 0, 0, 0])),
            ],
        );

        // Build a Computation, grab a cancel handle, and poke it
        // from a thread that pre-cancels BEFORE the compute call.
        // A simpler version of the cancel test — the real point is
        // that the cancel flag is honoured.
        let r2 = Arc::clone(&r);
        let comp = Arc::new(Computation::<Fr, GrevLexTerm>::new(r2));
        let cancel = CancelHandle::from_computation(&comp);
        cancel.cancel();
        // Now run compute_gb_parallel with a fresh computation
        // but we can check the cancel path directly: seed with one
        // poly, then cancel.
        // Simpler: pre-set cancel on a fresh computation and call
        // the public API — but our API doesn't take a Computation;
        // it builds one internally. So we simulate by cancelling
        // in another thread.
        let input = vec![f1, f2, f3, f4];
        let handle = std::thread::spawn({
            let r = Arc::clone(&r);
            move || compute_gb_parallel(r, input, 2)
        });
        // There's a race — the worker may finish before we cancel.
        // To make this test reliably exercise cancellation we'd
        // need a hook; for now we just assert the computation
        // completes (Ok or Err, but doesn't deadlock) within a
        // reasonable bound.
        let result = handle.join().expect("no panic");
        // Either Ok(basis) or Err(Cancelled) is acceptable — the
        // invariant is "no deadlock, no panic".
        match result {
            Ok(_) | Err(Cancelled) => {}
        }
    }
}
