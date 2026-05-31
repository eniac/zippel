//! Singly-linked-list backend for [`Poly`].
//!
//! Enabled by the `linked_list_poly` Cargo feature. The default is
//! the flat-array backend in [`poly_vec`](super::poly_vec); see ADR-001
//! for the profile evidence that favours it, and ADR-014 for the
//! rationale behind keeping this second backend available.
//!
//! The shape here is close to Singular's `spolyrec` storage: each
//! node owns a coefficient, a monomial, and a `NonNull<Node<F, M>>` pointing
//! at the next node (or `None` at the tail). `drop_leading_in_place`
//! is O(1) via a take-and-deallocate on the head slot. A custom
//! [`Drop`] impl walks the chain iteratively so a million-term poly
//! doesn't overflow the stack.
//!
//! All node allocations and deallocations route through
//! [`super::node_pool`] functions that use `Box::new`/`Box::from_raw`.
//! The thread-local pool optimization has been removed to support
//! generic field types.
//!
//! Invariants (checked by [`Poly::assert_canonical`]):
//!
//! 1. `len` equals the number of reachable nodes from `head`.
//! 2. All coefficients are nonzero (zeros excluded).
//! 3. Monomials are strictly descending under the ring's ordering (no
//!    duplicates, no unsorted runs).
//! 4. `lm_*` fields match the head node's coefficient / monomial / deg
//!    when nonempty.

use std::marker::PhantomData;
use std::ptr::NonNull;

use crate::field::Field;
use crate::monomial::Monomial;
use crate::ring::Ring;

use super::node_pool::{alloc, dealloc};

/// A sparse polynomial in a [`Ring`], stored as a singly linked list.
///
/// See module documentation for invariants. The head node is the
/// leading term; descendants are in strictly-descending order under
/// the ring's monomial ordering.
///
/// # `Send + Sync` safety
///
/// `Poly` contains a raw [`NonNull<Node<F, M>>`], which is `!Send` and
/// `!Sync` by default. We manually opt in:
///
/// * **`Send`**: a `Poly` can be moved to another thread because its
///   `Node`s hold only POD data (`F = u32`, `M`, another
///   raw pointer). The pool-owning thread distinction matters only
///   at allocation / deallocation time — reading the chain on a
///   different thread is sound.
/// * **`Sync`**: a `&Poly<F, M, W>` can be shared across threads because all
///   read paths (`iter`, `cursor`, `leading`, field accessors) treat
///   the chain as immutable; no interior mutation happens behind a
///   shared reference.
///
/// There is, however, a one-way rule the caller must respect: **a
/// `Poly` must be dropped on a thread whose `NodePool` contains its
/// nodes**. The thread-local pool is per-thread; dropping a `Poly`
/// on a foreign thread pushes its node storage onto that foreign
/// thread's free list, which then hands it out on a later `alloc` as
/// though it had originated there. With the current pool-backed
/// variant this is still sound (all `Node`s are POD-equivalent;
/// reusing storage across threads does not corrupt state) **and**
/// single-thread safe (ark_gb's bba driver is single-threaded per
/// `compute_gb` invocation), but it silently leaks capacity from the
/// originating thread's pool. Tests that spawn threads and share
/// `Poly`s should be aware of this.
///
/// If ark_gb's parallel story changes (`SINGULAR_THREADS>1`; cf.
/// `~/Singular-parallel-bba`), the pool design has to be revisited;
/// this is tracked as follow-up work in ADR-016.
pub struct Poly<F: Field + Copy, M: Monomial<F, W>, const W: usize = 4> {
    /// First node (the leading term), or `None` for the zero poly.
    head: Option<NonNull<Node<F, M>>>,
    /// Number of live nodes reachable from `head`. Maintained on
    /// every mutation so `len()` stays O(1).
    len: usize,
    /// Cached leading-term sev (`head.mono.sev()`); 0 when empty.
    lm_sev: u64,
    /// Cached leading coefficient (`head.coeff`); `F::zero()` when empty.
    lm_coeff: F,
    /// Cached leading monomial degree (`head.mono.total_deg()`);
    /// 0 when empty.
    lm_deg: u32,
    _marker: PhantomData<F>,
}

// SAFETY: See the `Send + Sync` safety section on `Poly` above. The
// inner `NonNull<Node<F, M>>` is the only reason these auto-traits don't
// apply automatically.
unsafe impl<F: Field + Copy + Send, M: Monomial<F, W> + Send, const W: usize> Send
    for Poly<F, M, W>
{
}
unsafe impl<F: Field + Copy + Sync, M: Monomial<F, W> + Sync, const W: usize> Sync
    for Poly<F, M, W>
{
}

/// One term's worth of storage in the linked list.
///
/// `pub(super)` because [`super::node_pool`] constructs and destroys
/// these through a thread-local allocator. The field layout is
/// deliberate: `F` first (hot cache line for arithmetic), then
/// the monomial, then the `next` pointer.
pub(super) struct Node<F, M> {
    pub(super) coeff: F,
    pub(super) mono: M,
    pub(super) next: Option<NonNull<Node<F, M>>>,
}

impl<F: Field + Copy + std::fmt::Debug, M: Monomial<F, W>, const W: usize> std::fmt::Debug
    for Poly<F, M, W>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut dbg = f.debug_struct("Poly");
        dbg.field("len", &self.len)
            .field("lm_coeff", &self.lm_coeff)
            .field("lm_sev", &self.lm_sev)
            .field("lm_deg", &self.lm_deg);
        // Walk and collect terms for debugging.
        let mut terms: Vec<(F, &M)> = Vec::with_capacity(self.len);
        let mut node = self.head;
        while let Some(n) = node {
            // SAFETY: nodes reachable from `head` are live by the
            // canonical invariant.
            let n_ref = unsafe { n.as_ref() };
            terms.push((n_ref.coeff, &n_ref.mono));
            node = n_ref.next;
        }
        dbg.field("terms", &terms).finish()
    }
}

impl<F: Field + Copy, M: Monomial<F, W>, const W: usize> Drop for Poly<F, M, W> {
    /// Iterative drop so a very long chain does not blow the stack.
    /// Every node is handed back to the thread-local [`POOL`]; the
    /// caller takes each node's `next` before releasing it so the
    /// pool's `dealloc` never has to walk a chain.
    ///
    /// Regression-guarded by
    /// `tests::iterative_drop_survives_long_chain` (100 000-term
    /// poly; recursive drop would overflow the stack).
    fn drop(&mut self) {
        let mut cur = self.head.take();
        if cur.is_none() {
            return;
        }

        while let Some(node_ptr) = cur {
            // SAFETY: `node_ptr` is a live node from this `Poly`'s
            // chain. We take its `next` before releasing it so
            // `dealloc`'s caller contract (no dangling children)
            // holds.
            unsafe {
                let node = node_ptr.as_ptr();
                cur = (*node).next.take();
                dealloc(node_ptr);
            }
        }
    }
}

impl<F: Field + Copy, M: Monomial<F, W>, const W: usize> Clone for Poly<F, M, W> {
    /// Deep clone: walks the source chain, allocating fresh nodes
    /// through the pool. The sentinel-slot / tail-cursor pattern
    /// matches `merge_consuming` and friends so `Poly::clone` keeps
    /// the same alloc profile as the destructive paths.
    fn clone(&self) -> Self {
        if self.head.is_none() {
            return Self::zero();
        }
        // SAFETY: both the write-through-raw-pointer pattern used on
        // the output tail and the dereference of source-chain pointers
        // below are bounded to this function. The output chain is
        // built head-to-tail, each freshly allocated node immediately
        // linked from the previous node's `next`. Source-chain reads
        // use immutable references through `NonNull::as_ref` on live
        // nodes reachable from `self.head`.

        let mut head: Option<NonNull<Node<F, M>>> = None;
        let mut tail: *mut Option<NonNull<Node<F, M>>> = &mut head;
        let mut node = self.head;
        while let Some(n) = node {
            let n_ref = unsafe { n.as_ref() };
            let fresh = alloc(n_ref.coeff, n_ref.mono, None);
            unsafe {
                *tail = Some(fresh);
                tail = &mut (*fresh.as_ptr()).next;
            }
            node = n_ref.next;
        }
        Poly {
            head,
            len: self.len,
            lm_sev: self.lm_sev,
            lm_coeff: self.lm_coeff,
            lm_deg: self.lm_deg,
            _marker: PhantomData,
        }
    }
}

impl<F: Field + Copy, M: Monomial<F, W>, const W: usize> Poly<F, M, W> {
    // ----- Constructors -----

    /// The zero polynomial.
    pub fn zero() -> Self {
        Self {
            head: None,
            len: 0,
            lm_sev: 0,
            lm_coeff: F::zero(),
            lm_deg: 0,
            _marker: PhantomData,
        }
    }

    /// A polynomial with a single term `c * m`. Returns the zero
    /// polynomial if `c == 0`. `c` must already be reduced mod `p`.
    pub fn monomial(_ring: &Ring<F, W>, c: F, m: M) -> Self {
        if c.is_zero() {
            return Self::zero();
        }
        let lm_sev = m.as_mono_term().sev();
        let lm_deg = m.as_mono_term().total_deg();
        let head = alloc(c, m, None);
        Self {
            head: Some(head),
            len: 1,
            lm_sev,
            lm_coeff: c,
            lm_deg,
            _marker: PhantomData,
        }
    }

    /// Build a polynomial from a sequence of `(coeff, monomial)` pairs
    /// already in strictly-descending monomial order with no
    /// duplicates and no zero coefficients. See the `poly_vec`
    /// counterpart for the caller contract.
    pub fn from_descending_terms_unchecked(_ring: &Ring<F, W>, terms: Vec<(F, M)>) -> Self {
        if terms.is_empty() {
            return Self::zero();
        }
        let len = terms.len();

        // Debug-only validation pass. Separate from the construction
        // pass because the borrow checker gets confused if we both
        // hold `prev_mono: &M` and append into the chain in the
        // same loop.
        #[cfg(debug_assertions)]
        {
            let mut prev_mono: Option<&M> = None;
            for (c, m) in terms.iter() {
                debug_assert!(!c.is_zero(), "from_descending_terms_unchecked: zero coeff");
                if let Some(prev) = prev_mono {
                    debug_assert!(
                        prev.cmp(m).is_gt(),
                        "from_descending_terms_unchecked: not strictly descending"
                    );
                }
                prev_mono = Some(m);
            }
        }

        let lm_coeff = terms[0].0;
        let lm_sev = terms[0].1.as_mono_term().sev();
        let lm_deg = terms[0].1.as_mono_term().total_deg();

        let mut head: Option<NonNull<Node<F, M>>> = None;
        let mut tail: *mut Option<NonNull<Node<F, M>>> = &mut head;
        for (c, m) in terms {
            let fresh = alloc(c, m, None);
            unsafe {
                *tail = Some(fresh);
                tail = &mut (*fresh.as_ptr()).next;
            }
        }
        Poly {
            head,
            len,
            lm_sev,
            lm_coeff,
            lm_deg,
            _marker: PhantomData,
        }
    }

    /// Build from parallel vectors in descending order. Mirrors the
    /// `poly_vec` signature verbatim. Iterates both vectors once to
    /// chain up nodes.
    pub fn from_descending_parallel_unchecked(
        _ring: &Ring<F, W>,
        coeffs: Vec<F>,
        terms: Vec<M>,
    ) -> Self {
        debug_assert_eq!(coeffs.len(), terms.len());
        if terms.is_empty() {
            return Self::zero();
        }
        #[cfg(debug_assertions)]
        {
            for &c in &coeffs {
                debug_assert!(!c.is_zero());
            }
            for w in terms.windows(2) {
                debug_assert!(w[0].cmp(&w[1]).is_gt());
            }
        }
        let len = coeffs.len();
        let lm_coeff = coeffs[0];
        let lm_sev = terms[0].as_mono_term().sev();
        let lm_deg = terms[0].as_mono_term().total_deg();

        let mut head: Option<NonNull<Node<F, M>>> = None;
        let mut tail: *mut Option<NonNull<Node<F, M>>> = &mut head;
        for (c, m) in coeffs.into_iter().zip(terms) {
            let fresh = alloc(c, m, None);
            unsafe {
                *tail = Some(fresh);
                tail = &mut (*fresh.as_ptr()).next;
            }
        }
        Poly {
            head,
            len,
            lm_sev,
            lm_coeff,
            lm_deg,
            _marker: PhantomData,
        }
    }

    /// Build from unsorted terms. Sorts descending, de-dupes via sum,
    /// drops zeros. Semantics match `poly_vec::Poly::from_terms`.
    pub fn from_terms(ring: &Ring<F, W>, terms: Vec<(F, M)>) -> Self {
        let mut terms = terms;
        terms.sort_by_key(|b| std::cmp::Reverse(b.1));

        // Normalise: merge adjacent equal monomials, reduce coeffs
        // mod p, drop zeros. We do this into a Vec first to keep the
        // merge logic straightforward, then chain the survivors into
        // the linked list.
        let mut surviving: Vec<(F, M)> = Vec::with_capacity(terms.len());
        for (c, m) in terms {
            if c.is_zero() {
                continue;
            }
            if let Some(last) = surviving.last_mut()
                && last.1 == m
            {
                last.0 += c;
                if last.0.is_zero() {
                    surviving.pop();
                }
                continue;
            }
            surviving.push((c, m));
        }
        if surviving.is_empty() {
            return Self::zero();
        }
        Self::from_descending_terms_unchecked(ring, surviving)
    }

    // ----- Cache maintenance -----

    fn refresh_cache(&mut self) {
        if let Some(h) = self.head {
            // SAFETY: `h` points to a live leading node.
            let h_ref = unsafe { h.as_ref() };
            self.lm_sev = h_ref.mono.as_mono_term().sev();
            self.lm_deg = h_ref.mono.as_mono_term().total_deg();
            self.lm_coeff = h_ref.coeff;
        } else {
            self.lm_sev = 0;
            self.lm_coeff = F::zero();
            self.lm_deg = 0;
        }
    }

    // ----- Accessors -----

    /// Number of live terms.
    #[allow(clippy::len_without_is_empty)]
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Whether this is the zero polynomial.
    #[inline]
    pub fn is_zero(&self) -> bool {
        self.head.is_none()
    }

    /// Iterate over `(coeff, &monomial)` pairs in descending order.
    pub fn iter(&self) -> impl Iterator<Item = (F, &M)> + '_ {
        let mut node = self.head;
        std::iter::from_fn(move || {
            let n = node?;
            // SAFETY: `n` is a live node reachable from `self.head`;
            // the returned reference is bounded by `self`'s lifetime.
            let n_ref = unsafe { n.as_ref() };
            node = n_ref.next;
            Some((n_ref.coeff, &n_ref.mono))
        })
    }

    /// Leading term `(coeff, &monomial)`, or `None` if zero.
    pub fn leading(&self) -> Option<(F, &M)> {
        self.head.map(|h| {
            // SAFETY: `h` is a live leading node bounded by `self`.
            let r = unsafe { h.as_ref() };
            (r.coeff, &r.mono)
        })
    }

    /// Leading short exponent vector. 0 when zero.
    #[inline]
    pub fn lm_sev(&self) -> u64 {
        self.lm_sev
    }

    /// Leading coefficient. 0 when zero.
    #[inline]
    pub fn lm_coeff(&self) -> F {
        self.lm_coeff
    }

    /// Leading monomial total degree. 0 when zero.
    #[inline]
    pub fn lm_deg(&self) -> u32 {
        self.lm_deg
    }

    /// A cursor positioned at the leading term (or at end if zero).
    /// Both backends expose the same cursor shape — see the parent
    /// module's dispatcher for context.
    #[inline]
    pub fn cursor(&self) -> PolyCursor<'_, F, M, W> {
        PolyCursor {
            node: self.head,
            _marker: std::marker::PhantomData,
        }
    }

    /// Return a new polynomial with the leading term removed. If
    /// `self` is zero or a single term, returns the zero polynomial.
    /// Implemented by walking the tail and cloning each node (O(n)
    /// like the Vec version).
    pub fn drop_leading(&self) -> Poly<F, M, W> {
        if self.len <= 1 {
            return Self::zero();
        }
        // Walk source starting from self.head.next; clone each node
        // into a fresh output chain.

        let mut out_head: Option<NonNull<Node<F, M>>> = None;
        let mut tail: *mut Option<NonNull<Node<F, M>>> = &mut out_head;
        // Skip the leading node.
        let mut node = self.head.and_then(|h| {
            // SAFETY: `h` is live.
            let r = unsafe { h.as_ref() };
            r.next
        });
        while let Some(n) = node {
            // SAFETY: live node.
            let n_ref = unsafe { n.as_ref() };
            let fresh = alloc(n_ref.coeff, n_ref.mono, None);
            unsafe {
                *tail = Some(fresh);
                tail = &mut (*fresh.as_ptr()).next;
            }
            node = n_ref.next;
        }
        let mut out = Poly {
            head: out_head,
            len: self.len - 1,
            lm_sev: 0,
            lm_coeff: F::zero(),
            lm_deg: 0,
            _marker: PhantomData,
        };
        out.refresh_cache();
        out
    }

    /// In-place leading-term drop. O(1): takes the head, replaces it
    /// with `head.next`, deallocates the detached node.
    pub fn drop_leading_in_place(&mut self) {
        if let Some(h) = self.head.take() {
            // SAFETY: `h` is the live leading node. We take its `next`
            // before returning it to the pool so `dealloc`'s no-chain
            // contract holds.
            unsafe {
                let node = h.as_ptr();
                self.head = (*node).next.take();
                dealloc(h);
            }
            self.len -= 1;
        }
        self.refresh_cache();
    }

    // ----- Arithmetic -----

    /// In-place: `self = self + other`.
    pub fn add_assign(&mut self, other: &Poly<F, M, W>, ring: &Ring<F, W>) {
        if other.is_zero() {
            return;
        }
        if self.is_zero() {
            *self = other.clone();
            return;
        }
        *self = merge(ring, self, other, false);
    }

    /// Out-of-place addition.
    pub fn add(&self, other: &Poly<F, M, W>, ring: &Ring<F, W>) -> Poly<F, M, W> {
        if other.is_zero() {
            return self.clone();
        }
        if self.is_zero() {
            return other.clone();
        }
        merge(ring, self, other, false)
    }

    /// Destructive addition: `self + other`, reusing both inputs' list
    /// nodes in the output chain rather than allocating fresh ones.
    /// Mirrors Singular's `p_Add_q` template
    /// (`~/Singular/libpolys/polys/templates/p_Add_q__T.cc`) — see
    /// ADR-015 for the contract mapping. Both operands are consumed
    /// (ownership transfer enforces Singular's "Destroys: p, q"
    /// comment at the Rust type level).
    pub fn add_consuming(self, other: Poly<F, M, W>, ring: &Ring<F, W>) -> Poly<F, M, W> {
        if other.is_zero() {
            return self;
        }
        if self.is_zero() {
            return other;
        }
        merge_consuming(ring, self, other, false)
    }

    /// Out-of-place subtraction.
    pub fn sub(&self, other: &Poly<F, M, W>, ring: &Ring<F, W>) -> Poly<F, M, W> {
        if other.is_zero() {
            return self.clone();
        }
        if self.is_zero() {
            return other.neg(ring);
        }
        merge(ring, self, other, true)
    }

    /// Negation (flip every coefficient).
    pub fn neg(&self, ring: &Ring<F, W>) -> Poly<F, M, W> {
        let _ = ring;
        if self.is_zero() {
            return Self::zero();
        }

        let mut out_head: Option<NonNull<Node<F, M>>> = None;
        let mut tail: *mut Option<NonNull<Node<F, M>>> = &mut out_head;
        let mut node = self.head;
        while let Some(n) = node {
            // SAFETY: `n` is a live node from `self`.
            let n_ref = unsafe { n.as_ref() };
            let fresh = alloc(-(n_ref.coeff), n_ref.mono, None);
            unsafe {
                *tail = Some(fresh);
                tail = &mut (*fresh.as_ptr()).next;
            }
            node = n_ref.next;
        }
        let mut out = Poly {
            head: out_head,
            len: self.len,
            lm_sev: 0,
            lm_coeff: F::zero(),
            lm_deg: 0,
            _marker: PhantomData,
        };
        out.refresh_cache();
        out
    }

    /// Multiply every coefficient by a scalar. Returns zero if
    /// `c == 0`.
    pub fn scale(&self, c: F, ring: &Ring<F, W>) -> Poly<F, M, W> {
        let _ = ring;
        if c.is_zero() || self.is_zero() {
            return Self::zero();
        }

        let mut out_head: Option<NonNull<Node<F, M>>> = None;
        let mut tail: *mut Option<NonNull<Node<F, M>>> = &mut out_head;
        let mut node = self.head;
        while let Some(n) = node {
            let n_ref = unsafe { n.as_ref() };
            let fresh = alloc((n_ref.coeff) * (c), n_ref.mono, None);
            unsafe {
                *tail = Some(fresh);
                tail = &mut (*fresh.as_ptr()).next;
            }
            node = n_ref.next;
        }
        let mut out = Poly {
            head: out_head,
            len: self.len,
            lm_sev: 0,
            lm_coeff: F::zero(),
            lm_deg: 0,
            _marker: PhantomData,
        };
        out.refresh_cache();
        out
    }

    /// Multiply every monomial by `m`. Per ADR-018, the caller's ring
    /// construction must ensure no product overflows the 7-bit
    /// per-variable budget; release builds do not check.
    pub fn shift(&self, m: &M, ring: &Ring<F, W>) -> Poly<F, M, W> {
        if self.is_zero() {
            return Self::zero();
        }

        let mut out_head: Option<NonNull<Node<F, M>>> = None;
        let mut tail: *mut Option<NonNull<Node<F, M>>> = &mut out_head;
        let mut node = self.head;
        while let Some(n) = node {
            let n_ref = unsafe { n.as_ref() };
            let new_mono = n_ref.mono.mul(m, ring);
            let fresh = alloc(n_ref.coeff, new_mono, None);
            unsafe {
                *tail = Some(fresh);
                tail = &mut (*fresh.as_ptr()).next;
            }
            node = n_ref.next;
        }
        // Descending order preserved by degrevlex monotonicity,
        // same as the Vec backend.
        let mut out = Poly {
            head: out_head,
            len: self.len,
            lm_sev: 0,
            lm_coeff: F::zero(),
            lm_deg: 0,
            _marker: PhantomData,
        };
        out.refresh_cache();
        out
    }

    /// Standard multiplication via an accumulator (same strategy as
    /// the Vec backend). Per ADR-018, the caller must ensure no
    /// product overflows.
    pub fn mul(&self, other: &Poly<F, M, W>, ring: &Ring<F, W>) -> Poly<F, M, W> {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        let mut acc: Vec<(F, M)> = Vec::with_capacity(self.len * other.len);
        for (ca, ma) in self.iter() {
            for (cb, mb) in other.iter() {
                let m = ma.mul(mb, ring);
                let c = (ca) * (cb);
                if !c.is_zero() {
                    acc.push((c, m));
                }
            }
        }
        Self::from_terms(ring, acc)
    }

    /// The inner reduction step `self - c * m * q`. Splice-style
    /// two-pointer merge along both inputs' linked chains.
    ///
    /// Per ADR-018, the caller's ring construction must guarantee
    /// that every `m * q[i]` product stays in-range; release builds
    /// do not check.
    pub fn sub_mul_term(&self, c: F, m: &M, q: &Poly<F, M, W>, ring: &Ring<F, W>) -> Poly<F, M, W> {
        if c.is_zero() || q.is_zero() {
            return self.clone();
        }

        let mut out_head: Option<NonNull<Node<F, M>>> = None;
        let mut tail: *mut Option<NonNull<Node<F, M>>> = &mut out_head;
        let mut out_len: usize = 0;

        let mut left = self.head;
        let mut right = q.head;

        while let (Some(l), Some(r)) = (left, right) {
            // SAFETY: live nodes from `self` / `q`.
            let l_ref = unsafe { l.as_ref() };
            let r_ref = unsafe { r.as_ref() };
            let r_mono = m.mul(&r_ref.mono, ring);
            match l_ref.mono.cmp(&r_mono) {
                std::cmp::Ordering::Greater => {
                    let fresh = alloc(l_ref.coeff, l_ref.mono, None);
                    unsafe {
                        *tail = Some(fresh);
                        tail = &mut (*fresh.as_ptr()).next;
                    }
                    out_len += 1;
                    left = l_ref.next;
                }
                std::cmp::Ordering::Less => {
                    let neg = -((c) * (r_ref.coeff));
                    if !neg.is_zero() {
                        let fresh = alloc(neg, r_mono, None);
                        unsafe {
                            *tail = Some(fresh);
                            tail = &mut (*fresh.as_ptr()).next;
                        }
                        out_len += 1;
                    }
                    right = r_ref.next;
                }
                std::cmp::Ordering::Equal => {
                    let cmq = (c) * (r_ref.coeff);
                    let diff = (l_ref.coeff) - (cmq);
                    if !diff.is_zero() {
                        let fresh = alloc(diff, l_ref.mono, None);
                        unsafe {
                            *tail = Some(fresh);
                            tail = &mut (*fresh.as_ptr()).next;
                        }
                        out_len += 1;
                    }
                    left = l_ref.next;
                    right = r_ref.next;
                }
            }
        }
        while let Some(l) = left {
            // SAFETY: live node.
            let l_ref = unsafe { l.as_ref() };
            let fresh = alloc(l_ref.coeff, l_ref.mono, None);
            unsafe {
                *tail = Some(fresh);
                tail = &mut (*fresh.as_ptr()).next;
            }
            out_len += 1;
            left = l_ref.next;
        }
        while let Some(r) = right {
            // SAFETY: live node.
            let r_ref = unsafe { r.as_ref() };
            let neg = -((c) * (r_ref.coeff));
            if !neg.is_zero() {
                let prod_m = m.mul(&r_ref.mono, ring);
                let fresh = alloc(neg, prod_m, None);
                unsafe {
                    *tail = Some(fresh);
                    tail = &mut (*fresh.as_ptr()).next;
                }
                out_len += 1;
            }
            right = r_ref.next;
        }

        let mut out = Poly {
            head: out_head,
            len: out_len,
            lm_sev: 0,
            lm_coeff: F::zero(),
            lm_deg: 0,
            _marker: PhantomData,
        };
        out.refresh_cache();
        out
    }

    /// Destructive variant of [`sub_mul_term`](Self::sub_mul_term):
    /// `self - c * m * q`, destroying `self` and reusing its list nodes
    /// in the output chain. `m` and `q` are read-only (const in
    /// Singular's terminology).
    ///
    /// Mirrors Singular's `p_Minus_mm_Mult_qq` template
    /// (`~/Singular/libpolys/polys/templates/p_Minus_mm_Mult_qq__T.cc`).
    /// See ADR-015 for the contract mapping. Per ADR-018, the caller's
    /// ring construction must ensure no `m * q[i]` product overflows
    /// the 7-bit-per-variable exponent budget; release builds do not
    /// check.
    ///
    /// Includes the tail-splice fast path: when `self` exhausts before
    /// `q`, the remainder of `-c * m * q` is produced in a single pass
    /// and appended, rather than going through the compare loop.
    pub fn sub_mm_mult_qq_consuming(
        mut self,
        c: F,
        m: &M,
        q: &Poly<F, M, W>,
        ring: &Ring<F, W>,
    ) -> Poly<F, M, W> {
        if c.is_zero() || q.is_zero() {
            return self;
        }

        // Sentinel-slot pattern: `sentinel_slot` is a stack-local
        // `Option<NonNull<Node<F, M>>>` that will end up containing the
        // output chain's head. `tail_slot` tracks the slot where the
        // next node attaches (starts at `&mut sentinel_slot`, moves
        // to `&mut new_node.next` after each append). See ADR-015 for
        // the soundness argument.
        let mut sentinel_slot: Option<NonNull<Node<F, M>>> = None;
        let mut tail_slot: *mut Option<NonNull<Node<F, M>>> = &mut sentinel_slot;
        let mut out_len: usize = 0;

        // Take ownership of self's chain. From here on, `self.head`
        // is None until we reconstruct at the end.
        let mut left: Option<NonNull<Node<F, M>>> = self.head.take();
        let mut right: Option<NonNull<Node<F, M>>> = q.head;

        // SAFETY: Every write through `tail_slot` targets an
        // `Option<NonNull<Node<F, M>>>` that belongs to either
        // `sentinel_slot` (on the first iteration) or the `next`
        // field of the node most recently appended (which
        // `sentinel_slot` transitively owns through the chain).
        // `sentinel_slot` is a stack-local that outlives every
        // `tail_slot` update. No other live reference to any tail
        // slot exists during the writes: the input chains
        // (`left`, `right`) are walked separately, and on each
        // iteration we either (a) allocate a fresh node and link
        // it in, or (b) detach a node from `left` and splice it
        // in, with the detach completing before the write.
        unsafe {
            while let (Some(l), Some(r)) = (left, right) {
                let l_ref = l.as_ref();
                let r_ref = r.as_ref();
                let r_mono = m.mul(&r_ref.mono, ring);
                match l_ref.mono.cmp(&r_mono) {
                    std::cmp::Ordering::Greater => {
                        // Splice left's head into the output tail.
                        let l_ptr = l.as_ptr();
                        left = (*l_ptr).next.take();
                        (*l_ptr).next = None;
                        *tail_slot = Some(l);
                        tail_slot = &mut (*l_ptr).next;
                        out_len += 1;
                    }
                    std::cmp::Ordering::Less => {
                        let neg = -((c) * (r_ref.coeff));
                        right = r_ref.next;
                        if !neg.is_zero() {
                            let fresh = alloc(neg, r_mono, None);
                            *tail_slot = Some(fresh);
                            tail_slot = &mut (*fresh.as_ptr()).next;
                            out_len += 1;
                        }
                    }
                    std::cmp::Ordering::Equal => {
                        let cmq = (c) * (r_ref.coeff);
                        let diff = (l_ref.coeff) - (cmq);
                        right = r_ref.next;
                        let l_ptr = l.as_ptr();
                        left = (*l_ptr).next.take();
                        if !diff.is_zero() {
                            (*l_ptr).coeff = diff;
                            (*l_ptr).next = None;
                            *tail_slot = Some(l);
                            tail_slot = &mut (*l_ptr).next;
                            out_len += 1;
                        } else {
                            // Free the dropped node.
                            dealloc(l);
                        }
                    }
                }
            }

            // Tail splices. At most one of `left` / `right` is nonempty.
            if let Some(l_head) = left.take() {
                // Self still has terms; q is exhausted. Splice
                // the entire remaining chain in one assignment
                // and count its length by walking.
                let mut remaining_len = 1usize;
                let mut node = l_head.as_ref().next;
                while let Some(x) = node {
                    remaining_len += 1;
                    node = x.as_ref().next;
                }
                *tail_slot = Some(l_head);
                out_len += remaining_len;
                // `tail_slot` is no longer used after this point.
            } else {
                // Self exhausted; q may still have terms. Build
                // the remainder of `-c * m * q` fresh.
                while let Some(r) = right {
                    let r_ref = r.as_ref();
                    let neg = -((c) * (r_ref.coeff));
                    right = r_ref.next;
                    if neg.is_zero() {
                        continue;
                    }
                    let prod_m = m.mul(&r_ref.mono, ring);
                    let fresh = alloc(neg, prod_m, None);
                    *tail_slot = Some(fresh);
                    tail_slot = &mut (*fresh.as_ptr()).next;
                    out_len += 1;
                }
            }
        };

        // Move the chain out of the sentinel slot.
        self.head = sentinel_slot.take();
        self.len = out_len;
        self.refresh_cache();
        self
    }

    /// Scale so the leading coefficient becomes 1.
    pub fn monic(&self, ring: &Ring<F, W>) -> Option<Poly<F, M, W>> {
        if self.is_zero() {
            return Some(Self::zero());
        }
        let lc = self.lm_coeff;
        if lc.is_one() {
            return Some(self.clone());
        }
        let inv = (lc).inverse()?;
        Some(self.scale(inv, ring))
    }

    // ----- Invariants -----

    /// Panic if any internal invariant is violated.
    pub fn assert_canonical(&self, ring: &Ring<F, W>) {
        let mut node = self.head;
        let mut prev: Option<&M> = None;
        let mut count: usize = 0;
        while let Some(n) = node {
            // SAFETY: live node.
            let n_ref = unsafe { n.as_ref() };
            assert!(!n_ref.coeff.is_zero(), "coeff[{count}] is zero");
            n_ref.mono.as_mono_term().assert_canonical(ring);
            if let Some(p_m) = prev {
                let ord = p_m.cmp(&n_ref.mono);
                assert!(
                    ord == std::cmp::Ordering::Greater,
                    "terms not strictly descending at [{count}]: got {ord:?}"
                );
            }
            prev = Some(&n_ref.mono);
            count += 1;
            node = n_ref.next;
        }
        assert_eq!(self.len, count, "cached len disagrees with walk");
        if self.is_zero() {
            assert_eq!(self.lm_sev, 0);
            assert!(self.lm_coeff.is_zero());
            assert_eq!(self.lm_deg, 0);
        } else {
            // SAFETY: head is live and non-null here.
            let h = unsafe { self.head.unwrap().as_ref() };
            assert_eq!(self.lm_sev, h.mono.as_mono_term().sev());
            assert_eq!(self.lm_coeff, h.coeff);
            assert_eq!(self.lm_deg, h.mono.as_mono_term().total_deg());
        }
    }
}

impl<F: Field + Copy, M: Monomial<F, W>, const W: usize> Default for Poly<F, M, W> {
    fn default() -> Self {
        Self::zero()
    }
}

/// A cursor walking a [`Poly`]'s terms in descending order.
///
/// Obtain one with [`Poly::cursor`]. Cheap and `Copy`: it holds
/// a single pointer to the current node (or `None` when
/// exhausted). On the linked-list backend `advance` chases the
/// `next` pointer; on the flat-array backend (see
/// [`super::poly_vec::PolyCursor`]) it bumps an index. The same
/// shape on both backends lets [`crate::reducer::Reducer`] work
/// uniformly.
#[derive(Clone, Copy)]
pub struct PolyCursor<'a, F: Field + Copy, M: Monomial<F, W>, const W: usize = 4> {
    node: Option<NonNull<Node<F, M>>>,
    _marker: std::marker::PhantomData<&'a Node<F, M>>,
}

impl<'a, F: Field + Copy, M: Monomial<F, W>, const W: usize> std::fmt::Debug
    for PolyCursor<'a, F, M, W>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PolyCursor")
            .field("exhausted", &self.node.is_none())
            .finish()
    }
}

impl<'a, F: Field + Copy, M: Monomial<F, W>, const W: usize> PolyCursor<'a, F, M, W> {
    /// Current term `(coeff, &monomial)`, or `None` if exhausted.
    #[inline]
    pub fn term(&self) -> Option<(F, &'a M)> {
        self.node.map(|n| {
            // SAFETY: the cursor's lifetime `'a` is tied to the
            // borrowed `Poly`; its chain stays live for `'a`.
            let r = unsafe { n.as_ref() };
            (r.coeff, &r.mono)
        })
    }

    /// Advance one term. No-op once exhausted.
    #[inline]
    pub fn advance(&mut self) {
        self.node = self.node.and_then(|n| {
            // SAFETY: live node during lifetime `'a`.
            unsafe { n.as_ref() }.next
        });
    }

    /// True once all terms have been walked.
    #[inline]
    pub fn is_done(&self) -> bool {
        self.node.is_none()
    }
}

impl<F: Field + Copy, M: Monomial<F, W>, const W: usize> PartialEq for Poly<F, M, W> {
    fn eq(&self, other: &Self) -> bool {
        // Same length + same terms in order. We compare through
        // cursors so the comparison stays O(n) (no materialised
        // Vecs).
        if self.len != other.len {
            return false;
        }
        let mut a = self.head;
        let mut b = other.head;
        while let (Some(x), Some(y)) = (a, b) {
            // SAFETY: live nodes.
            let xr = unsafe { x.as_ref() };
            let yr = unsafe { y.as_ref() };
            if xr.coeff != yr.coeff || xr.mono != yr.mono {
                return false;
            }
            a = xr.next;
            b = yr.next;
        }
        a.is_none() && b.is_none()
    }
}
impl<F: Field + Copy, M: Monomial<F, W>, const W: usize> Eq for Poly<F, M, W> {}

/// Destructive merge: walk both chains, splicing input nodes
/// directly into the output chain rather than allocating fresh
/// ones. Mirrors Singular's `p_Add_q` node-splice pattern (see
/// `~/Singular/libpolys/polys/templates/p_Add_q__T.cc` lines 57,
/// 65, 71, 60-61, 67, 73). Both operands are consumed; `subtract`
/// flag chooses add vs sub semantics on the second operand's
/// coefficients.
///
/// Both inputs must be nonempty (callers guard zero operands).
fn merge_consuming<F: Field + Copy, M: Monomial<F, W>, const W: usize>(
    _ring: &Ring<F, W>,
    a: Poly<F, M, W>,
    b: Poly<F, M, W>,
    subtract: bool,
) -> Poly<F, M, W> {
    debug_assert!(!a.is_zero());
    debug_assert!(!b.is_zero());

    // Sentinel-slot pattern (see `sub_mm_mult_qq_consuming` for the
    // soundness argument).
    let mut sentinel_slot: Option<NonNull<Node<F, M>>> = None;
    let mut tail_slot: *mut Option<NonNull<Node<F, M>>> = &mut sentinel_slot;
    let mut out_len: usize = 0;

    // Move both input chains into local owned variables. We can't
    // destructure Poly because it has a custom Drop; `head.take()`
    // leaves the Poly with `head = None`, so the subsequent implicit
    // drop of `a` / `b` is O(1).
    let mut a = a;
    let mut b = b;
    let mut left: Option<NonNull<Node<F, M>>> = a.head.take();
    let mut right: Option<NonNull<Node<F, M>>> = b.head.take();

    // SAFETY: Identical argument to `sub_mm_mult_qq_consuming`.
    // Every write through `tail_slot` targets an
    // `Option<NonNull<Node<F, M>>>` that belongs to the sentinel chain.
    // `sentinel_slot` outlives every update. Input nodes are
    // detached from their source list before any dereference of
    // `tail_slot` through the spliced pointer.
    unsafe {
        while let (Some(l), Some(r)) = (left, right) {
            let l_ref = l.as_ref();
            let r_ref = r.as_ref();
            match l_ref.mono.cmp(&r_ref.mono) {
                std::cmp::Ordering::Greater => {
                    let l_ptr = l.as_ptr();
                    left = (*l_ptr).next.take();
                    (*l_ptr).next = None;
                    *tail_slot = Some(l);
                    tail_slot = &mut (*l_ptr).next;
                    out_len += 1;
                }
                std::cmp::Ordering::Less => {
                    let r_ptr = r.as_ptr();
                    right = (*r_ptr).next.take();
                    (*r_ptr).next = None;
                    if subtract {
                        (*r_ptr).coeff = -((*r_ptr).coeff);
                    }
                    *tail_slot = Some(r);
                    tail_slot = &mut (*r_ptr).next;
                    out_len += 1;
                }
                std::cmp::Ordering::Equal => {
                    // Combine coefficients; reuse left's node if
                    // the sum is nonzero, otherwise free both.
                    let bc = if subtract {
                        -(r_ref.coeff)
                    } else {
                        r_ref.coeff
                    };
                    let s = (l_ref.coeff) + (bc);
                    // Consume both heads.
                    let l_ptr = l.as_ptr();
                    let r_ptr = r.as_ptr();
                    left = (*l_ptr).next.take();
                    right = (*r_ptr).next.take();
                    if !s.is_zero() {
                        (*l_ptr).coeff = s;
                        (*l_ptr).next = None;
                        *tail_slot = Some(l);
                        tail_slot = &mut (*l_ptr).next;
                        out_len += 1;
                        // Free r_node.
                        dealloc(r);
                    } else {
                        dealloc(l);
                        dealloc(r);
                    }
                }
            }
        }

        // Tail splices: one side is exhausted. Splice the
        // remainder of the other side in a single pointer
        // assignment.
        if let Some(l_head) = left.take() {
            let mut remaining_len = 1usize;
            let mut node = l_head.as_ref().next;
            while let Some(x) = node {
                remaining_len += 1;
                node = x.as_ref().next;
            }
            *tail_slot = Some(l_head);
            out_len += remaining_len;
        } else if let Some(r_head) = right.take() {
            // If subtracting, every node's coeff must be negated.
            // Otherwise the remainder can be spliced as-is.
            if subtract {
                let mut cur: Option<NonNull<Node<F, M>>> = Some(r_head);
                while let Some(n) = cur {
                    let n_ptr = n.as_ptr();
                    let nxt = (*n_ptr).next.take();
                    (*n_ptr).coeff = -((*n_ptr).coeff);
                    *tail_slot = Some(n);
                    tail_slot = &mut (*n_ptr).next;
                    out_len += 1;
                    cur = nxt;
                }
            } else {
                let mut remaining_len = 1usize;
                let mut node = r_head.as_ref().next;
                while let Some(x) = node {
                    remaining_len += 1;
                    node = x.as_ref().next;
                }
                *tail_slot = Some(r_head);
                out_len += remaining_len;
            }
        }
    };

    let mut out = Poly {
        head: sentinel_slot.take(),
        len: out_len,
        lm_sev: 0,
        lm_coeff: F::zero(),
        lm_deg: 0,
        _marker: PhantomData,
    };
    out.refresh_cache();
    out
}

/// Merge two polynomials into one via a splice-style two-pointer
/// walk along both chains. If `subtract` is true, the second
/// operand's coefficients are negated. Allocates fresh nodes for
/// every output term (list-splice node reuse is a future
/// optimisation).
fn merge<F: Field + Copy, M: Monomial<F, W>, const W: usize>(
    _ring: &Ring<F, W>,
    a: &Poly<F, M, W>,
    b: &Poly<F, M, W>,
    subtract: bool,
) -> Poly<F, M, W> {
    let mut out_head: Option<NonNull<Node<F, M>>> = None;
    let mut tail: *mut Option<NonNull<Node<F, M>>> = &mut out_head;
    let mut out_len: usize = 0;

    let mut left = a.head;
    let mut right = b.head;

    while let (Some(l), Some(r)) = (left, right) {
        // SAFETY: live nodes from a / b.
        let l_ref = unsafe { l.as_ref() };
        let r_ref = unsafe { r.as_ref() };
        match l_ref.mono.cmp(&r_ref.mono) {
            std::cmp::Ordering::Greater => {
                let fresh = alloc(l_ref.coeff, l_ref.mono, None);
                unsafe {
                    *tail = Some(fresh);
                    tail = &mut (*fresh.as_ptr()).next;
                }
                out_len += 1;
                left = l_ref.next;
            }
            std::cmp::Ordering::Less => {
                let c = if subtract {
                    -(r_ref.coeff)
                } else {
                    r_ref.coeff
                };
                // c is nonzero as long as r.coeff is nonzero
                // (which it always is by the canonical invariant):
                // negating preserves nonzeroness.
                let fresh = alloc(c, r_ref.mono, None);
                unsafe {
                    *tail = Some(fresh);
                    tail = &mut (*fresh.as_ptr()).next;
                }
                out_len += 1;
                right = r_ref.next;
            }
            std::cmp::Ordering::Equal => {
                let bc = if subtract {
                    -(r_ref.coeff)
                } else {
                    r_ref.coeff
                };
                let s = (l_ref.coeff) + (bc);
                if !s.is_zero() {
                    let fresh = alloc(s, l_ref.mono, None);
                    unsafe {
                        *tail = Some(fresh);
                        tail = &mut (*fresh.as_ptr()).next;
                    }
                    out_len += 1;
                }
                left = l_ref.next;
                right = r_ref.next;
            }
        }
    }
    while let Some(l) = left {
        // SAFETY: live node.
        let l_ref = unsafe { l.as_ref() };
        let fresh = alloc(l_ref.coeff, l_ref.mono, None);
        unsafe {
            *tail = Some(fresh);
            tail = &mut (*fresh.as_ptr()).next;
        }
        out_len += 1;
        left = l_ref.next;
    }
    while let Some(r) = right {
        // SAFETY: live node.
        let r_ref = unsafe { r.as_ref() };
        let c = if subtract {
            -(r_ref.coeff)
        } else {
            r_ref.coeff
        };
        let fresh = alloc(c, r_ref.mono, None);
        unsafe {
            *tail = Some(fresh);
            tail = &mut (*fresh.as_ptr()).next;
        }
        out_len += 1;
        right = r_ref.next;
    }

    let mut out = Poly {
        head: out_head,
        len: out_len,
        lm_sev: 0,
        lm_coeff: F::zero(),
        lm_deg: 0,
        _marker: PhantomData,
    };
    out.refresh_cache();
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::monomial::{GrevLexTerm, MonoTerm};
    use ark_bls12_381::Fr;

    type F = Fr;

    fn mk_ring(nvars: u32, _p: u32) -> Ring<F> {
        Ring::<F>::new(nvars).unwrap()
    }

    fn mono(r: &Ring<F>, e: &[u32]) -> GrevLexTerm {
        GrevLexTerm::from(MonoTerm::from_exponents(r, e).unwrap())
    }

    #[test]
    fn zero_is_zero() {
        let p = Poly::<F, GrevLexTerm>::zero();
        assert!(p.is_zero());
        assert_eq!(p.len(), 0);
        assert!(p.leading().is_none());
    }

    #[test]
    fn from_terms_sorts_and_dedups() {
        let r = mk_ring(3, 13);
        let terms = vec![
            (F::from(3u64), mono(&r, &[1, 0, 0])),
            (F::from(5u64), mono(&r, &[0, 2, 0])),
            (F::from(7u64), mono(&r, &[1, 0, 0])),
            (F::from(0u64), mono(&r, &[0, 0, 1])),
        ];
        let p = Poly::from_terms(&r, terms);
        p.assert_canonical(&r);
        assert_eq!(p.len(), 2);
        let (c0, m0) = p.leading().unwrap();
        assert_eq!(c0, F::from(5u64));
        assert_eq!(*m0, mono(&r, &[0, 2, 0]));
        // Second term via iter().
        let second = p.iter().nth(1).unwrap();
        assert_eq!(second.0, F::from(10u64));
        assert_eq!(*second.1, mono(&r, &[1, 0, 0]));
    }

    #[test]
    fn add_and_sub_cancel() {
        let r = mk_ring(3, 13);
        let f = Poly::from_terms(
            &r,
            vec![
                (F::from(3u64), mono(&r, &[1, 0, 0])),
                (F::from(5u64), mono(&r, &[0, 2, 0])),
                (F::from(1u64), mono(&r, &[0, 0, 1])),
            ],
        );
        let g = f.sub(&f, &r);
        g.assert_canonical(&r);
        assert!(g.is_zero());
    }

    #[test]
    fn sub_mul_term_matches_slow_path() {
        let r = mk_ring(3, 13);
        let p = Poly::from_terms(
            &r,
            vec![
                (F::from(3u64), mono(&r, &[2, 1, 0])),
                (F::from(7u64), mono(&r, &[1, 0, 1])),
                (F::from(1u64), mono(&r, &[0, 0, 2])),
            ],
        );
        let q = Poly::from_terms(
            &r,
            vec![
                (F::from(4u64), mono(&r, &[1, 1, 0])),
                (F::from(5u64), mono(&r, &[0, 0, 1])),
            ],
        );
        let m = mono(&r, &[1, 0, 0]);
        let c: F = F::from(2u64);

        let mq = q.shift(&m, &r).scale(c, &r);
        let slow = p.sub(&mq, &r);
        let fast = p.sub_mul_term(c, &m, &q, &r);
        slow.assert_canonical(&r);
        fast.assert_canonical(&r);
        assert_eq!(slow, fast);
    }

    #[test]
    fn monic_is_idempotent() {
        let r = mk_ring(2, 32003);
        let p = Poly::from_terms(
            &r,
            vec![
                (F::from(17u64), mono(&r, &[3, 0])),
                (F::from(2u64), mono(&r, &[1, 1])),
                (F::from(9u64), mono(&r, &[0, 2])),
            ],
        );
        let once = p.monic(&r).unwrap();
        let twice = once.monic(&r).unwrap();
        assert_eq!(once, twice);
        assert_eq!(once.lm_coeff(), F::from(1u64));
    }

    #[test]
    fn leading_invariants() {
        let r = mk_ring(2, 7);
        let p = Poly::from_terms(
            &r,
            vec![
                (F::from(3u64), mono(&r, &[2, 0])),
                (F::from(4u64), mono(&r, &[1, 1])),
            ],
        );
        let (c, m) = p.leading().unwrap();
        assert_eq!(c, F::from(3u64));
        assert_eq!(m.0.total_deg(), 2);
        assert_eq!(p.lm_sev(), m.0.sev());
        assert_eq!(p.lm_coeff(), F::from(3u64));
        assert_eq!(p.lm_deg(), 2);
    }

    #[test]
    fn drop_leading_basic() {
        let r = mk_ring(3, 13);
        let p = Poly::from_terms(
            &r,
            vec![
                (F::from(3u64), mono(&r, &[2, 1, 0])),
                (F::from(7u64), mono(&r, &[1, 0, 1])),
                (F::from(1u64), mono(&r, &[0, 0, 2])),
            ],
        );
        let tail = p.drop_leading();
        tail.assert_canonical(&r);
        assert_eq!(tail.len(), 2);
        let (c, m) = tail.leading().unwrap();
        assert_eq!(c, F::from(7u64));
        assert_eq!(m, &mono(&r, &[1, 0, 1]));
    }

    #[test]
    fn drop_leading_in_place_o1() {
        // Peel leaders repeatedly, checking the cache and length
        // stay consistent and the poly ends up zero.
        let r = mk_ring(3, 32003);
        let mut p = Poly::from_terms(
            &r,
            vec![
                (F::from(5u64), mono(&r, &[3, 0, 0])),
                (F::from(4u64), mono(&r, &[2, 1, 0])),
                (F::from(3u64), mono(&r, &[1, 0, 1])),
                (F::from(2u64), mono(&r, &[0, 0, 2])),
                (F::from(1u64), mono(&r, &[0, 1, 0])),
            ],
        );
        for expected_len in (0..5).rev() {
            p.drop_leading_in_place();
            p.assert_canonical(&r);
            assert_eq!(p.len(), expected_len);
        }
        // Extra drop on a zero poly is a no-op.
        p.drop_leading_in_place();
        assert!(p.is_zero());
    }

    #[test]
    fn cursor_walks_all_terms() {
        let r = mk_ring(3, 32003);
        let p = Poly::from_terms(
            &r,
            vec![
                (F::from(5u64), mono(&r, &[3, 0, 0])),
                (F::from(4u64), mono(&r, &[2, 1, 0])),
                (F::from(3u64), mono(&r, &[0, 0, 2])),
            ],
        );
        let mut c = p.cursor();
        assert!(!c.is_done());
        let (c0, m0) = c.term().unwrap();
        assert_eq!(c0, F::from(5u64));
        assert_eq!(*m0, mono(&r, &[3, 0, 0]));
        c.advance();
        let (c1, _) = c.term().unwrap();
        assert_eq!(c1, F::from(4u64));
        c.advance();
        let (c2, _) = c.term().unwrap();
        assert_eq!(c2, F::from(3u64));
        c.advance();
        assert!(c.is_done());
        assert!(c.term().is_none());
        // advance past end is a no-op.
        c.advance();
        assert!(c.is_done());
    }

    #[test]
    fn add_consuming_matches_add() {
        // Round-trip: destructive add matches non-destructive add on
        // the same inputs.
        let r = mk_ring(3, 13);
        let a = Poly::from_terms(
            &r,
            vec![
                (F::from(3u64), mono(&r, &[2, 0, 0])),
                (F::from(5u64), mono(&r, &[1, 1, 0])),
                (F::from(1u64), mono(&r, &[0, 0, 2])),
            ],
        );
        let b = Poly::from_terms(
            &r,
            vec![
                (F::from(2u64), mono(&r, &[1, 1, 0])),
                (F::from(4u64), mono(&r, &[0, 2, 0])),
                (F::from(9u64), mono(&r, &[0, 0, 1])),
            ],
        );
        let expected = a.add(&b, &r);
        let got = a.clone().add_consuming(b.clone(), &r);
        got.assert_canonical(&r);
        assert_eq!(got, expected);
    }

    #[test]
    fn add_consuming_cancellation_middle() {
        // Middle-of-chain cancellation: a has x^2 + x + 1, b has -x.
        // Output should be x^2 + 1.
        let r = mk_ring(1, 13);
        let a = Poly::from_terms(
            &r,
            vec![
                (F::from(1u64), mono(&r, &[2])),
                (F::from(1u64), mono(&r, &[1])),
                (F::from(1u64), mono(&r, &[0])),
            ],
        );
        let b = Poly::from_terms(&r, vec![(F::from(12u64), mono(&r, &[1]))]); // -1
        let expected = a.add(&b, &r);
        let got = a.clone().add_consuming(b.clone(), &r);
        got.assert_canonical(&r);
        assert_eq!(got, expected);
        assert_eq!(got.len(), 2);
    }

    #[test]
    fn add_consuming_full_cancellation() {
        // f + (-f) = 0.
        let r = mk_ring(3, 13);
        let f = Poly::from_terms(
            &r,
            vec![
                (F::from(3u64), mono(&r, &[1, 0, 0])),
                (F::from(5u64), mono(&r, &[0, 2, 0])),
                (F::from(1u64), mono(&r, &[0, 0, 1])),
            ],
        );
        let neg_f = f.neg(&r);
        let got = f.clone().add_consuming(neg_f, &r);
        got.assert_canonical(&r);
        assert!(got.is_zero());
    }

    #[test]
    fn add_consuming_tail_splice_left_longer() {
        // Left has more terms past the last b-term, exercising the
        // tail-splice path for `left`.
        let r = mk_ring(3, 13);
        let a = Poly::from_terms(
            &r,
            vec![
                (F::from(3u64), mono(&r, &[3, 0, 0])),
                (F::from(5u64), mono(&r, &[2, 0, 0])),
                (F::from(7u64), mono(&r, &[1, 0, 0])),
                (F::from(2u64), mono(&r, &[0, 1, 0])),
                (F::from(4u64), mono(&r, &[0, 0, 1])),
            ],
        );
        let b = Poly::from_terms(&r, vec![(F::from(1u64), mono(&r, &[3, 0, 0]))]);
        let expected = a.add(&b, &r);
        let got = a.clone().add_consuming(b.clone(), &r);
        got.assert_canonical(&r);
        assert_eq!(got, expected);
    }

    #[test]
    fn add_consuming_tail_splice_right_longer() {
        // Right has more terms past the last a-term.
        let r = mk_ring(3, 13);
        let a = Poly::from_terms(&r, vec![(F::from(3u64), mono(&r, &[3, 0, 0]))]);
        let b = Poly::from_terms(
            &r,
            vec![
                (F::from(5u64), mono(&r, &[2, 0, 0])),
                (F::from(7u64), mono(&r, &[1, 0, 0])),
                (F::from(2u64), mono(&r, &[0, 1, 0])),
                (F::from(4u64), mono(&r, &[0, 0, 1])),
            ],
        );
        let expected = a.add(&b, &r);
        let got = a.clone().add_consuming(b.clone(), &r);
        got.assert_canonical(&r);
        assert_eq!(got, expected);
    }

    #[test]
    fn add_consuming_single_terms() {
        let r = mk_ring(2, 7);
        let a = Poly::monomial(&r, F::from(3u64), mono(&r, &[1, 0]));
        let b = Poly::monomial(&r, F::from(4u64), mono(&r, &[0, 1]));
        let expected = a.add(&b, &r);
        let got = a.clone().add_consuming(b.clone(), &r);
        got.assert_canonical(&r);
        assert_eq!(got, expected);
    }

    #[test]
    fn add_consuming_zero_operands() {
        let r = mk_ring(2, 7);
        let f = Poly::from_terms(
            &r,
            vec![
                (F::from(3u64), mono(&r, &[2, 0])),
                (F::from(4u64), mono(&r, &[1, 1])),
            ],
        );
        let z = Poly::<F, GrevLexTerm>::zero();
        // f + 0 = f.
        let got = f.clone().add_consuming(z.clone(), &r);
        got.assert_canonical(&r);
        assert_eq!(got, f);
        // 0 + f = f.
        let got = Poly::<F, GrevLexTerm>::zero().add_consuming(f.clone(), &r);
        got.assert_canonical(&r);
        assert_eq!(got, f);
        // 0 + 0 = 0.
        let got = Poly::<F, GrevLexTerm>::zero().add_consuming(Poly::<F, GrevLexTerm>::zero(), &r);
        assert!(got.is_zero());
    }

    #[test]
    fn sub_mm_mult_qq_consuming_matches_sub_mul_term() {
        // Round-trip: destructive equals non-destructive on the same
        // inputs.
        let r = mk_ring(3, 13);
        let p = Poly::from_terms(
            &r,
            vec![
                (F::from(3u64), mono(&r, &[2, 1, 0])),
                (F::from(7u64), mono(&r, &[1, 0, 1])),
                (F::from(1u64), mono(&r, &[0, 0, 2])),
            ],
        );
        let q = Poly::from_terms(
            &r,
            vec![
                (F::from(4u64), mono(&r, &[1, 1, 0])),
                (F::from(5u64), mono(&r, &[0, 0, 1])),
            ],
        );
        let m = mono(&r, &[1, 0, 0]);
        let c: F = F::from(2u64);

        let expected = p.sub_mul_term(c, &m, &q, &r);
        let got = p.clone().sub_mm_mult_qq_consuming(c, &m, &q, &r);
        got.assert_canonical(&r);
        assert_eq!(got, expected);
    }

    #[test]
    fn sub_mm_mult_qq_consuming_cancellation() {
        // Choose inputs so a specific term cancels.
        let r = mk_ring(2, 13);
        // p = x^2 + xy + y^2. q = x + y. m = x, c = 1.
        // p - 1 * x * (x + y) = p - (x^2 + xy) = y^2.
        let p = Poly::from_terms(
            &r,
            vec![
                (F::from(1u64), mono(&r, &[2, 0])),
                (F::from(1u64), mono(&r, &[1, 1])),
                (F::from(1u64), mono(&r, &[0, 2])),
            ],
        );
        let q = Poly::from_terms(
            &r,
            vec![
                (F::from(1u64), mono(&r, &[1, 0])),
                (F::from(1u64), mono(&r, &[0, 1])),
            ],
        );
        let m = mono(&r, &[1, 0]);
        let got = p
            .clone()
            .sub_mm_mult_qq_consuming(F::from(1u64), &m, &q, &r);
        got.assert_canonical(&r);
        let expected = p.sub_mul_term(F::from(1u64), &m, &q, &r);
        assert_eq!(got, expected);
        assert_eq!(got.len(), 1);
    }

    #[test]
    fn sub_mm_mult_qq_consuming_tail_splice_self_exhausts() {
        // `p` exhausts before `q*m*c` does — exercises the
        // "self exhausts; q may still have terms" path.
        let r = mk_ring(2, 13);
        // p = x^3 (leading only). q has many smaller terms after
        // matching x^2 via m = x.
        let p = Poly::from_terms(&r, vec![(F::from(3u64), mono(&r, &[3, 0]))]);
        let q = Poly::from_terms(
            &r,
            vec![
                (F::from(1u64), mono(&r, &[2, 0])),
                (F::from(2u64), mono(&r, &[1, 1])),
                (F::from(4u64), mono(&r, &[0, 2])),
                (F::from(5u64), mono(&r, &[0, 0])),
            ],
        );
        let m = mono(&r, &[1, 0]);
        let c: F = F::from(1u64);
        let expected = p.sub_mul_term(c, &m, &q, &r);
        let got = p.clone().sub_mm_mult_qq_consuming(c, &m, &q, &r);
        got.assert_canonical(&r);
        assert_eq!(got, expected);
    }

    #[test]
    fn sub_mm_mult_qq_consuming_tail_splice_q_exhausts() {
        // `q*m*c` exhausts before `p` does.
        let r = mk_ring(2, 13);
        let p = Poly::from_terms(
            &r,
            vec![
                (F::from(3u64), mono(&r, &[5, 0])),
                (F::from(2u64), mono(&r, &[4, 0])),
                (F::from(1u64), mono(&r, &[3, 0])),
                (F::from(4u64), mono(&r, &[0, 1])),
                (F::from(5u64), mono(&r, &[0, 0])),
            ],
        );
        let q = Poly::from_terms(&r, vec![(F::from(1u64), mono(&r, &[4, 0]))]);
        let m = mono(&r, &[1, 0]);
        let c: F = F::from(1u64);
        let expected = p.sub_mul_term(c, &m, &q, &r);
        let got = p.clone().sub_mm_mult_qq_consuming(c, &m, &q, &r);
        got.assert_canonical(&r);
        assert_eq!(got, expected);
    }

    #[test]
    fn sub_mm_mult_qq_consuming_zero_coeff() {
        // c = 0 returns self unchanged.
        let r = mk_ring(2, 13);
        let p = Poly::from_terms(
            &r,
            vec![
                (F::from(3u64), mono(&r, &[2, 0])),
                (F::from(4u64), mono(&r, &[1, 1])),
            ],
        );
        let q = Poly::from_terms(&r, vec![(F::from(1u64), mono(&r, &[1, 0]))]);
        let m = mono(&r, &[0, 1]);
        let got = p
            .clone()
            .sub_mm_mult_qq_consuming(F::from(0u64), &m, &q, &r);
        got.assert_canonical(&r);
        assert_eq!(got, p);
    }

    #[test]
    fn sub_mm_mult_qq_consuming_zero_q() {
        // q = 0 returns self unchanged.
        let r = mk_ring(2, 13);
        let p = Poly::from_terms(
            &r,
            vec![
                (F::from(3u64), mono(&r, &[2, 0])),
                (F::from(4u64), mono(&r, &[1, 1])),
            ],
        );
        let q = Poly::<F, GrevLexTerm>::zero();
        let m = mono(&r, &[0, 1]);
        let got = p
            .clone()
            .sub_mm_mult_qq_consuming(F::from(2u64), &m, &q, &r);
        got.assert_canonical(&r);
        assert_eq!(got, p);
    }

    #[test]
    fn sub_mm_mult_qq_consuming_self_zero() {
        // self = 0; result is -c*m*q, same as Poly::zero().sub_mul_term(...).
        let r = mk_ring(2, 13);
        let q = Poly::from_terms(
            &r,
            vec![
                (F::from(3u64), mono(&r, &[1, 0])),
                (F::from(2u64), mono(&r, &[0, 1])),
            ],
        );
        let m = mono(&r, &[1, 0]);
        let c: F = F::from(2u64);
        let expected = Poly::<F, GrevLexTerm>::zero().sub_mul_term(c, &m, &q, &r);
        let got = Poly::<F, GrevLexTerm>::zero().sub_mm_mult_qq_consuming(c, &m, &q, &r);
        got.assert_canonical(&r);
        assert_eq!(got, expected);
    }

    #[test]
    fn iterative_drop_survives_long_chain() {
        // A recursive drop would overflow the stack on a chain of
        // this length. The custom iterative Drop must handle it.
        //
        // Exponents must fit the 7-bit-per-variable budget
        // (ADR-005), so we spread the chain across enough variables
        // to give us N distinct monomials at or below that cap. With
        // 4 variables each up to exponent 63 we get 64^4 = 16.8M
        // possible monomials — plenty for a 100 000-term chain, and
        // every pair is distinct so the descending-order contract
        // is trivial.
        let r = mk_ring(4, 32003);
        let n: usize = 100_000;

        let mut distinct: Vec<GrevLexTerm> = Vec::with_capacity(n);
        'outer: for d in 0u32..64 {
            for c in 0u32..64 {
                for b in 0u32..64 {
                    for a in 0u32..64 {
                        if distinct.len() >= n {
                            break 'outer;
                        }
                        distinct.push(mono(&r, &[a, b, c, d]));
                    }
                }
            }
        }
        // Sort descending under the ring's ordering.
        distinct.sort_by(|x, y| y.cmp(x));
        let terms: Vec<(F, GrevLexTerm)> =
            distinct.into_iter().map(|m| (F::from(1u64), m)).collect();
        let p = Poly::from_descending_terms_unchecked(&r, terms);
        assert_eq!(p.len(), n);
        // When `p` is dropped at scope exit, iterative Drop should
        // walk the chain without recursing. If this test ever starts
        // overflowing the stack, Drop has regressed to recursive.
        drop(p);
    }
}
