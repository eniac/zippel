//! Flat-array backend for [`Poly`]: parallel `Vec<F>` +
//! `Vec<M>` with an internal `head` cursor.
//!
//! This is the default backend selected when the `linked_list_poly`
//! Cargo feature is **off** (ADR-001, ADR-014). The parent module
//! [`crate::poly`] re-exports this backend's `Poly` and `PolyCursor`
//! under those names; the feature flag decides at compile time whether
//! `Poly` means `poly_vec::Poly` (this file) or `poly_list::Poly`
//! (the linked-list backend).
//!
//! Invariants (checked by [`Poly::assert_canonical`]):
//!
//! 1. `coeffs.len() == terms.len()`.
//! 2. All coefficients are nonzero (zeros excluded).
//! 3. Monomials are strictly descending under the ring's ordering (no
//!    duplicates, no unsorted runs).
//! 4. `lm_*` fields match `terms[head]` / `coeffs[head]` when nonempty.
//!
//! Mathicgb's `Poly.hpp` is the structural template (parallel arrays,
//! leading-term at index 0). This implementation does not copy mathicgb
//! code.

use crate::field::Field;
use crate::monomial::Monomial;
use crate::ring::Ring;
use std::marker::PhantomData;

/// A sparse polynomial in a [`Ring`].
///
/// See module documentation for invariants. `Send + Sync`: all fields
/// are owned vectors of plain integer data.
///
/// The live terms are `coeffs[head..]` / `terms[head..]`. `head`
/// advances when [`drop_leading_in_place`](Self::drop_leading_in_place)
/// peels a leader — that's an O(1) cursor bump rather than the O(n)
/// `Vec::remove(0)` that the previous representation required. The
/// dead prefix is reclaimed when the `Poly` is cloned (see the
/// custom `Clone` impl) or when it falls out of scope. All accessors
/// (`coeffs()`, `terms()`, `iter()`, `leading()`, `len()`,
/// `is_zero()`) operate on the live region.
#[derive(Debug)]
pub struct Poly<F: Field + Copy, M: Monomial<F, W>, const W: usize = 4> {
    /// Coefficients in the same order as `terms`. All nonzero.
    coeffs: Vec<F>,
    /// Monomials in strictly descending order.
    terms: Vec<M>,
    _field: PhantomData<F>,
    /// Index of the live leading term. `coeffs[head..]` and
    /// `terms[head..]` are the algebraically meaningful slice;
    /// indices below `head` are abandoned but not yet freed.
    /// Always `<= terms.len()`; equality means the polynomial is zero.
    head: usize,
    /// Cached leading-term sev (`terms[head].sev()`); 0 when empty.
    lm_sev: u64,
    /// Cached leading coefficient (`coeffs[head]`); F::zero() when empty.
    lm_coeff: F,
    /// Cached leading monomial degree (`terms[head].total_deg()`);
    /// 0 when empty.
    lm_deg: u32,
}

impl<F: Field + Copy, M: Monomial<F, W>, const W: usize> Clone for Poly<F, M, W> {
    /// Clone only the live tail (`coeffs[head..]` / `terms[head..]`)
    /// so the dead prefix is dropped at every clone site. This keeps
    /// the bucket-slot reuse pattern (drop_leading repeatedly, then
    /// absorb a new poly via `merge` which constructs fresh) from
    /// accumulating dead memory across the chain of intermediate
    /// clones a caller might make.
    fn clone(&self) -> Self {
        let coeffs = self.coeffs[self.head..].to_vec();
        let terms = self.terms[self.head..].to_vec();
        Self {
            coeffs,
            terms,
            _field: PhantomData,
            head: 0,
            lm_sev: self.lm_sev,
            lm_coeff: self.lm_coeff,
            lm_deg: self.lm_deg,
        }
    }
}

impl<F: Field + Copy, M: Monomial<F, W>, const W: usize> Poly<F, M, W> {
    // ----- Constructors -----

    /// The zero polynomial.
    pub fn zero() -> Self {
        Self {
            coeffs: Vec::new(),
            terms: Vec::new(),
            _field: PhantomData,
            head: 0,
            lm_sev: 0,
            lm_coeff: F::zero(),
            lm_deg: 0,
        }
    }

    /// A polynomial with a single term `c * m`. Returns the zero
    /// polynomial if `c.is_zero()`.
    pub fn monomial(_ring: &Ring<F, W>, c: F, m: M) -> Self {
        if c.is_zero() {
            return Self::zero();
        }
        let lm_sev = m.as_mono_term().sev();
        let lm_deg = m.as_mono_term().total_deg();
        Self {
            coeffs: vec![c],
            terms: vec![m],
            _field: PhantomData,
            head: 0,
            lm_sev,
            lm_coeff: c,
            lm_deg,
        }
    }

    /// Build a polynomial from a sequence of `(coeff, monomial)` pairs
    /// that is already in strictly-descending monomial order with no
    /// duplicates and no zero coefficients.
    ///
    /// This is the zero-overhead fast path used by hot loops that
    /// already know they produced descending, deduped, nonzero terms:
    /// `kbucket::build_neg_cmp` (monomial multiplication by a fixed m
    /// preserves descending order in degrevlex), and `bba::reduce_tail`
    /// (whose `done` vector accumulates in descending order by
    /// construction from the bucket's `extract_leading`).
    ///
    /// Preconditions (checked only in debug):
    /// * `terms` is strictly descending under the ring's ordering.
    /// * No monomial appears twice.
    /// * Every coefficient is nonzero.
    pub fn from_descending_terms_unchecked(_ring: &Ring<F, W>, terms: Vec<(F, M)>) -> Self {
        if terms.is_empty() {
            return Self::zero();
        }
        let mut coeffs: Vec<F> = Vec::with_capacity(terms.len());
        let mut mons: Vec<M> = Vec::with_capacity(terms.len());
        for (c, m) in terms {
            debug_assert!(!c.is_zero(), "from_descending_terms_unchecked: zero coeff");
            if cfg!(debug_assertions)
                && let Some(prev) = mons.last()
            {
                debug_assert!(
                    prev.cmp(&m).is_gt(),
                    "from_descending_terms_unchecked: not strictly descending"
                );
            }
            coeffs.push(c);
            mons.push(m);
        }
        let mut out = Self {
            coeffs,
            terms: mons,
            _field: PhantomData,
            head: 0,
            lm_sev: 0,
            lm_coeff: F::zero(),
            lm_deg: 0,
        };
        out.refresh_cache();
        out
    }

    /// Build a polynomial directly from pre-built parallel vectors of
    /// coefficients and monomials. Same preconditions as
    /// [`from_descending_terms_unchecked`] but skips the tuple
    /// unpacking: the vectors are moved in place. Used by the hot
    /// `kbucket::build_neg_cmp` loop where building parallel vectors
    /// is cheaper than pushing `(F, MonoTerm)` tuples one at a
    /// time into a single vec.
    pub fn from_descending_parallel_unchecked(
        ring: &Ring<F, W>,
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
        let _ = ring;
        let mut out = Self {
            coeffs,
            terms,
            _field: PhantomData,
            head: 0,
            lm_sev: 0,
            lm_coeff: F::zero(),
            lm_deg: 0,
        };
        out.refresh_cache();
        out
    }

    /// Build a polynomial from an unsorted sequence of `(coeff, monomial)`
    /// pairs. Duplicates are summed, zeros are dropped, the result is
    /// sorted into descending order. Primarily for tests and round-trip
    /// from textual input.
    pub fn from_terms(_ring: &Ring<F, W>, terms: Vec<(F, M)>) -> Self {
        // Sort descending by monomial.
        let mut terms = terms;
        terms.sort_by_key(|b| std::cmp::Reverse(b.1));

        let mut coeffs: Vec<F> = Vec::with_capacity(terms.len());
        let mut mons: Vec<M> = Vec::with_capacity(terms.len());

        for (c, m) in terms {
            if c.is_zero() {
                continue;
            }
            if let Some(last) = mons.last()
                && last == &m
            {
                // Merge with previous term.
                let idx = coeffs.len() - 1;
                coeffs[idx] += c;
                if coeffs[idx].is_zero() {
                    coeffs.pop();
                    mons.pop();
                }
                continue;
            }
            coeffs.push(c);
            mons.push(m);
        }

        let mut p = Self {
            coeffs,
            terms: mons,
            _field: PhantomData,
            head: 0,
            lm_sev: 0,
            lm_coeff: F::zero(),
            lm_deg: 0,
        };
        p.refresh_cache();
        p
    }

    // ----- Cache maintenance -----

    fn refresh_cache(&mut self) {
        if let Some(m) = self.terms.get(self.head) {
            self.lm_sev = m.as_mono_term().sev();
            self.lm_deg = m.as_mono_term().total_deg();
            self.lm_coeff = self.coeffs[self.head];
        } else {
            self.lm_sev = 0;
            self.lm_coeff = F::zero();
            self.lm_deg = 0;
        }
    }

    // ----- Accessors -----

    /// Number of live (post-`head`) terms.
    #[allow(clippy::len_without_is_empty)] // `is_zero` is the domain-natural spelling; see below.
    #[inline]
    pub fn len(&self) -> usize {
        self.terms.len() - self.head
    }

    /// Whether this is the zero polynomial.
    ///
    /// We deliberately expose `is_zero` instead of `is_empty`: a
    /// polynomial with zero terms *is* the zero polynomial, so this
    /// spells the same thing in ring-theoretic terminology.
    #[inline]
    pub fn is_zero(&self) -> bool {
        self.head == self.terms.len()
    }

    /// Iterate over `(coeff, monomial)` pairs in descending order.
    pub fn iter(&self) -> impl Iterator<Item = (F, &M)> + '_ {
        self.coeffs[self.head..]
            .iter()
            .copied()
            .zip(self.terms[self.head..].iter())
    }

    /// Leading term `(coeff, &monomial)`, or `None` if zero.
    pub fn leading(&self) -> Option<(F, &M)> {
        if self.is_zero() {
            None
        } else {
            Some((self.coeffs[self.head], &self.terms[self.head]))
        }
    }

    /// Leading short exponent vector. 0 when zero (caller should check
    /// `is_zero` before interpreting).
    #[inline]
    pub fn lm_sev(&self) -> u64 {
        self.lm_sev
    }

    /// Leading coefficient. F::zero() when zero.
    #[inline]
    pub fn lm_coeff(&self) -> F {
        self.lm_coeff
    }

    /// Leading monomial total degree. 0 when zero.
    #[inline]
    pub fn lm_deg(&self) -> u32 {
        self.lm_deg
    }

    /// Private helper: live-region view of coefficients. Exists so
    /// the in-module implementations (merge, sub_mul_term, eq, the
    /// canonicality check, and a handful of tests) can work on the
    /// active tail without going through a public slice API. The
    /// previous public `coeffs()` / `terms()` methods were dropped
    /// when the cursor API landed (ADR-014) — they can't be
    /// implemented by the linked-list backend without materialising
    /// the whole poly.
    #[inline]
    fn live_coeffs(&self) -> &[F] {
        &self.coeffs[self.head..]
    }

    /// Private helper: live-region view of monomials. See
    /// [`Self::live_coeffs`] for the rationale.
    #[inline]
    fn live_terms(&self) -> &[M] {
        &self.terms[self.head..]
    }

    /// A cursor positioned at the leading term (or at end if zero).
    ///
    /// Both the `Vec`-backed and the future `List`-backed `Poly`
    /// expose the same cursor API so callers can walk a polynomial
    /// in descending order without assuming random access. The
    /// cursor is cheap (`Copy`) and carries only a reference to the
    /// underlying storage plus its position; the reducer stores one
    /// per in-flight reducer.
    #[inline]
    pub fn cursor(&self) -> PolyCursor<'_, F, M, W> {
        PolyCursor {
            poly: self,
            idx: self.head,
        }
    }

    /// Return a new polynomial with the leading term removed. If `self`
    /// is zero or a single term, returns the zero polynomial.
    ///
    /// The tail of a canonical polynomial is itself canonical (terms are
    /// strictly descending and coefficients all nonzero), so this skips
    /// the sort+dedup pass that `from_terms` would do.
    pub fn drop_leading(&self) -> Self {
        if self.len() <= 1 {
            return Self::zero();
        }
        let mut out = Self {
            coeffs: self.coeffs[self.head + 1..].to_vec(),
            terms: self.terms[self.head + 1..].to_vec(),
            _field: PhantomData,
            head: 0,
            lm_sev: 0,
            lm_coeff: F::zero(),
            lm_deg: 0,
        };
        out.refresh_cache();
        out
    }

    /// In-place variant of [`drop_leading`](Self::drop_leading).
    ///
    /// Bumps the internal `head` cursor by one — O(1). Does not free
    /// the old leader's slot in the underlying `Vec`s; the dead prefix
    /// is reclaimed when this `Poly` is cloned or dropped.
    ///
    /// Used by the geobucket's cancellation peel in
    /// [`KBucket::leading`](crate::kbucket::KBucket::leading) and by
    /// [`KBucket::extract_leading`](crate::kbucket::KBucket::extract_leading).
    /// In a long bucket-slot lifetime (many drops without an
    /// intervening absorb) the slot can hold a Poly whose live region
    /// is much smaller than its allocation; the next `merge`/`absorb`
    /// constructs a fresh Poly with `head == 0`, returning that memory
    /// to bounded use.
    pub fn drop_leading_in_place(&mut self) {
        if self.is_zero() {
            return;
        }
        self.head += 1;
        self.refresh_cache();
    }

    // ----- Arithmetic -----

    /// In-place: `self = self + other`. Linear merge by monomial order.
    pub fn add_assign(&mut self, other: &Poly<F, M, W>, ring: &Ring<F, W>) {
        if other.is_zero() {
            return;
        }
        if self.is_zero() {
            *self = other.clone();
            return;
        }
        *self = merge(ring, self, other, /* subtract = */ false);
    }

    /// Out-of-place addition. `other` may alias self (Rust borrow rules
    /// prevent true aliasing at the type level, but we accept any two
    /// references including `&a, &a`).
    pub fn add(&self, other: &Poly<F, M, W>, ring: &Ring<F, W>) -> Poly<F, M, W> {
        if other.is_zero() {
            return self.clone();
        }
        if self.is_zero() {
            return other.clone();
        }
        merge(ring, self, other, false)
    }

    /// Consuming addition. Equivalent to `self.add(&other, ring)` on the
    /// Vec backend — there is no splice story for flat arrays, so the
    /// by-value inputs are simply dropped after the non-destructive
    /// merge produces its output. The method exists so callers (notably
    /// `kbucket::absorb`) can use the same API regardless of backend;
    /// on the List backend (ADR-015) this variant splices input nodes
    /// directly into the output chain. See `p_Add_q` in
    /// `~/Singular/libpolys/polys/templates/p_Add_q__T.cc`.
    pub fn add_consuming(self, other: Poly<F, M, W>, ring: &Ring<F, W>) -> Poly<F, M, W> {
        self.add(&other, ring)
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
    pub fn neg(&self, _ring: &Ring<F, W>) -> Poly<F, M, W> {
        let coeffs: Vec<F> = self.coeffs[self.head..].iter().map(|&c| -c).collect();
        let mut out = Self {
            coeffs,
            terms: self.terms[self.head..].to_vec(),
            _field: PhantomData,
            head: 0,
            lm_sev: 0,
            lm_coeff: F::zero(),
            lm_deg: 0,
        };
        out.refresh_cache();
        out
    }

    /// Multiply every coefficient by a scalar. Returns zero if `c.is_zero()`.
    pub fn scale(&self, c: F, _ring: &Ring<F, W>) -> Poly<F, M, W> {
        if c.is_zero() || self.is_zero() {
            return Self::zero();
        }
        let coeffs: Vec<F> = self.coeffs[self.head..].iter().map(|&ci| ci * c).collect();
        let mut out = Self {
            coeffs,
            terms: self.terms[self.head..].to_vec(),
            _field: PhantomData,
            head: 0,
            lm_sev: 0,
            lm_coeff: F::zero(),
            lm_deg: 0,
        };
        out.refresh_cache();
        out
    }

    /// Multiply every monomial by `m` (no scalar scaling). Per ADR-018,
    /// the caller's ring construction must ensure no product overflows
    /// the 7-bit per-variable budget; release builds do not check.
    pub fn shift(&self, m: &M, ring: &Ring<F, W>) -> Poly<F, M, W> {
        if self.is_zero() {
            return Self::zero();
        }
        let mut terms = Vec::with_capacity(self.len());
        for t in &self.terms[self.head..] {
            terms.push(t.mul(m, ring));
        }
        // Descending order is preserved: monomial multiplication by a
        // fixed m is monotone in degrevlex.
        let mut out = Self {
            coeffs: self.coeffs[self.head..].to_vec(),
            terms,
            _field: PhantomData,
            head: 0,
            lm_sev: 0,
            lm_coeff: F::zero(),
            lm_deg: 0,
        };
        out.refresh_cache();
        out
    }

    /// Standard multiplication. Straightforward O(|f|·|g|) using a
    /// merge-based accumulator; fine for tests. A heap-based Johnson
    /// multiplication is future work. Per ADR-018, the caller must
    /// ensure no product overflows.
    pub fn mul(&self, other: &Poly<F, M, W>, ring: &Ring<F, W>) -> Poly<F, M, W> {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        let mut acc: Vec<(F, M)> = Vec::with_capacity(self.len() * other.len());
        for (ca, ma) in self.iter() {
            for (cb, mb) in other.iter() {
                let m = ma.mul(mb, ring);
                let c = ca * cb;
                if !c.is_zero() {
                    acc.push((c, m));
                }
            }
        }
        Self::from_terms(ring, acc)
    }

    /// The inner reduction step `p - c * m * q`.
    ///
    /// This is the single hottest operation inside the bba driver — it
    /// is the equivalent of Singular's `p_Minus_mm_Mult_qq` (see
    /// `~/Singular/libpolys/polys/pInline2.h`) and of mathicgb's
    /// `Poly::combineInto`. We materialise `m*q` lazily during the
    /// merge so no intermediate polynomial is allocated.
    ///
    /// Per ADR-018, the caller's ring construction must ensure every
    /// `m * q[i]` product stays in-range; release builds do not check.
    pub fn sub_mul_term(&self, c: F, m: &M, q: &Poly<F, M, W>, ring: &Ring<F, W>) -> Poly<F, M, W> {
        if c.is_zero() || q.is_zero() {
            return self.clone();
        }

        let s_c = self.live_coeffs();
        let s_m = self.live_terms();
        let q_c = q.live_coeffs();
        let q_m = q.live_terms();

        // Walk `self` and `c * m * q` with a two-pointer merge.
        let mut out_c: Vec<F> = Vec::with_capacity(s_c.len() + q_c.len());
        let mut out_m: Vec<M> = Vec::with_capacity(s_m.len() + q_m.len());

        let mut i = 0usize; // index into self.live
        let mut j = 0usize; // index into q.live

        while i < s_m.len() && j < q_m.len() {
            // Next term from `c*m*q` is (c * q_c[j], m * q_m[j]).
            let mq_term_mon = m.mul(&q_m[j], ring);
            match s_m[i].cmp(&mq_term_mon) {
                std::cmp::Ordering::Greater => {
                    out_c.push(s_c[i]);
                    out_m.push(s_m[i]);
                    i += 1;
                }
                std::cmp::Ordering::Less => {
                    // subtract: output is 0 - (c * q_c[j]).
                    let neg = -(c * q_c[j]);
                    if !neg.is_zero() {
                        out_c.push(neg);
                        out_m.push(mq_term_mon);
                    }
                    j += 1;
                }
                std::cmp::Ordering::Equal => {
                    let cmq = c * q_c[j];
                    let diff = s_c[i] - cmq;
                    if !diff.is_zero() {
                        out_c.push(diff);
                        out_m.push(s_m[i]);
                    }
                    i += 1;
                    j += 1;
                }
            }
        }
        while i < s_m.len() {
            out_c.push(s_c[i]);
            out_m.push(s_m[i]);
            i += 1;
        }
        while j < q_m.len() {
            let neg = -(c * q_c[j]);
            if !neg.is_zero() {
                out_c.push(neg);
                out_m.push(m.mul(&q_m[j], ring));
            }
            j += 1;
        }

        let mut out = Self {
            coeffs: out_c,
            terms: out_m,
            _field: PhantomData,
            head: 0,
            lm_sev: 0,
            lm_coeff: F::zero(),
            lm_deg: 0,
        };
        out.refresh_cache();
        out
    }

    /// Consuming variant of [`sub_mul_term`](Self::sub_mul_term). Same
    /// semantics as `self.sub_mul_term(c, m, &q, ring)` on the Vec
    /// backend — the by-value `self` is dropped after the result is
    /// produced. Exists so callers (notably `kbucket::minus_m_mult_p`)
    /// can use the same API regardless of backend; on the List backend
    /// (ADR-015) this variant destructively reuses `self`'s nodes, and
    /// allocates new nodes only for the `m * q[i]` products it needs
    /// to emit. See `p_Minus_mm_Mult_qq` in
    /// `~/Singular/libpolys/polys/templates/p_Minus_mm_Mult_qq__T.cc`.
    pub fn sub_mm_mult_qq_consuming(
        self,
        c: F,
        m: &M,
        q: &Poly<F, M, W>,
        ring: &Ring<F, W>,
    ) -> Poly<F, M, W> {
        self.sub_mul_term(c, m, q, ring)
    }

    /// Return a scalar multiple that makes the leading coefficient 1.
    /// Zero is returned unchanged. Requires a nonzero leading coefficient
    /// that's invertible (always true over a prime field for nonzero lc).
    pub fn monic(&self, ring: &Ring<F, W>) -> Option<Poly<F, M, W>> {
        if self.is_zero() {
            return Some(Self::zero());
        }
        let lc = self.lm_coeff;
        if lc.is_one() {
            return Some(self.clone());
        }
        let inv = lc.inverse()?;
        Some(self.scale(inv, ring))
    }

    // ----- Invariants -----

    /// Panic if any internal invariant is violated.
    pub fn assert_canonical(&self, ring: &Ring<F, W>) {
        assert_eq!(self.coeffs.len(), self.terms.len(), "length mismatch");
        assert!(
            self.head <= self.terms.len(),
            "head {} out of range (terms.len = {})",
            self.head,
            self.terms.len()
        );
        let live_c = self.live_coeffs();
        let live_m = self.live_terms();
        for (k, (&c, m)) in live_c.iter().zip(live_m.iter()).enumerate() {
            assert!(!c.is_zero(), "live coeff[{k}] is zero");
            m.as_mono_term().assert_canonical(ring);
        }
        for w in live_m.windows(2) {
            let ord = w[0].cmp(&w[1]);
            assert!(
                ord == std::cmp::Ordering::Greater,
                "live terms not strictly descending: got {ord:?}"
            );
        }
        // Cached leading fields agree with the live leading term.
        if self.is_zero() {
            assert_eq!(self.lm_sev, 0);
            assert!(self.lm_coeff.is_zero());
            assert_eq!(self.lm_deg, 0);
        } else {
            assert_eq!(self.lm_sev, self.terms[self.head].as_mono_term().sev());
            assert_eq!(self.lm_coeff, self.coeffs[self.head]);
            assert_eq!(
                self.lm_deg,
                self.terms[self.head].as_mono_term().total_deg()
            );
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
/// Obtain one with [`Poly::cursor`]. The cursor is `Copy` and cheap;
/// it holds a reference to the polynomial and a position. Both
/// `Vec`-backed and `List`-backed `Poly` back-ends expose this same
/// cursor shape, so consumers (notably [`crate::reducer::Reducer`])
/// work uniformly regardless of storage choice.
///
/// On the `Vec` backend the position is an index into the parallel
/// arrays; on the `List` backend it is an `Option<&Node>`. Callers
/// never observe the difference: [`term`](Self::term) always returns
/// `Some((coeff, &monomial))` when live and `None` once exhausted,
/// [`advance`](Self::advance) steps one term forward, and
/// [`is_done`](Self::is_done) reports exhaustion.
#[derive(Clone, Copy, Debug)]
pub struct PolyCursor<'a, F: Field + Copy, M: Monomial<F, W>, const W: usize = 4> {
    poly: &'a Poly<F, M, W>,
    /// Index into the parallel-array storage. Always in `[head, terms.len()]`;
    /// equality with `terms.len()` means exhausted.
    idx: usize,
}

impl<'a, F: Field + Copy, M: Monomial<F, W>, const W: usize> PolyCursor<'a, F, M, W> {
    /// Current term `(coeff, &monomial)`, or `None` if exhausted.
    #[inline]
    pub fn term(&self) -> Option<(F, &'a M)> {
        if self.idx < self.poly.terms.len() {
            Some((self.poly.coeffs[self.idx], &self.poly.terms[self.idx]))
        } else {
            None
        }
    }

    /// Advance one term. No-op once exhausted (`is_done` stays true).
    #[inline]
    pub fn advance(&mut self) {
        if self.idx < self.poly.terms.len() {
            self.idx += 1;
        }
    }

    /// True once all terms have been walked.
    #[inline]
    pub fn is_done(&self) -> bool {
        self.idx >= self.poly.terms.len()
    }
}

impl<F: Field + Copy, M: Monomial<F, W>, const W: usize> PartialEq for Poly<F, M, W> {
    fn eq(&self, other: &Self) -> bool {
        // Compare the live regions only — `head` may differ between
        // two algebraically equal polys depending on their drop history.
        self.live_coeffs() == other.live_coeffs() && self.live_terms() == other.live_terms()
    }
}
impl<F: Field + Copy, M: Monomial<F, W>, const W: usize> Eq for Poly<F, M, W> {}

/// Merge two sorted polynomials into one. If `subtract` is true, the
/// second operand's coefficients are negated.
///
/// Implementation per ADR-006: pre-allocates the output to the
/// upper-bound capacity `a.len() + b.len()`, writes through
/// `Vec::spare_capacity_mut()` with `MaybeUninit::write`, and finalises
/// the length once via `set_len` instead of pushing one term at a
/// time. Cancellation is branch-free: the write happens
/// unconditionally and the cursor is incremented only when the
/// resulting coefficient is nonzero. This mirrors FLINT's
/// `_nmod_mpoly_add` (`~/flint/src/nmod_mpoly/add.c:16-124`).
fn merge<F: Field + Copy, M: crate::monomial::Monomial<F, W>, const W: usize>(
    _ring: &Ring<F, W>,
    a: &Poly<F, M, W>,
    b: &Poly<F, M, W>,
    subtract: bool,
) -> Poly<F, M, W> {
    let a_c = a.live_coeffs();
    let a_m = a.live_terms();
    let b_c = b.live_coeffs();
    let b_m = b.live_terms();
    let cap = a_c.len() + b_c.len();
    let mut out_c: Vec<F> = Vec::with_capacity(cap);
    let mut out_m: Vec<M> = Vec::with_capacity(cap);

    // Number of initialised slots written so far. Tracked outside the
    // inner block so the final `set_len` can read it after the
    // spare-capacity borrows have been dropped.
    let mut k: usize = 0;
    {
        let spare_c = out_c.spare_capacity_mut();
        let spare_m = out_m.spare_capacity_mut();
        let mut i = 0usize;
        let mut j = 0usize;

        while i < a_m.len() && j < b_m.len() {
            match a_m[i].cmp(&b_m[j]) {
                std::cmp::Ordering::Greater => {
                    spare_c[k].write(a_c[i]);
                    spare_m[k].write(a_m[i]);
                    k += 1;
                    i += 1;
                }
                std::cmp::Ordering::Less => {
                    let c = if subtract { -b_c[j] } else { b_c[j] };
                    spare_c[k].write(c);
                    spare_m[k].write(b_m[j]);
                    // Branch-free cancellation skip: write
                    // unconditionally; advance k only on nonzero.
                    // The next iteration overwrites the same slot if
                    // k didn't advance.
                    k += (!c.is_zero()) as usize;
                    j += 1;
                }
                std::cmp::Ordering::Equal => {
                    let bc = if subtract { -b_c[j] } else { b_c[j] };
                    let s = a_c[i] + bc;
                    spare_c[k].write(s);
                    spare_m[k].write(a_m[i]);
                    k += (!s.is_zero()) as usize;
                    i += 1;
                    j += 1;
                }
            }
        }
        while i < a_m.len() {
            spare_c[k].write(a_c[i]);
            spare_m[k].write(a_m[i]);
            k += 1;
            i += 1;
        }
        while j < b_m.len() {
            let c = if subtract { -b_c[j] } else { b_c[j] };
            spare_c[k].write(c);
            spare_m[k].write(b_m[j]);
            k += (!c.is_zero()) as usize;
            j += 1;
        }
    }
    // SAFETY: We have written exactly `k` initialised slots starting
    // at index 0 in both `out_c` and `out_m`. Slots in [k, capacity)
    // may have been written to by the branch-free cancellation pattern
    // (their bytes are non-canonical garbage), but `set_len(k)`
    // truncates them out of the live region so they are never read
    // and never dropped via the Vec's destructor. Both `F` and
    // `MonoTerm` (POD struct of u64s and u32s) have no Drop side
    // effects, so no resource leak occurs.
    unsafe {
        out_c.set_len(k);
        out_m.set_len(k);
    }
    let mut out = Poly {
        coeffs: out_c,
        terms: out_m,
        _field: PhantomData,
        head: 0,
        lm_sev: 0,
        lm_coeff: F::zero(),
        lm_deg: 0,
    };
    out.refresh_cache();
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::monomial::{GrevLexTerm, MonoTerm};
    use ark_bls12_381::Fr;
    use ark_ff::{One, Zero};

    fn mk_ring(nvars: u32) -> Ring<Fr> {
        Ring::<Fr>::new(nvars).unwrap()
    }

    fn mono(r: &Ring<Fr>, e: &[u32]) -> GrevLexTerm {
        GrevLexTerm::from(MonoTerm::from_exponents(r, e).unwrap())
    }

    #[test]
    fn zero_is_zero() {
        let p = Poly::<Fr, GrevLexTerm>::zero();
        assert!(p.is_zero());
        assert_eq!(p.len(), 0);
        assert!(p.leading().is_none());
    }

    #[test]
    fn from_terms_sorts_and_dedups() {
        let r = mk_ring(3);
        // y^2 has higher total degree than x, so it becomes leading
        // under degrevlex.
        let terms = vec![
            (Fr::from(3u64), mono(&r, &[1, 0, 0])),
            (Fr::from(5u64), mono(&r, &[0, 2, 0])),
            (Fr::from(7u64), mono(&r, &[1, 0, 0])), // duplicate: merges -> 3+7 = 10
            (Fr::zero(), mono(&r, &[0, 0, 1])),     // zero coeff: dropped
        ];
        let p = Poly::from_terms(&r, terms);
        p.assert_canonical(&r);
        assert_eq!(p.len(), 2);
        let (c0, m0) = p.leading().unwrap();
        assert_eq!(c0, Fr::from(5u64));
        assert_eq!(*m0, mono(&r, &[0, 2, 0]));
        // The non-leading term has the combined coefficient 10.
        assert_eq!(p.live_coeffs()[1], Fr::from(10u64));
        assert_eq!(p.live_terms()[1], mono(&r, &[1, 0, 0]));
    }

    #[test]
    fn add_and_sub_cancel() {
        let r = mk_ring(3);
        let f = Poly::from_terms(
            &r,
            vec![
                (Fr::from(3u64), mono(&r, &[1, 0, 0])),
                (Fr::from(5u64), mono(&r, &[0, 2, 0])),
                (Fr::from(1u64), mono(&r, &[0, 0, 1])),
            ],
        );
        let g = f.sub(&f, &r);
        g.assert_canonical(&r);
        assert!(g.is_zero());
    }

    #[test]
    fn sub_mul_term_matches_slow_path() {
        let r = mk_ring(3);
        let p = Poly::from_terms(
            &r,
            vec![
                (Fr::from(3u64), mono(&r, &[2, 1, 0])),
                (Fr::from(7u64), mono(&r, &[1, 0, 1])),
                (Fr::from(1u64), mono(&r, &[0, 0, 2])),
            ],
        );
        let q = Poly::from_terms(
            &r,
            vec![
                (Fr::from(4u64), mono(&r, &[1, 1, 0])),
                (Fr::from(5u64), mono(&r, &[0, 0, 1])),
            ],
        );
        let m = mono(&r, &[1, 0, 0]);
        let c = Fr::from(2u64);

        // Slow path.
        let mq = q.shift(&m, &r).scale(c, &r);
        let slow = p.sub(&mq, &r);
        let fast = p.sub_mul_term(c, &m, &q, &r);
        slow.assert_canonical(&r);
        fast.assert_canonical(&r);
        assert_eq!(slow, fast);
    }

    #[test]
    fn monic_is_idempotent() {
        let r = mk_ring(2);
        let p = Poly::from_terms(
            &r,
            vec![
                (Fr::from(17u64), mono(&r, &[3, 0])),
                (Fr::from(2u64), mono(&r, &[1, 1])),
                (Fr::from(9u64), mono(&r, &[0, 2])),
            ],
        );
        let once = p.monic(&r).unwrap();
        let twice = once.monic(&r).unwrap();
        assert_eq!(once, twice);
        assert_eq!(once.lm_coeff(), Fr::one());
    }

    #[test]
    fn leading_invariants() {
        let r = mk_ring(2);
        let p = Poly::from_terms(
            &r,
            vec![
                (Fr::from(3u64), mono(&r, &[2, 0])),
                (Fr::from(4u64), mono(&r, &[1, 1])),
            ],
        );
        let (c, m) = p.leading().unwrap();
        assert_eq!(c, Fr::from(3u64));
        assert_eq!(m.0.total_deg(), 2);
        assert_eq!(p.lm_sev(), m.0.sev());
        assert_eq!(p.lm_coeff(), Fr::from(3u64));
        assert_eq!(p.lm_deg(), 2);
    }

    #[test]
    fn drop_leading_basic() {
        let r = mk_ring(3);
        let p = Poly::from_terms(
            &r,
            vec![
                (Fr::from(3u64), mono(&r, &[2, 1, 0])),
                (Fr::from(7u64), mono(&r, &[1, 0, 1])),
                (Fr::from(1u64), mono(&r, &[0, 0, 2])),
            ],
        );
        let tail = p.drop_leading();
        tail.assert_canonical(&r);
        assert_eq!(tail.len(), 2);
        // New leading is the old second term.
        let (c, m) = tail.leading().unwrap();
        assert_eq!(c, Fr::from(7u64));
        assert_eq!(m, &mono(&r, &[1, 0, 1]));
        // Cache fields agree.
        assert_eq!(tail.lm_coeff(), Fr::from(7u64));
        assert_eq!(tail.lm_sev(), m.0.sev());
        assert_eq!(tail.lm_deg(), m.0.total_deg());
    }

    #[test]
    fn drop_leading_edge_cases() {
        let r = mk_ring(2);
        // Zero in, zero out.
        let z = Poly::<Fr, GrevLexTerm>::zero();
        let z_tail = z.drop_leading();
        assert!(z_tail.is_zero());
        z_tail.assert_canonical(&r);
        // Single term in, zero out.
        let single = Poly::monomial(&r, Fr::from(3u64), mono(&r, &[1, 0]));
        let single_tail = single.drop_leading();
        assert!(single_tail.is_zero());
        single_tail.assert_canonical(&r);
    }

    #[test]
    fn drop_leading_in_place_walks_head_cursor() {
        // Locks in the head-cursor mechanic: repeated in-place drops
        // must produce the same logical poly as the same number of
        // out-of-place drops, and arithmetic on the partly-dropped
        // poly must agree with arithmetic on the equivalent fresh poly.
        let r = mk_ring(3);
        let original = Poly::from_terms(
            &r,
            vec![
                (Fr::from(5u64), mono(&r, &[3, 0, 0])),
                (Fr::from(4u64), mono(&r, &[2, 1, 0])),
                (Fr::from(3u64), mono(&r, &[1, 0, 1])),
                (Fr::from(2u64), mono(&r, &[0, 0, 2])),
                (Fr::from(1u64), mono(&r, &[0, 1, 0])),
            ],
        );

        let mut peeled = original.clone();
        peeled.drop_leading_in_place();
        peeled.drop_leading_in_place();
        peeled.assert_canonical(&r);
        assert_eq!(peeled.len(), 3);

        let fresh = original.drop_leading().drop_leading();
        fresh.assert_canonical(&r);

        // Logical equality across the head boundary.
        assert_eq!(peeled, fresh);
        assert_eq!(peeled.live_coeffs(), fresh.live_coeffs());
        assert_eq!(peeled.live_terms(), fresh.live_terms());
        assert_eq!(peeled.lm_coeff(), fresh.lm_coeff());
        assert_eq!(peeled.lm_sev(), fresh.lm_sev());
        assert_eq!(peeled.lm_deg(), fresh.lm_deg());

        // Arithmetic across the head boundary: subtracting peeled
        // from itself yields zero, and adding it to fresh doubles it.
        let zero = peeled.sub(&peeled, &r);
        zero.assert_canonical(&r);
        assert!(zero.is_zero());

        let doubled_via_peeled = peeled.add(&fresh, &r);
        let doubled_via_fresh = fresh.add(&fresh, &r);
        assert_eq!(doubled_via_peeled, doubled_via_fresh);

        // Cloning a peeled poly must drop the dead prefix.
        let cloned = peeled.clone();
        cloned.assert_canonical(&r);
        assert_eq!(cloned, peeled);
        assert_eq!(cloned.live_coeffs().len(), cloned.len());

        // Drop the rest one at a time; final state is zero with cache
        // cleared.
        let mut p = peeled;
        for _ in 0..3 {
            p.drop_leading_in_place();
            p.assert_canonical(&r);
        }
        assert!(p.is_zero());
        assert!(p.lm_coeff().is_zero());
        assert_eq!(p.lm_sev(), 0);
        assert_eq!(p.lm_deg(), 0);
        // Extra drop on a zero poly is a no-op.
        p.drop_leading_in_place();
        assert!(p.is_zero());
    }

    #[test]
    fn drop_leading_matches_from_terms_tail() {
        // The optimised drop_leading should match what from_terms
        // would produce for the same tail, just without re-sorting.
        let r = mk_ring(4);
        let p = Poly::from_terms(
            &r,
            vec![
                (Fr::from(5u64), mono(&r, &[3, 0, 0, 0])),
                (Fr::from(2u64), mono(&r, &[2, 1, 0, 0])),
                (Fr::from(9u64), mono(&r, &[1, 0, 1, 0])),
                (Fr::from(4u64), mono(&r, &[0, 0, 0, 2])),
            ],
        );
        let fast = p.drop_leading();
        let slow_tail: Vec<(Fr, GrevLexTerm)> = p.live_coeffs()[1..]
            .iter()
            .zip(p.live_terms()[1..].iter())
            .map(|(&c, m)| (c, *m))
            .collect();
        let slow = Poly::from_terms(&r, slow_tail);
        assert_eq!(fast, slow);
    }
}
