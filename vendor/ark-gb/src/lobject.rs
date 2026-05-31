//! `LObject` — "polynomial being reduced" transient.
//!
//! Design reference: `~/project/docs/rust-bba-port-plan.md` §5, §7.
//!
//! An [`LObject`] wraps a [`KBucket`](crate::kbucket::KBucket)
//! accumulator plus cached leading-term metadata. The bba driver
//! creates one per S-pair it pulls from the [`LSet`](crate::lset::LSet),
//! runs a series of `minus_m_mult_p` reductions on the bucket, and
//! finalises it into a `Poly` survivor via [`LObject::into_poly`].
//!
//! The cached `lm_sev`, `lm_coeff`, `lm_deg` fields mirror `Poly`'s
//! conventions and are refreshed by [`LObject::refresh`] after each
//! reduction step. The driver's SIMD sev scan reads
//! `lobject.lm_sev` on every tick without touching the bucket; the
//! full `leading()` probe runs only on a sev hit.

use std::sync::Arc;

use crate::field::Field;
use crate::kbucket::KBucket;
use crate::monomial::{MonoTerm, Monomial};
use crate::pair::Pair;
use crate::poly::Poly;
use crate::ring::Ring;

/// A reducer transient.
///
/// `Send` via `KBucket`; `!Sync` for the same reason (the bucket is
/// single-owner). A later parallel driver passes `LObject`s between
/// workers by move.
#[derive(Debug)]
pub struct LObject<F: Field + Copy, M: Monomial<F, W> + From<MonoTerm<W>>, const W: usize = 4> {
    /// The geobucket accumulator.
    bucket: KBucket<F, M, W>,
    /// Cached leading sev. 0 when the LObject is zero.
    lm_sev: u64,
    /// Cached leading coeff. 0 when zero.
    lm_coeff: F,
    /// Cached leading total degree. 0 when zero.
    lm_deg: u32,
    /// Cached is_zero flag (snapshot of the last `refresh`).
    is_zero: bool,
    /// Sugar degree propagated from the originating pair (or input).
    sugar: u32,
}

impl<F: Field + Copy, M: Monomial<F, W> + From<MonoTerm<W>>, const W: usize> LObject<F, M, W> {
    /// Build an `LObject` from an existing `Poly` with sugar seeded
    /// from the poly's leading total degree.
    pub fn from_poly(ring: Arc<Ring<F, W>>, p: Poly<F, M, W>) -> Self {
        let sugar = p.lm_deg();
        Self::from_poly_with_sugar(ring, p, sugar)
    }

    /// Build an `LObject` from an existing `Poly` with an explicit
    /// sugar value.
    pub fn from_poly_with_sugar(ring: Arc<Ring<F, W>>, p: Poly<F, M, W>, sugar: u32) -> Self {
        let mut o = Self {
            bucket: KBucket::from_poly(ring, p),
            lm_sev: 0,
            lm_coeff: F::zero(),
            lm_deg: 0,
            is_zero: false,
            sugar,
        };
        o.refresh();
        o
    }

    /// Build the S-polynomial of `(s_i, s_j)` into a fresh bucket.
    ///
    /// Given leading terms `c_i * lm_i`, `c_j * lm_j` and
    /// `lcm = lcm(lm_i, lm_j)`, with `m_i = lcm / lm_i`, `m_j = lcm / lm_j`,
    /// the S-polynomial is `c_j * m_i * s_i - c_i * m_j * s_j`.
    /// The cached `pair.lcm` is consumed (not recomputed).
    ///
    /// Returns `None` in the pathological case where the S-polynomial
    /// is trivially zero — the leading terms cancel and the tails are
    /// empty (single-term inputs). Otherwise an `LObject` is
    /// returned; the caller is responsible for running divisor
    /// reductions on it.
    pub fn from_spoly(
        ring: Arc<Ring<F, W>>,
        s_i: &Poly<F, M, W>,
        s_j: &Poly<F, M, W>,
        pair: &Pair<W>,
    ) -> Option<Self> {
        debug_assert!(!s_i.is_zero() && !s_j.is_zero());
        let (_, lm_i) = s_i.leading()?;
        let (_, lm_j) = s_j.leading()?;
        let c_i = s_i.lm_coeff();
        let c_j = s_j.lm_coeff();
        let m_i = M::from(pair.lcm.div(lm_i.as_mono_term(), &ring)?);
        let m_j = M::from(pair.lcm.div(lm_j.as_mono_term(), &ring)?);

        // sugar = max(sugar_i + deg(m_i), sugar_j + deg(m_j))
        // For the bootstrap, per-pair sugar is already computed by
        // the caller (Pair.sugar). We use that, since propagating
        // per-poly sugar from outside this function is cleaner.
        let sugar = pair.sugar;

        // Start the bucket with c_j * m_i * s_i (i.e. subtract
        // -c_j * m_i * s_i).
        let neg_c_j = -c_j;
        let mut bucket = KBucket::new(Arc::clone(&ring));
        bucket.minus_m_mult_p(&m_i, neg_c_j, s_i);
        // Then subtract c_i * m_j * s_j.
        bucket.minus_m_mult_p(&m_j, c_i, s_j);

        let mut o = Self {
            bucket,
            lm_sev: 0,
            lm_coeff: F::zero(),
            lm_deg: 0,
            is_zero: false,
            sugar,
        };
        o.refresh();
        if o.is_zero {
            return None;
        }
        Some(o)
    }

    /// Re-probe the bucket's leading term and populate the cache.
    /// Call after every `minus_m_mult_p` on the bucket.
    pub fn refresh(&mut self) {
        match self.bucket.leading() {
            None => {
                self.lm_sev = 0;
                self.lm_coeff = F::zero();
                self.lm_deg = 0;
                self.is_zero = true;
            }
            Some((c, m)) => {
                self.lm_sev = m.sev();
                self.lm_coeff = c;
                self.lm_deg = m.raw_total_deg();
                self.is_zero = false;
            }
        }
    }

    /// Cached leading sev. 0 when zero.
    #[inline]
    pub fn lm_sev(&self) -> u64 {
        self.lm_sev
    }

    /// Cached leading coeff. 0 when zero.
    #[inline]
    pub fn lm_coeff(&self) -> F {
        self.lm_coeff
    }

    /// Cached leading total degree. 0 when zero.
    #[inline]
    pub fn lm_deg(&self) -> u32 {
        self.lm_deg
    }

    /// Whether the LObject's value is zero (as of the last
    /// `refresh`).
    #[inline]
    pub fn is_zero(&self) -> bool {
        self.is_zero
    }

    /// Sugar degree.
    #[inline]
    pub fn sugar(&self) -> u32 {
        self.sugar
    }

    /// Overwrite the cached sugar degree. Used by the bba driver's
    /// reducer loop to propagate
    /// `max(sugar(lobj), sugar(s) + deg(m))` after each reduction by
    /// `s_basis[idx]` with multiplier `m`.
    #[inline]
    pub fn set_sugar(&mut self, sugar: u32) {
        self.sugar = sugar;
    }

    /// Mutable access to the underlying bucket for reduction steps.
    #[inline]
    pub fn bucket_mut(&mut self) -> &mut KBucket<F, M, W> {
        &mut self.bucket
    }

    /// Borrow the underlying ring (via the bucket).
    #[inline]
    pub fn ring(&self) -> &Arc<Ring<F, W>> {
        self.bucket.ring()
    }

    /// Read the bucket's leading term, refreshing the cache. Returns
    /// `None` when the LObject is zero.
    pub fn leading(&mut self) -> Option<(F, &M)> {
        self.bucket.leading()
    }

    /// Extract the current leading term, shrinking the bucket by
    /// that term. Cache is cleared; call `refresh` before reading
    /// cached fields again.
    pub fn extract_leading(&mut self) -> Option<(F, M)> {
        let out = self.bucket.extract_leading();
        // Cache is now stale; mark as such. The driver will refresh.
        self.lm_sev = 0;
        self.lm_coeff = F::zero();
        self.lm_deg = 0;
        self.is_zero = false; // unknown; caller must refresh
        out
    }

    /// Finalise: consume the LObject and return its polynomial value.
    pub fn into_poly(self) -> Poly<F, M, W> {
        self.bucket.into_poly()
    }

    /// Debug-only invariant check.
    pub fn assert_canonical(&self) {
        self.bucket.assert_canonical();
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
    fn from_poly_has_matching_lm() {
        let r = mk_ring(3);
        let p = Poly::from_terms(
            &r,
            vec![
                (Fr::from(3u64), mono(&r, &[2, 1, 0])),
                (Fr::from(7u64), mono(&r, &[1, 0, 1])),
            ],
        );
        let p_sev = p.lm_sev();
        let o = LObject::from_poly(Arc::clone(&r), p);
        assert_eq!(o.lm_sev(), p_sev);
        assert_eq!(o.lm_coeff(), Fr::from(3u64));
        assert!(!o.is_zero());
    }

    #[test]
    fn from_spoly_cancels_leading() {
        // s_i = x*y - 1,  s_j = x*z - 2
        // lcm = x*y*z, m_i = z, m_j = y
        // S = c_j * m_i * s_i - c_i * m_j * s_j = z*(xy-1) - y*(xz-2) = -z + 2y
        let r = mk_ring(3);
        let s_i = Poly::from_terms(
            &r,
            vec![
                (Fr::from(1u64), mono(&r, &[1, 1, 0])),
                (-Fr::one(), mono(&r, &[0, 0, 0])),
            ],
        );
        let s_j = Poly::from_terms(
            &r,
            vec![
                (Fr::from(1u64), mono(&r, &[1, 0, 1])),
                (-Fr::from(2u64), mono(&r, &[0, 0, 0])),
            ],
        );
        let lcm = mono(&r, &[1, 1, 1]);
        let pair = Pair::new(0, 1, lcm.0, 3, 0);
        let mut o = LObject::from_spoly(Arc::clone(&r), &s_i, &s_j, &pair).unwrap();
        // Expected: -z + 2y; leading in degrevlex (total
        // deg 1 tied, larger-index variable smaller exponent wins)
        // is 2y (exponent of z is 0 < 1).
        let got = o.bucket_mut().leading().unwrap();
        assert_eq!(got.0, Fr::from(2u64));
        assert_eq!(*got.1, mono(&r, &[0, 1, 0]));
    }

    #[test]
    fn from_spoly_trivial_zero() {
        // s_i = x,  s_j = x -- same poly.  S = x*x - x*x = 0.
        let r = mk_ring(2);
        let s_i = Poly::<Fr, GrevLexTerm>::monomial(&r, Fr::one(), mono(&r, &[1, 0]));
        let s_j = Poly::<Fr, GrevLexTerm>::monomial(&r, Fr::one(), mono(&r, &[1, 0]));
        let lcm = mono(&r, &[1, 0]);
        let pair = Pair::new(0, 1, lcm.0, 1, 0);
        assert!(LObject::from_spoly(Arc::clone(&r), &s_i, &s_j, &pair).is_none());
    }

    #[test]
    fn into_poly_round_trips() {
        let r = mk_ring(3);
        let p = Poly::from_terms(
            &r,
            vec![
                (Fr::from(3u64), mono(&r, &[2, 1, 0])),
                (Fr::from(7u64), mono(&r, &[1, 0, 1])),
                (Fr::from(1u64), mono(&r, &[0, 0, 2])),
            ],
        );
        let o = LObject::from_poly(Arc::clone(&r), p.clone());
        assert_eq!(o.into_poly(), p);
    }
}
