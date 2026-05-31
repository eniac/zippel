//! Packed-exponent monomials and the `Monomial<F, W>` trait.
//!
//! Monomials are stored as `[u64; W]`, with `BITS_PER_VAR = 8` bits
//! per variable exponent. The most-significant byte of the last word
//! caches the (saturated) total degree. This caps the number of
//! variables at `W * 8 - 1` (default `W = 4` ⇒ 31 variables).
//!
//! # Const-generic width `W`
//!
//! The `W` parameter defaults to `4`, preserving the original
//! 32-byte / 31-variable layout. Downstream callers that need more
//! variables can instantiate `Ring<F, 8>` (and the M / Poly chain
//! that follows from it) for 63 variables, etc. Hot ops compile down
//! to fixed-size loops over `[u64; W]` and unroll under
//! monomorphisation; at `W = 4` the generated code is byte-for-byte
//! the same as the previous hand-unrolled version.
//!
//! See module-level documentation in earlier commits for the full
//! packing layout.

use crate::field::Field;
use crate::ring::{BITS_PER_VAR, Ring};
use std::cmp::Ordering;
use std::hash::Hash;

const _BITS_PER_VAR_IS_8: () = assert!(BITS_PER_VAR == 8);

/// Const flip mask for degrevlex on width `W`. Every variable byte
/// gets `0x7F`; the cap byte (top byte of the last word) stays `0`.
#[inline]
const fn degrevlex_flip<const W: usize>() -> [u64; W] {
    let mut out = [0u64; W];
    let mut i = 0;
    while i < W {
        out[i] = 0x7F7F_7F7F_7F7F_7F7F;
        i += 1;
    }
    // Mask off the cap byte at the top of the last word.
    out[W - 1] = 0x007F_7F7F_7F7F_7F7F;
    out
}

/// The `Monomial<F, W>` trait: order-aware monomial abstraction.
///
/// Implementors provide an `Ord` impl that pins the monomial order.
/// `W` is the const-generic packing width (default 4, ⇒ 31 vars).
pub trait Monomial<F: Field + Copy + Send + Sync, const W: usize = 4>:
    Sized + Copy + Send + Sync + std::fmt::Debug + PartialEq + Eq + std::hash::Hash + Ord
{
    /// The identity monomial (all exponents zero).
    fn one(ring: &Ring<F, W>) -> Self;
    /// Build a monomial from an exponent slice of length `ring.nvars()`.
    fn from_exponents(ring: &Ring<F, W>, exps: &[u32]) -> Option<Self>;
    /// Exponent of variable `i`. Returns `None` if `i >= ring.nvars()`.
    fn exponent(&self, ring: &Ring<F, W>, i: u32) -> Option<u32>;
    /// Copy the exponent vector into a `Vec<u32>`.
    fn exponents(&self, ring: &Ring<F, W>) -> Vec<u32>;
    /// Total degree.
    fn total_deg(&self, ring: &Ring<F, W>) -> u32;
    /// Multiply two monomials.
    fn mul(&self, other: &Self, ring: &Ring<F, W>) -> Self;
    /// `true` iff `self | other` (each `e_i(self) ≤ e_i(other)`).
    fn divides(&self, other: &Self, ring: &Ring<F, W>) -> bool;
    /// Divide. Precondition `other.divides(self)`; returns `None` otherwise.
    fn div(&self, other: &Self, ring: &Ring<F, W>) -> Option<Self>;
    /// Componentwise maximum (least common multiple of monomials).
    fn lcm(&self, other: &Self, ring: &Ring<F, W>) -> Self;
    /// Access the underlying `MonoTerm`.
    fn as_mono_term(&self) -> &MonoTerm<W>;

    /// Short exponent vector (ring-independent).
    #[inline]
    fn sev(&self) -> u64 {
        self.as_mono_term().sev()
    }

    /// Cached total degree (ring-independent).
    #[inline]
    fn raw_total_deg(&self) -> u32 {
        self.as_mono_term().total_deg()
    }

    /// Heap-comparison key for the Monagan-Pearce reducer.
    ///
    /// Returns `(prefix, key)`; the heap lex-compares `prefix`
    /// first, then `key` MSB-word first. The contract is:
    ///
    /// > `lex_compare(M::cmp_key(a, ring), M::cmp_key(b, ring))`
    /// > `==`
    /// > `M::cmp(M::from(a), M::from(b))`
    ///
    /// for any two `MonoTerm<W>` `a`, `b` over `ring`.
    ///
    /// Default impl: pure DegRevLex via the XOR-flip-mask trick
    /// (matches `GrevLexTerm::cmp`). `prefix = 0`.
    /// Orders that prepend a block (e.g., elimination orders) must
    /// override this method to put the block metric in `prefix`.
    #[inline]
    fn cmp_key(packed: &MonoTerm<W>, ring: &Ring<F, W>) -> (u64, [u64; W]) {
        let mask = ring.cmp_flip_mask();
        let key: [u64; W] = std::array::from_fn(|i| packed.packed()[i] ^ mask[i]);
        (0, key)
    }
}

/// Packed-exponent monomial. See module documentation for layout.
///
/// `MonoTerm` is a pure data carrier — no `Ord` impl. The monomial
/// order is pinned by the newtype wrappers (`GrevLexTerm`,
/// `OddElimTerm`) via their `Ord` impls.
///
/// Const-generic on `W` (number of `u64` words in the packed block,
/// default 4).
#[derive(Clone, Copy, Debug)]
pub struct MonoTerm<const W: usize = 4> {
    /// `W` u64 words; word `W-1` is most significant.
    packed: [u64; W],
    /// Short exponent vector.
    sev: u64,
    /// True total degree, uncapped.
    total_deg: u32,
    /// Component index. Always 0 today.
    component: u16,
    /// Number of variables in the parent ring (cached for ringless comparisons).
    nvars: u16,
}

impl<const W: usize> MonoTerm<W> {
    // ----- Construction -----

    /// Build a monomial from an exponent slice of length `ring.nvars()`.
    pub fn from_exponents<F: Field + Copy + Send + Sync>(
        ring: &Ring<F, W>,
        exps: &[u32],
    ) -> Option<Self> {
        let n = ring.nvars() as usize;
        if exps.len() != n {
            return None;
        }
        for &e in exps {
            if e > crate::ring::MAX_VAR_EXP {
                return None;
            }
        }

        let mut packed = [0u64; W];
        let mut total: u64 = 0;
        let mut sev: u64 = 0;

        for (i, &e) in exps.iter().enumerate() {
            total += e as u64;
            if e > 0 {
                sev |= 1u64 << (i % 64);
            }
            let byte_idx = byte_index_for_var::<W>(n, i);
            let (word, shift) = split_byte_index::<W>(byte_idx);
            packed[word] |= (e as u64) << shift;
        }

        let capped = total.min(u8::MAX as u64);
        packed[W - 1] |= capped << 56;

        if total > u32::MAX as u64 {
            return None;
        }

        Some(Self {
            packed,
            sev,
            total_deg: total as u32,
            component: 0,
            nvars: n as u16,
        })
    }

    /// The identity monomial (all exponents zero).
    pub fn one<F: Field + Copy + Send + Sync>(ring: &Ring<F, W>) -> Self {
        let zeros = vec![0u32; ring.nvars() as usize];
        Self::from_exponents(ring, &zeros).expect("identity monomial fits trivially")
    }

    // ----- Accessors -----

    /// Short exponent vector.
    #[inline]
    pub fn sev(&self) -> u64 {
        self.sev
    }

    /// Total degree (uncapped).
    #[inline]
    pub fn total_deg(&self) -> u32 {
        self.total_deg
    }

    /// Component index. Always 0 in this bootstrap.
    #[inline]
    pub fn component(&self) -> u32 {
        self.component as u32
    }

    /// Borrow the packed exponent block (`W × u64 = W*8` bytes).
    #[inline]
    pub fn packed(&self) -> &[u64; W] {
        &self.packed
    }

    /// Exponent of variable `i`. Returns `None` if `i >= ring.nvars()`.
    pub fn exponent<F: Field + Copy + Send + Sync>(
        &self,
        ring: &Ring<F, W>,
        i: u32,
    ) -> Option<u32> {
        if i >= ring.nvars() {
            return None;
        }
        Some(self.exponent_raw(ring.nvars() as usize, i as usize))
    }

    #[inline]
    fn exponent_raw(&self, nvars: usize, i: usize) -> u32 {
        let byte_idx = byte_index_for_var::<W>(nvars, i);
        let (word, shift) = split_byte_index::<W>(byte_idx);
        ((self.packed[word] >> shift) & 0x7F) as u32
    }

    /// Copy the exponent vector into a `Vec<u32>`.
    pub fn exponents<F: Field + Copy + Send + Sync>(&self, ring: &Ring<F, W>) -> Vec<u32> {
        let n = ring.nvars() as usize;
        (0..n).map(|i| self.exponent_raw(n, i)).collect()
    }

    // ----- Arithmetic -----

    /// Multiply two monomials.
    pub fn mul<F: Field + Copy + Send + Sync>(&self, other: &Self, ring: &Ring<F, W>) -> Self {
        // Element-wise wrapping add of the packed words.
        // At `W = 4`, monomorphisation unrolls this into the same four
        // wrapping_add instructions the hand-rolled code emitted; at
        // larger W it stays a tight fixed-size loop.
        let mut packed: [u64; W] =
            std::array::from_fn(|i| self.packed[i].wrapping_add(other.packed[i]));

        if cfg!(debug_assertions) {
            let m = ring.overflow_mask();
            let mut ovf: u64 = 0;
            for i in 0..W {
                ovf |= packed[i] & m[i];
            }
            debug_assert_eq!(
                ovf, 0,
                "MonoTerm::mul overflow: per-byte exponent > 127 (ADR-018 contract: \
                 caller's ring construction must guarantee no bba-step product overflows)"
            );
            debug_assert!(
                self.total_deg.checked_add(other.total_deg).is_some(),
                "MonoTerm::mul total-degree u32 overflow (ADR-018 contract)"
            );
        }

        let total = self.total_deg.wrapping_add(other.total_deg);
        let capped = (total as u64).min(u8::MAX as u64);
        packed[W - 1] = (packed[W - 1] & !(0xFFu64 << 56)) | (capped << 56);

        let sev = self.sev | other.sev;

        Self {
            packed,
            sev,
            total_deg: total,
            component: 0,
            nvars: self.nvars,
        }
    }

    /// `true` iff `self | other` (each `e_i(self) ≤ e_i(other)`).
    pub fn divides<F: Field + Copy + Send + Sync>(&self, other: &Self, ring: &Ring<F, W>) -> bool {
        let n = ring.nvars() as usize;
        let first_var_byte = (W * 8 - 1) - n;
        let last_var_byte = W * 8 - 2;
        for byte_idx in first_var_byte..=last_var_byte {
            let (word, shift) = split_byte_index::<W>(byte_idx);
            let ea = (self.packed[word] >> shift) & 0x7F;
            let eb = (other.packed[word] >> shift) & 0x7F;
            if ea > eb {
                return false;
            }
        }
        true
    }

    /// Divide. Precondition `other.divides(self)`; returns `None` otherwise.
    pub fn div<F: Field + Copy + Send + Sync>(
        &self,
        other: &Self,
        ring: &Ring<F, W>,
    ) -> Option<Self> {
        let n = ring.nvars() as usize;
        let first_var_byte = (W * 8 - 1) - n;
        let last_var_byte = W * 8 - 2;
        let mut packed = [0u64; W];
        let mut sev: u64 = 0;
        for byte_idx in first_var_byte..=last_var_byte {
            let (word, shift) = split_byte_index::<W>(byte_idx);
            let ea = (self.packed[word] >> shift) & 0x7F;
            let eb = (other.packed[word] >> shift) & 0x7F;
            if eb > ea {
                return None;
            }
            let new_e = ea - eb;
            packed[word] |= new_e << shift;
            if new_e > 0 {
                let var_i = byte_idx + n - (W * 8 - 1);
                sev |= 1u64 << (var_i % 64);
            }
        }
        if other.total_deg > self.total_deg {
            return None;
        }
        let total = self.total_deg - other.total_deg;
        let capped = (total as u64).min(u8::MAX as u64);
        packed[W - 1] |= capped << 56;
        Some(Self {
            packed,
            sev,
            total_deg: total,
            component: 0,
            nvars: self.nvars,
        })
    }

    /// Componentwise maximum (least common multiple of monomials).
    pub fn lcm<F: Field + Copy + Send + Sync>(&self, other: &Self, ring: &Ring<F, W>) -> Self {
        let n = ring.nvars() as usize;
        let mut exps = vec![0u32; n];
        for (i, slot) in exps.iter_mut().enumerate() {
            *slot = self.exponent_raw(n, i).max(other.exponent_raw(n, i));
        }
        Self::from_exponents(ring, &exps).expect("lcm per-var exponents ≤ MAX_VAR_EXP")
    }

    // ----- Ordering helpers (pub(crate)) -----

    /// Degrevlex comparison using the CONST flip mask.
    pub(crate) fn cmp_degrevlex_packed(&self, other: &Self) -> Ordering {
        let flip = degrevlex_flip::<W>();
        let a_cap = (self.packed[W - 1] >> 56) & 0xFF;
        let b_cap = (other.packed[W - 1] >> 56) & 0xFF;
        let saturated = a_cap == u8::MAX as u64 || b_cap == u8::MAX as u64;

        if saturated {
            match self.total_deg.cmp(&other.total_deg) {
                Ordering::Equal => {}
                ord => return ord,
            }
            for i in (0..W - 1).rev() {
                let av = self.packed[i] ^ flip[i];
                let bv = other.packed[i] ^ flip[i];
                match av.cmp(&bv) {
                    Ordering::Equal => {}
                    ord => return ord,
                }
            }
            let lo_mask = (1u64 << 56) - 1;
            let av_top = (self.packed[W - 1] ^ flip[W - 1]) & lo_mask;
            let bv_top = (other.packed[W - 1] ^ flip[W - 1]) & lo_mask;
            return av_top.cmp(&bv_top);
        }

        for i in (0..W).rev() {
            let av = self.packed[i] ^ flip[i];
            let bv = other.packed[i] ^ flip[i];
            match av.cmp(&bv) {
                Ordering::Equal => {}
                ord => return ord,
            }
        }
        Ordering::Equal
    }

    /// Degrevlex comparison using the ring's dynamic flip mask.
    #[allow(dead_code)]
    pub(crate) fn cmp_degrevlex<F: Field + Copy + Send + Sync>(
        &self,
        other: &Self,
        ring: &Ring<F, W>,
    ) -> Ordering {
        let a_cap = (self.packed[W - 1] >> 56) & 0xFF;
        let b_cap = (other.packed[W - 1] >> 56) & 0xFF;
        let saturated = a_cap == u8::MAX as u64 || b_cap == u8::MAX as u64;
        let mask = ring.cmp_flip_mask();

        if saturated {
            match self.total_deg.cmp(&other.total_deg) {
                Ordering::Equal => {}
                ord => return ord,
            }
            for i in (0..W - 1).rev() {
                let av = self.packed[i] ^ mask[i];
                let bv = other.packed[i] ^ mask[i];
                match av.cmp(&bv) {
                    Ordering::Equal => {}
                    ord => return ord,
                }
            }
            let lo_mask = (1u64 << 56) - 1;
            let av_top = (self.packed[W - 1] ^ mask[W - 1]) & lo_mask;
            let bv_top = (other.packed[W - 1] ^ mask[W - 1]) & lo_mask;
            return av_top.cmp(&bv_top);
        }

        for i in (0..W).rev() {
            let av = self.packed[i] ^ mask[i];
            let bv = other.packed[i] ^ mask[i];
            match av.cmp(&bv) {
                Ordering::Equal => {}
                ord => return ord,
            }
        }
        Ordering::Equal
    }

    /// Block elimination comparison with a closure deciding which vars are in the elim block.
    pub(crate) fn cmp_elim_packed(
        &self,
        other: &Self,
        eliminate: impl Fn(usize) -> bool,
    ) -> Ordering {
        let n = self.nvars as usize;
        let mut wa: u32 = 0;
        let mut wb: u32 = 0;
        for i in 0..n {
            if eliminate(i) {
                let byte_idx = byte_index_for_var::<W>(n, i);
                let (word, shift) = split_byte_index::<W>(byte_idx);
                let ea = ((self.packed[word] >> shift) & 0x7F) as u32;
                let eb = ((other.packed[word] >> shift) & 0x7F) as u32;
                wa += ea;
                wb += eb;
            }
        }
        match wa.cmp(&wb) {
            Ordering::Equal => {}
            ord => return ord,
        }
        self.cmp_degrevlex_packed(other)
    }

    // ----- Invariants -----

    /// Panic if any internal invariant is violated.
    pub fn assert_canonical<F: Field + Copy + Send + Sync>(&self, ring: &Ring<F, W>) {
        let n = ring.nvars() as usize;
        let mut total: u64 = 0;
        let mut sev: u64 = 0;

        for i in 0..n {
            let e = self.exponent_raw(n, i);
            assert!(
                e <= crate::ring::MAX_VAR_EXP,
                "exponent {e} at var {i} exceeds 7-bit limit ({})",
                crate::ring::MAX_VAR_EXP
            );
            total += e as u64;
            if e > 0 {
                sev |= 1u64 << (i % 64);
            }
        }

        for word in 0..W {
            assert_eq!(
                self.packed[word] & ring.overflow_mask()[word],
                0,
                "overflow guard bit set in word {word}"
            );
        }

        assert!(total <= u32::MAX as u64, "total degree overflows u32");
        assert_eq!(total as u32, self.total_deg, "total_deg cache mismatch");
        assert_eq!(sev, self.sev, "sev cache mismatch");

        let expected_cap = total.min(u8::MAX as u64);
        let cap = (self.packed[W - 1] >> 56) & 0xFF;
        assert_eq!(cap, expected_cap, "top-byte total-degree cap mismatch");

        let expected = Self::from_exponents(ring, &self.exponents(ring))
            .expect("re-canonicalising from our own exponents must succeed");
        assert_eq!(
            self.packed, expected.packed,
            "packed differs from canonical"
        );

        assert_eq!(self.component, 0, "non-zero component not yet supported");
    }
}

impl<const W: usize> PartialEq for MonoTerm<W> {
    fn eq(&self, other: &Self) -> bool {
        self.packed == other.packed && self.component == other.component
    }
}
impl<const W: usize> Eq for MonoTerm<W> {}

impl<const W: usize> Hash for MonoTerm<W> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.packed.hash(state);
        self.component.hash(state);
    }
}

// ----- Newtypes -----

/// Graded reverse lexicographic order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct GrevLexTerm<const W: usize = 4>(pub(crate) MonoTerm<W>);

/// Elimination order: odd-indexed variables form the elimination block.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct OddElimTerm<const W: usize = 4>(pub(crate) MonoTerm<W>);

impl<const W: usize> From<MonoTerm<W>> for GrevLexTerm<W> {
    fn from(t: MonoTerm<W>) -> Self {
        GrevLexTerm(t)
    }
}
impl<const W: usize> From<MonoTerm<W>> for OddElimTerm<W> {
    fn from(t: MonoTerm<W>) -> Self {
        OddElimTerm(t)
    }
}

impl<const W: usize> Ord for GrevLexTerm<W> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp_degrevlex_packed(&other.0)
    }
}
impl<const W: usize> PartialOrd for GrevLexTerm<W> {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}

impl<const W: usize> Ord for OddElimTerm<W> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp_elim_packed(&other.0, |idx| idx % 2 == 1)
    }
}
impl<const W: usize> PartialOrd for OddElimTerm<W> {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}

// ----- Monomial<F, W> impls -----

impl<F: Field + Copy + Send + Sync, const W: usize> Monomial<F, W> for GrevLexTerm<W> {
    #[inline]
    fn one(ring: &Ring<F, W>) -> Self {
        Self(MonoTerm::one(ring))
    }
    #[inline]
    fn from_exponents(ring: &Ring<F, W>, exps: &[u32]) -> Option<Self> {
        MonoTerm::from_exponents(ring, exps).map(Self)
    }
    #[inline]
    fn exponent(&self, ring: &Ring<F, W>, i: u32) -> Option<u32> {
        self.0.exponent(ring, i)
    }
    #[inline]
    fn exponents(&self, ring: &Ring<F, W>) -> Vec<u32> {
        self.0.exponents(ring)
    }
    #[inline]
    fn total_deg(&self, _ring: &Ring<F, W>) -> u32 {
        self.0.total_deg
    }
    #[inline]
    fn mul(&self, other: &Self, ring: &Ring<F, W>) -> Self {
        Self(self.0.mul(&other.0, ring))
    }
    #[inline]
    fn divides(&self, other: &Self, ring: &Ring<F, W>) -> bool {
        self.0.divides(&other.0, ring)
    }
    #[inline]
    fn div(&self, other: &Self, ring: &Ring<F, W>) -> Option<Self> {
        self.0.div(&other.0, ring).map(Self)
    }
    #[inline]
    fn lcm(&self, other: &Self, ring: &Ring<F, W>) -> Self {
        Self(self.0.lcm(&other.0, ring))
    }
    #[inline]
    fn as_mono_term(&self) -> &MonoTerm<W> {
        &self.0
    }
}

impl<F: Field + Copy + Send + Sync, const W: usize> Monomial<F, W> for OddElimTerm<W> {
    #[inline]
    fn one(ring: &Ring<F, W>) -> Self {
        Self(MonoTerm::one(ring))
    }
    #[inline]
    fn from_exponents(ring: &Ring<F, W>, exps: &[u32]) -> Option<Self> {
        MonoTerm::from_exponents(ring, exps).map(Self)
    }
    #[inline]
    fn exponent(&self, ring: &Ring<F, W>, i: u32) -> Option<u32> {
        self.0.exponent(ring, i)
    }
    #[inline]
    fn exponents(&self, ring: &Ring<F, W>) -> Vec<u32> {
        self.0.exponents(ring)
    }
    #[inline]
    fn total_deg(&self, _ring: &Ring<F, W>) -> u32 {
        self.0.total_deg
    }
    #[inline]
    fn mul(&self, other: &Self, ring: &Ring<F, W>) -> Self {
        Self(self.0.mul(&other.0, ring))
    }
    #[inline]
    fn divides(&self, other: &Self, ring: &Ring<F, W>) -> bool {
        self.0.divides(&other.0, ring)
    }
    #[inline]
    fn div(&self, other: &Self, ring: &Ring<F, W>) -> Option<Self> {
        self.0.div(&other.0, ring).map(Self)
    }
    #[inline]
    fn lcm(&self, other: &Self, ring: &Ring<F, W>) -> Self {
        Self(self.0.lcm(&other.0, ring))
    }
    #[inline]
    fn as_mono_term(&self) -> &MonoTerm<W> {
        &self.0
    }

    /// Heap key for the elimination order: the block-sum (sum of
    /// exponents at odd-indexed variables) is packed into `prefix`,
    /// and the existing DegRevLex flip-masked key forms the tail.
    ///
    /// This matches `OddElimTerm::cmp` (which is
    /// `cmp_elim_packed(|i| i % 2 == 1)`): block-sum first, then
    /// DegRevLex tiebreak.
    ///
    /// Capacity check: each exponent is 7 bits, the block has at
    /// most `nvars / 2 < W*4` variables, so the sum is bounded by
    /// `127 * W*4`. For all `W <= 2^53 / (127*4) ≈ 2^44`, the sum
    /// fits in a `u64` with room to spare.
    #[inline]
    fn cmp_key(packed: &MonoTerm<W>, ring: &Ring<F, W>) -> (u64, [u64; W]) {
        let nvars = ring.nvars() as usize;
        debug_assert!(
            nvars / 2 < W * 4,
            "elim block_sum capacity requires nvars/2 < W*4"
        );
        let mut block_sum: u64 = 0;
        let mut i = 1;
        while i < nvars {
            block_sum += packed.exponent_raw(nvars, i) as u64;
            i += 2;
        }
        let mask = ring.cmp_flip_mask();
        let tail: [u64; W] = std::array::from_fn(|i| packed.packed()[i] ^ mask[i]);
        (block_sum, tail)
    }
}

// ----- packing helpers -----

/// Byte index of variable `i` in the `W*8`-byte packed block.
#[inline]
fn byte_index_for_var<const W: usize>(nvars: usize, i: usize) -> usize {
    debug_assert!(i < nvars);
    debug_assert!(nvars < W * 8);
    i + (W * 8 - 1) - nvars
}

/// Split a byte index in `[0, W*8)` into `(word_idx, bit_shift)`.
#[inline]
fn split_byte_index<const W: usize>(byte_idx: usize) -> (usize, u32) {
    debug_assert!(byte_idx < W * 8);
    let word = byte_idx / 8;
    let shift = ((byte_idx % 8) * 8) as u32;
    (word, shift)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;

    fn mk_ring(nvars: u32) -> Ring<Fr> {
        Ring::<Fr>::new(nvars).unwrap()
    }

    /// Property: lex compare on `(pre_key, cmp_key)` returned by
    /// `M::cmp_key` must agree with `M::cmp` on the underlying
    /// `MonoTerm` values. This is the contract the heap reducer
    /// relies on.
    fn prop_cmp_key_lex_matches_m_cmp<M>(nvars: u32)
    where
        M: Monomial<Fr, 4> + From<MonoTerm<4>>,
    {
        let ring = mk_ring(nvars);
        // Deterministic LCG to generate exponent vectors.
        let mut s: u64 = 0x9E3779B97F4A7C15;
        let mut step = || {
            s = s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            s
        };
        let n = nvars as usize;
        let mut samples: Vec<MonoTerm<4>> = Vec::with_capacity(64);
        while samples.len() < 64 {
            let exps: Vec<u32> = (0..n).map(|_| (step() % 6) as u32).collect();
            if let Some(m) = MonoTerm::from_exponents(&ring, &exps) {
                samples.push(m);
            }
        }

        for a in &samples {
            for b in &samples {
                let m_cmp = M::from(*a).cmp(&M::from(*b));
                let (pa, ka) = M::cmp_key(a, &ring);
                let (pb, kb) = M::cmp_key(b, &ring);
                let lex = pa
                    .cmp(&pb)
                    .then_with(|| ka.iter().rev().cmp(kb.iter().rev()));
                assert_eq!(
                    lex,
                    m_cmp,
                    "cmp_key lex disagrees with M::cmp at a={:?} b={:?}",
                    a.exponents(&ring),
                    b.exponents(&ring),
                );
            }
        }
    }

    #[test]
    fn cmp_key_matches_grevlex() {
        for nvars in [1u32, 2, 5, 10, 31] {
            prop_cmp_key_lex_matches_m_cmp::<GrevLexTerm>(nvars);
        }
    }

    #[test]
    fn cmp_key_matches_oddelim() {
        for nvars in [1u32, 2, 5, 10, 31] {
            prop_cmp_key_lex_matches_m_cmp::<OddElimTerm>(nvars);
        }
    }

    #[test]
    fn round_trip_exponents() {
        let r = mk_ring(5);
        let exps = vec![0u32, 3, 7, 0, 12];
        let m = MonoTerm::from_exponents(&r, &exps).unwrap();
        assert_eq!(m.exponents(&r), exps);
        assert_eq!(m.total_deg(), 22);
        m.assert_canonical(&r);
    }

    #[test]
    fn one_is_canonical() {
        let r = mk_ring(7);
        let one = MonoTerm::one(&r);
        assert_eq!(one.total_deg(), 0);
        assert_eq!(one.sev(), 0);
        one.assert_canonical(&r);
    }

    #[test]
    fn from_exponents_rejects_above_max_var_exp() {
        let r = mk_ring(3);
        assert!(MonoTerm::from_exponents(&r, &[127, 0, 0]).is_some());
        assert!(MonoTerm::from_exponents(&r, &[128, 0, 0]).is_none());
        assert!(MonoTerm::from_exponents(&r, &[0, 200, 0]).is_none());
        assert!(MonoTerm::from_exponents(&r, &[0, 0, 255]).is_none());
    }

    #[test]
    fn mul_within_budget_succeeds() {
        let r = mk_ring(4);
        let a = MonoTerm::from_exponents(&r, &[63, 0, 0, 0]).unwrap();
        let b = MonoTerm::from_exponents(&r, &[64, 0, 0, 0]).unwrap();
        let p = a.mul(&b, &r);
        p.assert_canonical(&r);
        assert_eq!(p.exponent(&r, 0).unwrap(), 127);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "MonoTerm::mul overflow")]
    fn mul_debug_asserts_on_per_byte_overflow() {
        let r = mk_ring(4);
        let a = MonoTerm::from_exponents(&r, &[1, 100, 0, 0]).unwrap();
        let b = MonoTerm::from_exponents(&r, &[1, 50, 0, 0]).unwrap();
        let _ = a.mul(&b, &r);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "MonoTerm::mul overflow")]
    fn mul_debug_asserts_on_exact_guard_bit_trip() {
        let r = mk_ring(4);
        let a = MonoTerm::from_exponents(&r, &[64, 0, 0, 0]).unwrap();
        let b = MonoTerm::from_exponents(&r, &[64, 0, 0, 0]).unwrap();
        let _ = a.mul(&b, &r);
    }

    #[test]
    fn mul_no_carry_propagation_between_neighbouring_bytes() {
        let r = mk_ring(5);
        let a = MonoTerm::from_exponents(&r, &[60, 70, 80, 90, 100]).unwrap();
        let b = MonoTerm::from_exponents(&r, &[60, 50, 40, 30, 20]).unwrap();
        let p = a.mul(&b, &r);
        p.assert_canonical(&r);
        for i in 0..5 {
            assert_eq!(p.exponent(&r, i).unwrap(), 120);
        }
        assert_eq!(p.total_deg(), 600);
    }

    #[test]
    fn sev_matches_nonzero_vars() {
        let r = mk_ring(10);
        let m = MonoTerm::from_exponents(&r, &[0, 2, 0, 0, 5, 0, 0, 1, 0, 0]).unwrap();
        let expected = (1u64 << 1) | (1u64 << 4) | (1u64 << 7);
        assert_eq!(m.sev(), expected);
    }

    #[test]
    fn divides_is_componentwise_le() {
        let r = mk_ring(3);
        let a = MonoTerm::from_exponents(&r, &[1, 2, 3]).unwrap();
        let b = MonoTerm::from_exponents(&r, &[2, 2, 4]).unwrap();
        assert!(a.divides(&b, &r));
        assert!(!b.divides(&a, &r));
    }

    #[test]
    fn div_after_mul_roundtrip() {
        let r = mk_ring(4);
        let a = MonoTerm::from_exponents(&r, &[1, 2, 0, 5]).unwrap();
        let b = MonoTerm::from_exponents(&r, &[3, 0, 4, 1]).unwrap();
        let p = a.mul(&b, &r);
        let back = p.div(&b, &r).unwrap();
        assert_eq!(back, a);
    }

    #[test]
    fn lcm_is_max_componentwise() {
        let r = mk_ring(3);
        let a = MonoTerm::from_exponents(&r, &[1, 5, 3]).unwrap();
        let b = MonoTerm::from_exponents(&r, &[4, 2, 3]).unwrap();
        let l = a.lcm(&b, &r);
        assert_eq!(l.exponents(&r), vec![4, 5, 3]);
    }

    #[test]
    fn degrevlex_cmp_basic() {
        let r = mk_ring(3);
        let x2 = GrevLexTerm::from_exponents(&r, &[2, 0, 0]).unwrap();
        let xy = GrevLexTerm::from_exponents(&r, &[1, 1, 0]).unwrap();
        let y2 = GrevLexTerm::from_exponents(&r, &[0, 2, 0]).unwrap();
        let xz = GrevLexTerm::from_exponents(&r, &[1, 0, 1]).unwrap();
        let yz = GrevLexTerm::from_exponents(&r, &[0, 1, 1]).unwrap();
        let z2 = GrevLexTerm::from_exponents(&r, &[0, 0, 2]).unwrap();
        assert_eq!(x2.cmp(&xy), Ordering::Greater);
        assert_eq!(xy.cmp(&y2), Ordering::Greater);
        assert_eq!(y2.cmp(&xz), Ordering::Greater);
        assert_eq!(xz.cmp(&yz), Ordering::Greater);
        assert_eq!(yz.cmp(&z2), Ordering::Greater);
    }

    #[test]
    fn degrevlex_cmp_by_total_deg() {
        let r = mk_ring(3);
        let a = GrevLexTerm::from_exponents(&r, &[3, 0, 0]).unwrap();
        let b = GrevLexTerm::from_exponents(&r, &[0, 0, 2]).unwrap();
        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn degrevlex_cmp_equal() {
        let r = mk_ring(4);
        let a = GrevLexTerm::from_exponents(&r, &[1, 2, 3, 4]).unwrap();
        let b = GrevLexTerm::from_exponents(&r, &[1, 2, 3, 4]).unwrap();
        assert_eq!(a.cmp(&b), Ordering::Equal);
    }

    #[test]
    fn large_total_deg_cap_still_orders_correctly() {
        let r = mk_ring(3);
        let a = GrevLexTerm::from_exponents(&r, &[127, 50, 127]).unwrap();
        let b = GrevLexTerm::from_exponents(&r, &[50, 127, 127]).unwrap();
        assert_eq!(a.cmp(&b), Ordering::Greater);
    }

    #[test]
    fn degrevlex_tiebreak_on_last_variable() {
        let r = mk_ring(3);
        let xy2 = GrevLexTerm::from_exponents(&r, &[1, 2, 0]).unwrap();
        let y3 = GrevLexTerm::from_exponents(&r, &[0, 3, 0]).unwrap();
        let xyz = GrevLexTerm::from_exponents(&r, &[1, 1, 1]).unwrap();
        let y2z = GrevLexTerm::from_exponents(&r, &[0, 2, 1]).unwrap();
        let xz2 = GrevLexTerm::from_exponents(&r, &[1, 0, 2]).unwrap();
        let yz2 = GrevLexTerm::from_exponents(&r, &[0, 1, 2]).unwrap();
        let z3 = GrevLexTerm::from_exponents(&r, &[0, 0, 3]).unwrap();
        let sequence = [&xy2, &y3, &xyz, &y2z, &xz2, &yz2, &z3];
        for w in sequence.windows(2) {
            assert_eq!(w[0].cmp(w[1]), Ordering::Greater);
        }
    }

    #[test]
    fn cmp_degrevlex_packed_agrees_with_ring_based() {
        let r = mk_ring(3);
        let pairs: Vec<([u32; 3], [u32; 3])> = vec![
            ([0, 0, 0], [1, 0, 0]),
            ([1, 0, 0], [0, 1, 0]),
            ([2, 0, 0], [1, 1, 0]),
            ([1, 1, 0], [0, 2, 0]),
            ([1, 0, 1], [0, 1, 1]),
            ([3, 0, 0], [0, 0, 2]),
            ([127, 50, 127], [50, 127, 127]),
        ];
        for (a_exp, b_exp) in &pairs {
            let a = MonoTerm::from_exponents(&r, a_exp).unwrap();
            let b = MonoTerm::from_exponents(&r, b_exp).unwrap();
            let packed = a.cmp_degrevlex_packed(&b);
            let ring_based = a.cmp_degrevlex(&b, &r);
            assert_eq!(
                packed, ring_based,
                "disagreement for {:?} vs {:?}",
                a_exp, b_exp
            );
        }
    }
}
