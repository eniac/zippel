//! Sparse-matrix data shape and primitive row ops.
//!
//! The [`Matrix`] alias and the [`transpose`] / [`mat_vec_mul`]
//! functions are copied verbatim from
//! [`arkworks-rs/snark`](https://github.com/arkworks-rs/snark)
//! `relations/src/utils/matrix.rs` (commit `6d5f7ae`, dual MIT /
//! Apache-2.0). The [`SparseRow`] newtype and its operations are
//! original ark-gb code.

use ark_ff::Field;

// ---------------------------------------------------------------------
// arkworks-rs/snark verbatim (relations/src/utils/matrix.rs @ 6d5f7ae)
// ---------------------------------------------------------------------

/// A sparse representation of constraint matrices.
///
/// Each row is a `Vec<(value, column_index)>`. Snark does **not**
/// guarantee any particular ordering of the entries within a row;
/// ark-gb's [`SparseRow`] adds that invariant on top.
pub type Matrix<F> = Vec<Vec<(F, usize)>>;

/// Transpose a matrix of field elements.
#[must_use]
pub fn transpose<F: Field>(matrix: &Matrix<F>, num_col: usize) -> Matrix<F> {
    let mut transposed: Matrix<F> = vec![Vec::new(); num_col];
    for (row_index, row) in matrix.iter().enumerate() {
        for &(value, col_index) in row {
            transposed[col_index].push((value, row_index));
        }
    }
    transposed
}

/// Multiply a matrix by a vector.
pub fn mat_vec_mul<F: Field>(matrix: &Matrix<F>, vector: &[F]) -> Vec<F> {
    let mut output: Vec<F> = Vec::new();
    for row in matrix {
        let mut sum: F = F::zero();
        for (value, col) in row {
            sum += vector[*col] * value;
        }
        output.push(sum);
    }
    output
}

// ---------------------------------------------------------------------
// SparseRow<F> — original to ark-gb
// ---------------------------------------------------------------------

/// A sparse row of field elements.
///
/// Invariants (always upheld by the public constructors and by every
/// public op):
///
/// 1. column indices are strictly ascending,
/// 2. no entry has a zero value.
///
/// This makes leading-column lookup `O(1)`, AXPY a linear merge, and
/// equality / hashing meaningful without canonicalisation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SparseRow<F: Field> {
    /// `(value, column)` pairs, strictly ascending in `column`,
    /// no zero values.
    entries: Vec<(F, usize)>,
}

impl<F: Field> Default for SparseRow<F> {
    fn default() -> Self {
        Self::new()
    }
}

impl<F: Field> SparseRow<F> {
    /// The empty row (the zero polynomial in linear-algebra terms).
    #[must_use]
    pub const fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// Build a row from a sequence of `(value, column)` pairs.
    ///
    /// Pairs may appear in any order and may contain duplicate columns;
    /// values at the same column are summed, zero-valued entries are
    /// dropped, and the result is sorted ascending in `column`.
    #[must_use]
    pub fn from_pairs<I: IntoIterator<Item = (F, usize)>>(pairs: I) -> Self {
        let mut v: Vec<(F, usize)> = pairs.into_iter().collect();
        v.sort_by_key(|&(_, c)| c);
        // collapse duplicates left-to-right
        let mut out: Vec<(F, usize)> = Vec::with_capacity(v.len());
        for (val, col) in v {
            if let Some(last) = out.last_mut()
                && last.1 == col
            {
                last.0 += val;
                continue;
            }
            out.push((val, col));
        }
        out.retain(|&(v, _)| !v.is_zero());
        Self { entries: out }
    }

    /// Build a row from a dense slice. Zero entries are skipped.
    #[must_use]
    pub fn from_dense(dense: &[F]) -> Self {
        let entries = dense
            .iter()
            .enumerate()
            .filter_map(|(i, &v)| if v.is_zero() { None } else { Some((v, i)) })
            .collect();
        Self { entries }
    }

    /// Borrow the underlying `(value, column)` pairs (sorted, no zeros).
    #[must_use]
    pub fn as_pairs(&self) -> &[(F, usize)] {
        &self.entries
    }

    /// Consume the row, yielding the underlying pairs (sorted, no zeros).
    #[must_use]
    pub fn into_pairs(self) -> Vec<(F, usize)> {
        self.entries
    }

    /// `true` iff the row has no non-zero entries.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.entries.is_empty()
    }

    /// Number of non-zero entries.
    #[must_use]
    pub fn len_nz(&self) -> usize {
        self.entries.len()
    }

    /// Smallest column with a non-zero entry, if any.
    #[must_use]
    pub fn leading_col(&self) -> Option<usize> {
        self.entries.first().map(|&(_, c)| c)
    }

    /// Largest column with a non-zero entry, if any.
    #[must_use]
    pub fn trailing_col(&self) -> Option<usize> {
        self.entries.last().map(|&(_, c)| c)
    }

    /// Coefficient at `column`, or zero if not present.
    #[must_use]
    pub fn coeff(&self, column: usize) -> F {
        match self.entries.binary_search_by_key(&column, |&(_, c)| c) {
            Ok(i) => self.entries[i].0,
            Err(_) => F::zero(),
        }
    }

    /// Multiply every entry by `c` in place. If `c` is zero the row
    /// becomes empty.
    pub fn scale(&mut self, c: &F) {
        if c.is_zero() {
            self.entries.clear();
            return;
        }
        for (v, _) in &mut self.entries {
            *v *= c;
        }
    }

    /// Return `self - c * other`, preserving the row invariant.
    ///
    /// Implemented as a linear merge over the two sorted column lists.
    /// Cancellations are dropped; the result has no zero entries.
    #[must_use]
    pub fn axpy(&self, c: &F, other: &Self) -> Self {
        if c.is_zero() || other.is_zero() {
            return self.clone();
        }
        let mut out: Vec<(F, usize)> = Vec::with_capacity(self.entries.len() + other.entries.len());
        let (a, b) = (&self.entries, &other.entries);
        let (mut i, mut j) = (0usize, 0usize);
        while i < a.len() && j < b.len() {
            let (va, ca) = a[i];
            let (vb, cb) = b[j];
            match ca.cmp(&cb) {
                core::cmp::Ordering::Less => {
                    out.push((va, ca));
                    i += 1;
                }
                core::cmp::Ordering::Greater => {
                    let mut nv = vb;
                    nv *= c;
                    nv = -nv;
                    out.push((nv, cb));
                    j += 1;
                }
                core::cmp::Ordering::Equal => {
                    let mut nv = vb;
                    nv *= c;
                    let nv = va - nv;
                    if !nv.is_zero() {
                        out.push((nv, ca));
                    }
                    i += 1;
                    j += 1;
                }
            }
        }
        while i < a.len() {
            out.push(a[i]);
            i += 1;
        }
        while j < b.len() {
            let (vb, cb) = b[j];
            let mut nv = vb;
            nv *= c;
            out.push((-nv, cb));
            j += 1;
        }
        Self { entries: out }
    }

    /// In-place version of [`axpy`](Self::axpy): `self ← self - c * other`.
    pub fn axpy_assign(&mut self, c: &F, other: &Self) {
        let merged = self.axpy(c, other);
        *self = merged;
    }
}

impl<F: Field> From<Vec<(F, usize)>> for SparseRow<F> {
    /// Sort, dedup-sum, drop zeros — same as [`SparseRow::from_pairs`].
    fn from(pairs: Vec<(F, usize)>) -> Self {
        Self::from_pairs(pairs)
    }
}

impl<F: Field> From<SparseRow<F>> for Vec<(F, usize)> {
    fn from(row: SparseRow<F>) -> Self {
        row.entries
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;
    use ark_ff::{One, UniformRand, Zero};

    fn fr(x: u64) -> Fr {
        Fr::from(x)
    }

    // -- snark-borrowed helpers ------------------------------------------------

    #[test]
    fn transpose_round_trips() {
        // 2x3 matrix: row 0 = [1, 0, 2], row 1 = [0, 3, 4]
        let m: Matrix<Fr> = vec![vec![(fr(1), 0), (fr(2), 2)], vec![(fr(3), 1), (fr(4), 2)]];
        let t = transpose(&m, 3);
        // t is 3x2: col 0 of m -> row 0 of t etc.
        assert_eq!(t.len(), 3);
        assert_eq!(t[0], vec![(fr(1), 0)]);
        assert_eq!(t[1], vec![(fr(3), 1)]);
        assert_eq!(t[2], vec![(fr(2), 0), (fr(4), 1)]);
        let tt = transpose(&t, 2);
        assert_eq!(tt, m);
    }

    #[test]
    fn mat_vec_identity() {
        // 3x3 identity, vec = [10, 20, 30]
        let m: Matrix<Fr> = vec![vec![(fr(1), 0)], vec![(fr(1), 1)], vec![(fr(1), 2)]];
        let v = vec![fr(10), fr(20), fr(30)];
        assert_eq!(mat_vec_mul(&m, &v), v);
    }

    #[test]
    fn mat_vec_mixed() {
        // Row 0 = [1, 0, 2]; Row 1 = [0, 3, 4]; v = [5, 6, 7]
        // expected = [1*5 + 2*7, 3*6 + 4*7] = [19, 46]
        let m: Matrix<Fr> = vec![vec![(fr(1), 0), (fr(2), 2)], vec![(fr(3), 1), (fr(4), 2)]];
        let out = mat_vec_mul(&m, &[fr(5), fr(6), fr(7)]);
        assert_eq!(out, vec![fr(19), fr(46)]);
    }

    // -- SparseRow constructors / invariants ---------------------------------

    #[test]
    fn from_pairs_sorts_and_dedups() {
        let r = SparseRow::<Fr>::from_pairs(vec![
            (fr(2), 5),
            (fr(3), 1),
            (fr(4), 5), // duplicate column
            (fr(0), 7), // zero
            (fr(1), 0),
        ]);
        assert_eq!(r.as_pairs(), &[(fr(1), 0), (fr(3), 1), (fr(6), 5)]);
        // invariant: strictly ascending columns
        let cols: Vec<_> = r.as_pairs().iter().map(|&(_, c)| c).collect();
        assert!(cols.windows(2).all(|w| w[0] < w[1]));
        // invariant: no zero entries
        assert!(r.as_pairs().iter().all(|&(v, _)| !v.is_zero()));
    }

    #[test]
    fn from_pairs_cancellation_drops_entry() {
        // 3 + (-3) at the same column -> entry removed
        let r = SparseRow::<Fr>::from_pairs(vec![(fr(3), 2), (-fr(3), 2), (fr(7), 4)]);
        assert_eq!(r.as_pairs(), &[(fr(7), 4)]);
    }

    #[test]
    fn from_dense_round_trips() {
        let dense = vec![fr(0), fr(2), fr(0), fr(5)];
        let r = SparseRow::<Fr>::from_dense(&dense);
        assert_eq!(r.as_pairs(), &[(fr(2), 1), (fr(5), 3)]);
        assert_eq!(r.coeff(0), Fr::zero());
        assert_eq!(r.coeff(1), fr(2));
        assert_eq!(r.coeff(3), fr(5));
        assert_eq!(r.coeff(99), Fr::zero());
    }

    #[test]
    fn leading_and_trailing() {
        let r = SparseRow::<Fr>::from_dense(&[fr(0), fr(2), fr(0), fr(5)]);
        assert_eq!(r.leading_col(), Some(1));
        assert_eq!(r.trailing_col(), Some(3));
        let z = SparseRow::<Fr>::new();
        assert!(z.is_zero());
        assert_eq!(z.leading_col(), None);
    }

    // -- scale / axpy ---------------------------------------------------------

    #[test]
    fn scale_by_zero_clears() {
        let mut r = SparseRow::<Fr>::from_dense(&[fr(1), fr(2), fr(3)]);
        r.scale(&Fr::zero());
        assert!(r.is_zero());
    }

    #[test]
    fn scale_by_two() {
        let mut r = SparseRow::<Fr>::from_dense(&[fr(1), fr(0), fr(3)]);
        r.scale(&fr(2));
        assert_eq!(r.as_pairs(), &[(fr(2), 0), (fr(6), 2)]);
    }

    #[test]
    fn axpy_matches_dense() {
        // a = [1, 0, 2, 0]; b = [0, 3, 5, 7]; c = 2
        // a - c*b = [1, -6, -8, -14]
        let a = SparseRow::<Fr>::from_dense(&[fr(1), fr(0), fr(2), fr(0)]);
        let b = SparseRow::<Fr>::from_dense(&[fr(0), fr(3), fr(5), fr(7)]);
        let r = a.axpy(&fr(2), &b);
        assert_eq!(
            r.as_pairs(),
            &[(fr(1), 0), (-fr(6), 1), (-fr(8), 2), (-fr(14), 3)]
        );
    }

    #[test]
    fn axpy_cancellation_drops_entry() {
        // a = [3, 0]; b = [3, 0]; c = 1   →  a - 1*b = [0, 0]
        let a = SparseRow::<Fr>::from_dense(&[fr(3), fr(0)]);
        let b = SparseRow::<Fr>::from_dense(&[fr(3), fr(0)]);
        let r = a.axpy(&Fr::one(), &b);
        assert!(r.is_zero());
    }

    #[test]
    fn axpy_with_zero_scalar_returns_self() {
        let a = SparseRow::<Fr>::from_dense(&[fr(1), fr(2)]);
        let b = SparseRow::<Fr>::from_dense(&[fr(7), fr(8)]);
        let r = a.axpy(&Fr::zero(), &b);
        assert_eq!(r, a);
    }

    // -- proptest: axpy matches a dense reference ----------------------------

    #[test]
    fn axpy_random_matches_dense_reference() {
        use ark_std::rand::SeedableRng;
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(0xA1FACE);
        for _ in 0..256 {
            let n = 8usize;
            let mut da = vec![Fr::zero(); n];
            let mut db = vec![Fr::zero(); n];
            for v in da.iter_mut() {
                if u8::rand(&mut rng) % 3 != 0 {
                    *v = Fr::rand(&mut rng);
                }
            }
            for v in db.iter_mut() {
                if u8::rand(&mut rng) % 3 != 0 {
                    *v = Fr::rand(&mut rng);
                }
            }
            let c = Fr::rand(&mut rng);
            let a = SparseRow::<Fr>::from_dense(&da);
            let b = SparseRow::<Fr>::from_dense(&db);
            let got = a.axpy(&c, &b);
            let want: Vec<Fr> = da.iter().zip(&db).map(|(x, y)| *x - c * y).collect();
            assert_eq!(got, SparseRow::<Fr>::from_dense(&want));
        }
    }

    // -- conversions ----------------------------------------------------------

    #[test]
    fn from_into_vec_pairs() {
        let raw = vec![(fr(2), 5), (fr(3), 1), (fr(4), 5)];
        let r: SparseRow<Fr> = raw.into();
        // dedup-summed
        assert_eq!(r.as_pairs(), &[(fr(3), 1), (fr(6), 5)]);
        let back: Vec<(Fr, usize)> = r.into();
        assert_eq!(back, vec![(fr(3), 1), (fr(6), 5)]);
    }
}
