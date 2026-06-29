//! `GroebnerBasis<F, T>` plus production polynomial-reduction helpers.
//!
//! The public Buchberger entry points (`buchberger`, `reduce_groebner_basis`,
//! `buchberger_and_reduce`) dispatch through [`Monomial::compute_reduced_gb`],
//! which both `GrevLexTerm` and `ElimTerm` override to route into the external
//! `ark-gb` crate (~10000× speedup on Katsura/Cyclic-n; see
//! `analyses::groebner::ark_gb_adapter`). The original in-tree Buchberger lives
//! under `tests::analyses::groebner::legacy` and is compiled only in test
//! builds for regression and speedup comparisons.

use ark_ff::Field;
use std::fmt;
use std::ops::Index;

use crate::backend::ark_gb::SparsePolynomial;
use crate::backend::ark_gb::monomial::Monomial;

/// A struct representing a Gröbner basis.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct GroebnerBasis<F: Field, T: Monomial> {
    pub basis: Vec<SparsePolynomial<F, T>>,
    pub num_vars: usize,
}

impl<F: Field, T: Monomial> Index<usize> for GroebnerBasis<F, T> {
    type Output = SparsePolynomial<F, T>;

    fn index(&self, index: usize) -> &Self::Output {
        &self.basis[index]
    }
}

impl<F: Field, T: Monomial> IntoIterator for GroebnerBasis<F, T> {
    type Item = SparsePolynomial<F, T>;
    type IntoIter = std::vec::IntoIter<SparsePolynomial<F, T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.basis.into_iter()
    }
}

impl<F: Field, T: Monomial> GroebnerBasis<F, T> {
    pub fn new(num_vars: usize, basis: Vec<SparsePolynomial<F, T>>) -> Self {
        Self { basis, num_vars }
    }

    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.basis.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &SparsePolynomial<F, T>> {
        self.basis.iter()
    }

    /// Reduces polynomial `p` with respect to the basis `G`.
    /// Returns the remainder `r` such that `p = sum(q_i * g_i) + r`, and no term in `r`
    /// is divisible by the leading term of any `g_i` in `G`.
    /// Assumes `G` does not contain the zero polynomial.
    pub fn reduce(&self, mut p: SparsePolynomial<F, T>) -> SparsePolynomial<F, T> {
        let mut remainder = SparsePolynomial::zero();

        // The basis against which we reduce. Filter out zeros once.
        let reducers: Vec<_> = self.basis.iter().filter(|poly| !poly.is_zero()).collect();

        // While p is not zero
        while let Some((p_lc, p_lt)) = p.leading_term() {
            let found_divisor = reducers.iter().find(|g| {
                if let Some((_g_lc, g_lt)) = g.leading_term() {
                    p_lt.is_divided(&g_lt)
                } else {
                    false
                }
            });

            if let Some(g) = found_divisor {
                let (g_lc, g_lt) = g.leading_term().unwrap();
                let multiplier_term =
                    (p_lt / g_lt).expect("Division should succeed if is_divided is true");
                let multiplier_scalar = p_lc
                    * g_lc
                        .inverse()
                        .expect("Leading coefficient must be invertible");
                let to_subtract = g.mul_by_term_and_scalar(multiplier_scalar, &multiplier_term);
                p -= to_subtract;
            } else {
                // No division occurred, move LT(p) to the remainder.
                let (lt, lc) = p.terms.pop_first().unwrap(); // BTreeMap specific method
                remainder.terms.insert(&lt, &lc); // Add to remainder
            }
        }

        remainder
    }

    /// Compute the reduced Gröbner basis.
    ///
    /// Dispatches via [`Monomial::compute_reduced_gb`].
    ///
    /// W is the packed monomial width (8 or 16). Caller must ensure W is
    /// appropriate for the problem size.
    #[allow(dead_code)]
    pub fn buchberger_and_reduce<const W: usize>(self) -> Self {
        let reduced = T::compute_reduced_gb::<_, W>(self.num_vars, self.basis);
        Self::new(self.num_vars, reduced)
    }
}

impl<F: Field, T: Monomial> fmt::Display for GroebnerBasis<F, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for p in self.iter() {
            writeln!(f, "\t{} == 0", p)?;
        }
        Ok(())
    }
}
