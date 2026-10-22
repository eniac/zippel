//! Sparse multivariate polynomials (arkworks' `SparsePolynomial` over `SparseTerm`s) with some
//! of their variables fixed. Each result is built with `from_coefficients_vec`, so its terms
//! are in canonical order, merged, and without zero coefficients.

use ark_ff::Field;
use ark_poly::DenseMVPolynomial;
use ark_poly::multivariate::{SparsePolynomial, SparseTerm, Term};
use lang::typ::CRange;

use super::fixed_index_for_var;

/// A sparse multivariate polynomial.
pub(super) type Multivariate<F> = SparsePolynomial<F, SparseTerm>;

/// `p` with variables `0..point.len()` fixed to `point`, the others renumbered from 0.
pub(super) fn fix_low<F: Field>(p: &Multivariate<F>, point: &[F]) -> Multivariate<F> {
    let k = point.len();
    substitute(p, p.num_vars - k, |var| {
        if var < k {
            Ok(point[var])
        } else {
            Err(var - k)
        }
    })
}

/// `p` with every variable outside `free_range` fixed to the next value of `fixed` (see
/// [`fixed_index_for_var`]), the free ones renumbered from 0 in order.
pub(super) fn restrict<F: Field>(
    p: &Multivariate<F>,
    free_range: &CRange,
    fixed: &[F],
) -> Multivariate<F> {
    substitute(p, free_range.len(), |var| {
        match fixed_index_for_var(free_range, var) {
            Some(i) => Ok(fixed[i]),
            None => Err(var - free_range.start()),
        }
    })
}

/// `p` over `num_vars` variables, each variable either fixed to a value (`Ok`) or renumbered
/// (`Err`) by `fix`: a fixed variable's power goes into its term's coefficient.
fn substitute<F: Field>(
    p: &Multivariate<F>,
    num_vars: usize,
    fix: impl Fn(usize) -> Result<F, usize>,
) -> Multivariate<F> {
    let terms = p
        .terms
        .iter()
        .map(|(coefficient, term)| {
            let mut coefficient = *coefficient;
            let mut rest = Vec::with_capacity(term.len());
            for &(var, power) in term.iter() {
                match fix(var) {
                    Ok(value) => coefficient *= value.pow([power as u64]),
                    Err(var) => rest.push((var, power)),
                }
            }
            (coefficient, SparseTerm::new(rest))
        })
        .collect();
    Multivariate::from_coefficients_vec(num_vars, terms)
}
