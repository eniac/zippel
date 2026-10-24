//! Sparse multivariate polynomials: a sum of monomials ([`Term`]s) with coefficients. Every
//! constructor canonicalizes, so terms are sorted, merged and non-zero, and structural
//! equality is equality of polynomials. Also: such a polynomial with some of its variables
//! fixed.

use crate::Field;
use lang::typ::CRange;

use super::fixed_index_for_var;

/// A monomial, as `(variable, power)` pairs sorted by variable, each variable once and with a
/// non-zero power; the constant monomial has none.
#[derive(Debug, Clone, Default, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Term(Vec<(usize, usize)>);

impl Term {
    /// The monomial with these powers, in any order; powers of one variable add up.
    pub fn new(mut powers: Vec<(usize, usize)>) -> Self {
        powers.sort_unstable_by_key(|&(var, _)| var);
        let mut merged: Vec<(usize, usize)> = Vec::with_capacity(powers.len());
        for (var, power) in powers {
            match merged.last_mut() {
                Some((last, sum)) if *last == var => *sum += power,
                _ => merged.push((var, power)),
            }
        }
        merged.retain(|&(_, power)| power != 0);
        Self(merged)
    }

    /// The `(variable, power)` pairs, by variable.
    pub fn powers(&self) -> &[(usize, usize)] {
        &self.0
    }

    /// The total degree.
    pub fn degree(&self) -> usize {
        self.0.iter().map(|&(_, power)| power).sum()
    }

    fn evaluate<F: Field>(&self, point: &[F]) -> F {
        self.0
            .iter()
            .map(|&(var, power)| point[var].pow(power as u64))
            .product()
    }
}

/// A sparse multivariate polynomial over `num_vars` variables: `(coefficient, term)` pairs
/// sorted by term, each term once and with a non-zero coefficient.
#[derive(Debug, Clone, Default, Hash, PartialEq, Eq)]
pub struct Multivariate<F> {
    num_vars: usize,
    terms: Vec<(F, Term)>,
}

impl<F: Field> Multivariate<F> {
    /// The polynomial over `num_vars` variables with these terms, in any order; coefficients
    /// of one term add up.
    ///
    /// # Panics
    /// Panics if a term has a variable outside `0..num_vars`.
    pub fn new(num_vars: usize, mut terms: Vec<(F, Term)>) -> Self {
        assert!(
            terms
                .iter()
                .all(|(_, t)| t.0.last().is_none_or(|&(var, _)| var < num_vars)),
            "a term's variable is outside 0..{num_vars}"
        );
        terms.sort_unstable_by(|(_, a), (_, b)| a.cmp(b));
        let mut merged: Vec<(F, Term)> = Vec::with_capacity(terms.len());
        for (c, t) in terms {
            match merged.last_mut() {
                Some((sum, last)) if *last == t => *sum += c,
                _ => merged.push((c, t)),
            }
        }
        merged.retain(|(c, _)| !c.is_zero());
        Self {
            num_vars,
            terms: merged,
        }
    }

    /// The number of variables.
    pub fn num_vars(&self) -> usize {
        self.num_vars
    }

    /// The `(coefficient, term)` pairs, by term.
    pub fn terms(&self) -> &[(F, Term)] {
        &self.terms
    }

    /// Whether this is the zero polynomial.
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// The total degree; 0 for the zero polynomial.
    pub fn degree(&self) -> usize {
        self.terms
            .iter()
            .map(|(_, t)| t.degree())
            .max()
            .unwrap_or(0)
    }

    /// The value at `point`, one coordinate per variable.
    pub fn evaluate(&self, point: &[F]) -> F {
        self.terms.iter().map(|(c, t)| *c * t.evaluate(point)).sum()
    }

    /// The sum, over the larger variable count.
    pub fn add(&self, other: &Self) -> Self {
        Self::new(
            self.num_vars.max(other.num_vars),
            self.terms.iter().chain(&other.terms).cloned().collect(),
        )
    }

    /// The same polynomial with `f` applied to every coefficient; `f` must map zero to zero.
    pub(super) fn map_coeffs(&self, f: impl Fn(F) -> F) -> Self {
        Self::new(
            self.num_vars,
            self.terms.iter().map(|(c, t)| (f(*c), t.clone())).collect(),
        )
    }
}

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
            let mut rest = Vec::with_capacity(term.0.len());
            for &(var, power) in &term.0 {
                match fix(var) {
                    Ok(value) => coefficient *= value.pow(power as u64),
                    Err(var) => rest.push((var, power)),
                }
            }
            (coefficient, Term::new(rest))
        })
        .collect();
    Multivariate::new(num_vars, terms)
}
