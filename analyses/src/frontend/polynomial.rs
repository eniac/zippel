//! Order-free sparse polynomial — `HashMap<Monomial, F>`.
//!
//! No `leading_term` is exposed: the frontend never depends on monomial
//! ordering semantics. Ordering is runtime data ([`super::MonoOrder`]) passed
//! to the backend when a Gröbner basis or reduction is needed.

use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::fmt;
use std::iter::Sum;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use crate::Var;
use ark_ff::Field;
use share::{Ctx, Set};

use super::monomial::Monomial;

/// A sparse polynomial: a `HashMap` from monomials to coefficients.
///
/// Iteration order is nondeterministic. `Display` sorts terms structurally
/// before printing (output-only determinism).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Polynomial<F: Field> {
    /// Nonzero terms, keyed by monomial. A missing key means a zero
    /// coefficient; arithmetic prunes entries that cancel, so the empty map
    /// is the canonical representation of the zero polynomial.
    pub terms: HashMap<Monomial, F>,
}

// -----------------------------------------------------------------------
// Arithmetic
// -----------------------------------------------------------------------

/// Add `coeff·term` to `terms`, dropping the entry if it cancels.
///
/// Only the touched entry is checked, so accumulating into a large polynomial
/// costs the size of what is added, not of the accumulator.
fn add_term<F: Field>(terms: &mut HashMap<Monomial, F>, term: Monomial, coeff: F) {
    match terms.entry(term) {
        Entry::Occupied(mut entry) => {
            *entry.get_mut() += coeff;
            if entry.get().is_zero() {
                entry.remove();
            }
        }
        Entry::Vacant(entry) => {
            if !coeff.is_zero() {
                entry.insert(coeff);
            }
        }
    }
}

impl<F: Field> AddAssign for Polynomial<F> {
    fn add_assign(&mut self, other: Self) {
        for (term, coeff) in other.terms {
            add_term(&mut self.terms, term, coeff);
        }
    }
}

impl<F: Field> SubAssign for Polynomial<F> {
    fn sub_assign(&mut self, other: Self) {
        for (term, coeff) in other.terms {
            add_term(&mut self.terms, term, -coeff);
        }
    }
}

impl<F: Field> Neg for Polynomial<F> {
    type Output = Self;
    fn neg(mut self) -> Self {
        for coeff in self.terms.values_mut() {
            *coeff = (*coeff).neg();
        }
        self
    }
}

impl<F: Field> MulAssign for Polynomial<F> {
    fn mul_assign(&mut self, other: Self) {
        *self = self.product(&other);
    }
}

impl<F: Field> Add for Polynomial<F> {
    type Output = Self;
    fn add(mut self, other: Self) -> Self {
        self += other;
        self
    }
}

impl<F: Field> Add for &Polynomial<F> {
    type Output = Polynomial<F>;
    fn add(self, other: Self) -> Polynomial<F> {
        let mut result = self.clone();
        for (term, coeff) in &other.terms {
            add_term(&mut result.terms, term.clone(), *coeff);
        }
        result
    }
}

impl<F: Field> Sub for Polynomial<F> {
    type Output = Self;
    fn sub(mut self, other: Self) -> Self {
        self -= other;
        self
    }
}

impl<F: Field> Sub for &Polynomial<F> {
    type Output = Polynomial<F>;
    fn sub(self, other: Self) -> Polynomial<F> {
        let mut result = self.clone();
        for (term, coeff) in &other.terms {
            add_term(&mut result.terms, term.clone(), -*coeff);
        }
        result
    }
}

impl<F: Field> Mul for Polynomial<F> {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        self.product(&other)
    }
}

impl<F: Field> Mul for &Polynomial<F> {
    type Output = Polynomial<F>;
    fn mul(self, other: Self) -> Polynomial<F> {
        self.product(other)
    }
}

impl<F: Field> Sum for Polynomial<F> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        let mut s = Polynomial::zero();
        for x in iter {
            s += x;
        }
        s
    }
}

impl<F: Field> From<Vec<(&Monomial, F)>> for Polynomial<F> {
    fn from(terms: Vec<(&Monomial, F)>) -> Self {
        let mut poly = Polynomial::zero();
        for (term, coeff) in terms {
            *poly.terms.entry(term.clone()).or_insert(F::zero()) += coeff;
        }
        poly.terms.retain(|_, c| !c.is_zero());
        poly
    }
}

// -----------------------------------------------------------------------
// Display — sorts terms structurally for deterministic output
// -----------------------------------------------------------------------

impl<F: Field> fmt::Display for Polynomial<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            return write!(f, "0");
        }
        let mut sorted: Vec<(&Monomial, &F)> = self.terms.iter().collect();
        sorted.sort_by(|a, b| b.0.cmp(a.0));
        let mut parts: Vec<String> = Vec::new();
        let mut first = true;
        for (term, coeff) in sorted {
            if coeff.is_one() && first {
                parts.push(format!("{}", term));
                first = false;
            } else if coeff.is_one() {
                parts.push(format!("+ {}", term));
            } else if coeff.is_zero() {
                continue;
            } else if (*coeff).neg().is_one() {
                parts.push(format!("- {}", term));
                first = false;
            } else if first {
                parts.push(format!("{}*{}", coeff, term));
                first = false;
            } else {
                parts.push(format!("+ {}*{}", coeff, term));
            }
        }
        write!(f, "{}", parts.join(" "))
    }
}

// -----------------------------------------------------------------------
// Inherent methods (order-free subset of the old SparsePolynomial surface)
// -----------------------------------------------------------------------

impl<F: Field> Polynomial<F> {
    /// The zero polynomial (no terms).
    pub fn zero() -> Self {
        Polynomial {
            terms: HashMap::new(),
        }
    }

    /// Whether this is the zero polynomial, i.e. it has no surviving terms.
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// The constant polynomial `f`, stored as `f` times the empty monomial.
    pub fn lit(f: &F) -> Self {
        if f.is_zero() {
            return Self::zero();
        }
        let mut terms = HashMap::new();
        terms.insert(Monomial::default(), *f);
        Polynomial { terms }
    }

    /// The polynomial `v`, i.e. the degree-one monomial in `v` with
    /// coefficient one.
    pub fn var(v: &Var) -> Self {
        let mut terms = HashMap::new();
        terms.insert(Monomial::from(vec![(v.clone(), 1)]), F::one());
        Polynomial { terms }
    }

    /// Total degree: the largest degree over all terms, or `0` when zero or
    /// constant.
    pub fn degree(&self) -> usize {
        self.terms.keys().map(|t| t.degree()).max().unwrap_or(0)
    }

    /// Whether every term is the empty monomial, so the polynomial denotes a
    /// field constant.
    pub fn is_constant(&self) -> bool {
        self.degree() == 0
    }

    /// Extract the constant coefficient (the coefficient of the monomial `1`).
    /// Returns `F::zero()` if the polynomial has no constant term.
    pub fn constant_coeff(&self) -> F {
        self.terms
            .get(&Monomial::default())
            .copied()
            .unwrap_or(F::zero())
    }

    /// Whether `v` occurs with a nonzero exponent in some term.
    pub fn contains(&self, v: &Var) -> bool {
        self.vars().contains(v)
    }

    /// The set of variables occurring anywhere in this polynomial; the
    /// support used when building an ideal's variable set.
    pub fn vars(&self) -> Set<Var> {
        self.terms.keys().flat_map(|t| t.vars()).collect()
    }

    /// The product `self · other`, without consuming or copying either
    /// operand. A one-term factor, the common case when substituting a
    /// definition into a monomial, shifts and scales the other factor term
    /// by term instead of going through the general double loop.
    pub fn product(&self, other: &Self) -> Self {
        let (small, large) = if self.terms.len() <= other.terms.len() {
            (self, other)
        } else {
            (other, self)
        };
        if let (1, Some((monomial, coeff))) = (small.terms.len(), small.terms.iter().next()) {
            let terms = large
                .terms
                .iter()
                .map(|(term, c)| (term.clone() * monomial.clone(), *c * *coeff))
                .filter(|(_, c)| !c.is_zero())
                .collect();
            return Polynomial { terms };
        }
        let mut terms: HashMap<Monomial, F> = HashMap::new();
        for (term1, coeff1) in &small.terms {
            for (term2, coeff2) in &large.terms {
                *terms
                    .entry(term1.clone() * term2.clone())
                    .or_insert(F::zero()) += *coeff1 * *coeff2;
            }
        }
        terms.retain(|_, c| !c.is_zero());
        Polynomial { terms }
    }

    /// Square in place (`self *= self`).
    pub fn square(&mut self) {
        *self = self.product(self);
    }

    /// Raise to the power `exp` in place, by repeated squaring on the trailing
    /// factors of two followed by repeated multiplication.
    ///
    /// `exp == 0` replaces `self` with the constant one, including for the
    /// zero polynomial.
    pub fn pow(&mut self, exp: usize) {
        if exp == 0 {
            *self = Polynomial::lit(&F::one());
            return;
        }
        let mut i = exp;
        while i.is_multiple_of(2) {
            self.square();
            i /= 2;
        }
        if i <= 1 {
            return;
        }
        let mul = self.clone();
        i -= 1;
        while i > 0 {
            *self = self.product(&mul);
            i -= 1;
        }
    }

    /// Substitute every variable through `f` and expand the result.
    ///
    /// Each term's variables are replaced by `f(var)` raised to that
    /// variable's exponent, and the products are summed, so the result is a
    /// fully expanded polynomial rather than a formal composition.
    pub fn flat_map_vars<FF: Fn(Var) -> Self>(self, f: &FF) -> Self {
        let mut new_poly = Polynomial::zero();
        for (term, coeff) in self.terms.into_iter() {
            let mut new_mono = Polynomial::lit(&coeff);
            for (var, power) in term.vars().into_iter().zip(term.powers()) {
                let mut p = f(var);
                p.pow(power);
                new_mono *= p;
            }
            new_poly += new_mono;
        }
        new_poly
    }

    /// Inline variables from `substitutions` into this polynomial.
    /// Returns `(result, did_change)`.
    ///
    /// A term without a substituted variable is carried over as is. In the
    /// others, the variables that stay form one monomial, which is then
    /// multiplied by each substitution raised to its exponent.
    pub fn inline_vars(self, substitutions: &Ctx<Var, Polynomial<F>>) -> (Self, bool) {
        let mut new_poly = Polynomial::zero();
        let mut did_change = false;
        for (term, coeff) in self.terms {
            if !term.iter().any(|(var, _)| substitutions.get(var).is_some()) {
                add_term(&mut new_poly.terms, term, coeff);
                continue;
            }
            did_change = true;
            let mut kept = Vec::new();
            let mut factors = Vec::new();
            for (var, &power) in term.iter() {
                match substitutions.get(var) {
                    Some(sub) => factors.push((sub, power)),
                    None => kept.push((var.clone(), power)),
                }
            }
            let mut new_mono = Polynomial {
                terms: HashMap::from([(Monomial::from(kept), coeff)]),
            };
            for (sub, power) in factors {
                if power == 1 {
                    new_mono = new_mono.product(sub);
                } else {
                    let mut factor = sub.clone();
                    factor.pow(power);
                    new_mono = new_mono.product(&factor);
                }
            }
            new_poly += new_mono;
        }
        (new_poly, did_change)
    }

    /// Remap every variable in every term through `f`.
    pub fn remap_vars(&self, f: &dyn Fn(&Var) -> Var) -> Self {
        let mut new_poly = Polynomial::zero();
        for (term, coeff) in &self.terms {
            let pairs: Vec<(Var, usize)> = term
                .vars()
                .iter()
                .zip(term.powers().iter())
                .map(|(v, &p)| (f(v), p))
                .collect();
            let new_term = Monomial::from(pairs);
            *new_poly.terms.entry(new_term).or_insert(F::zero()) += *coeff;
        }
        new_poly.terms.retain(|_, c| !c.is_zero());
        new_poly
    }
}

#[cfg(test)]
mod tests {
    use super::{Monomial, Polynomial};
    use crate::Var;
    use ark_bls12_381::Fr;
    use backend::ATyp;
    use lang::typ::Qualifier;
    use petgraph::graph::NodeIndex;
    use share::Ctx;

    fn var(i: usize) -> Var {
        Var::from_node(NodeIndex::new(i), ATyp::scalar(), Qualifier::Witness)
    }

    fn x(i: usize) -> Polynomial<Fr> {
        Polynomial::var(&var(i))
    }

    fn lit(n: u64) -> Polynomial<Fr> {
        Polynomial::lit(&Fr::from(n))
    }

    /// `Σ c·Π x_i^e` from `(c, [(i, e), …])`, built without arithmetic.
    fn poly(terms: &[(u64, &[(usize, usize)])]) -> Polynomial<Fr> {
        let monomials: Vec<(Monomial, Fr)> = terms
            .iter()
            .map(|(c, powers)| {
                let powers: Vec<(Var, usize)> = powers.iter().map(|&(i, e)| (var(i), e)).collect();
                (Monomial::from(powers), Fr::from(*c))
            })
            .collect();
        Polynomial::from(monomials.iter().map(|(m, c)| (m, *c)).collect::<Vec<_>>())
    }

    #[test]
    fn cancelled_terms_leave_no_entries() {
        let p = &(x(0) + x(1)) - &x(1);
        assert_eq!(p, x(0));

        let mut q = x(0) * x(1);
        q -= x(1) * x(0);
        assert!(q.is_zero());

        let mut r = x(2);
        r += -x(2);
        assert!(r.is_zero());
    }

    #[test]
    fn cancellation_after_a_literal_zero_is_canonical() {
        let zero = lit(0);
        assert!(zero.is_zero());
        assert_eq!(zero, Polynomial::zero());

        let p = &(&zero + &x(0)) - &x(0);
        assert!(p.is_zero(), "zero coefficient survived: {p:?}");
        assert_eq!(p, Polynomial::zero());

        let p = (zero.clone() + x(0)) - x(0);
        assert_eq!(p, Polynomial::zero());

        let p = (zero - x(0)) + x(0);
        assert_eq!(p, Polynomial::zero());
    }

    #[test]
    fn products_by_one_term_and_by_several_agree() {
        let a = x(0) + x(1) + lit(2);
        let b = lit(3) * x(0);
        let expected = poly(&[(3, &[(0, 2)]), (3, &[(0, 1), (1, 1)]), (6, &[(0, 1)])]);
        assert_eq!(&a * &b, expected);
        assert_eq!(&b * &a, expected);

        let minus_one = -lit(1);
        let difference = x(0) + &x(1) * &minus_one;
        let squares = poly(&[(1, &[(0, 2)])]) - poly(&[(1, &[(1, 2)])]);
        assert_eq!(&(x(0) + x(1)) * &difference, squares);

        assert!((&a * &Polynomial::zero()).is_zero());
    }

    #[test]
    fn inline_vars_substitutes_only_defined_variables() {
        let mut defs = Ctx::new();
        defs.insert(&var(1), &(x(2) + lit(1)));

        // x0·x1² + x0 with x1 := x2 + 1 is x0·x2² + 2·x0·x2 + 2·x0.
        let p = poly(&[(1, &[(0, 1), (1, 2)]), (1, &[(0, 1)])]);
        let (q, changed) = p.inline_vars(&defs);
        assert!(changed);
        let expected = poly(&[
            (1, &[(0, 1), (2, 2)]),
            (2, &[(0, 1), (2, 1)]),
            (2, &[(0, 1)]),
        ]);
        assert_eq!(q, expected);

        let (same, changed) = x(0).inline_vars(&defs);
        assert!(!changed);
        assert_eq!(same, x(0));
    }

    #[test]
    fn inline_vars_preserves_large_exponents() {
        let mut defs = Ctx::new();
        defs.insert(&var(0), &poly(&[(1, &[(1, 2)])]));
        let p = poly(&[(1, &[(0, 65_536)])]);
        let (q, changed) = p.inline_vars(&defs);
        assert!(changed);
        assert_eq!(q, poly(&[(1, &[(1, 131_072)])]));
    }

    #[test]
    fn variables_on_the_same_slot_stay_distinct() {
        // `Var` hashes only its slot, so these collide; `Eq` still tells
        // them apart.
        let mut other = var(0);
        other.name = "other".to_string();
        let p = x(0) + Polynomial::var(&other);
        assert_eq!(p.terms.len(), 2);
    }
}
