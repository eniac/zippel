//! Order-free sparse polynomial — `HashMap<Monomial, F>`.
//!
//! No `leading_term` is exposed: the frontend never depends on monomial
//! ordering semantics. Ordering is runtime data ([`super::MonoOrder`]) passed
//! to the backend when a Gröbner basis or reduction is needed.

use std::collections::HashMap;
use std::fmt;
use std::iter::Sum;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use crate::Var;
use ark_ff::Field;
use share::{Ctx, DocAllocator, DocBuilder, Pretty, Set};

use super::monomial::Monomial;

/// A sparse polynomial: a `HashMap` from monomials to coefficients.
///
/// Iteration order is nondeterministic. `Display` sorts terms structurally
/// before printing (output-only determinism).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Polynomial<F: Field> {
    pub terms: HashMap<Monomial, F>,
}

// -----------------------------------------------------------------------
// Arithmetic
// -----------------------------------------------------------------------

impl<F: Field> AddAssign for Polynomial<F> {
    fn add_assign(&mut self, other: Self) {
        for (term, coef) in other.terms {
            *self.terms.entry(term).or_insert(F::zero()) += coef;
        }
        self.terms.retain(|_, c| !c.is_zero());
    }
}

impl<F: Field> SubAssign for Polynomial<F> {
    fn sub_assign(&mut self, other: Self) {
        for (term, coef) in other.terms {
            *self.terms.entry(term).or_insert(F::zero()) -= coef;
        }
        self.terms.retain(|_, c| !c.is_zero());
    }
}

impl<F: Field> Neg for Polynomial<F> {
    type Output = Self;
    fn neg(self) -> Self {
        let mut result = self.clone();
        for coeff in result.terms.values_mut() {
            *coeff = (*coeff).neg();
        }
        result
    }
}

impl<F: Field> MulAssign for Polynomial<F> {
    fn mul_assign(&mut self, other: Self) {
        let mut new_terms: HashMap<Monomial, F> = HashMap::new();
        for (term1, coeff1) in &self.terms {
            for (term2, coeff2) in &other.terms {
                let new_term = term1.clone() * term2.clone();
                let new_coeff = *coeff1 * *coeff2;
                *new_terms.entry(new_term).or_insert(F::zero()) += new_coeff;
            }
        }
        self.terms = new_terms;
        self.terms.retain(|_, c| !c.is_zero());
    }
}

impl<F: Field> Add for Polynomial<F> {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        let mut result = self.clone();
        result += other;
        result
    }
}

impl<F: Field> Add for &Polynomial<F> {
    type Output = Polynomial<F>;
    fn add(self, other: Self) -> Polynomial<F> {
        let mut result = self.clone();
        result += other.clone();
        result
    }
}

impl<F: Field> Sub for Polynomial<F> {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        let mut result = self.clone();
        result -= other;
        result
    }
}

impl<F: Field> Sub for &Polynomial<F> {
    type Output = Polynomial<F>;
    fn sub(self, other: Self) -> Polynomial<F> {
        let mut result = self.clone();
        result -= other.clone();
        result
    }
}

impl<F: Field> Mul for Polynomial<F> {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        let mut result = self.clone();
        result *= other;
        result
    }
}

impl<F: Field> Mul for &Polynomial<F> {
    type Output = Polynomial<F>;
    fn mul(self, other: Self) -> Polynomial<F> {
        self.clone() * other.clone()
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
    pub fn zero() -> Self {
        Polynomial {
            terms: HashMap::new(),
        }
    }

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    pub fn lit(f: &F) -> Self {
        let mut terms = HashMap::new();
        terms.insert(Monomial::default(), *f);
        Polynomial { terms }
    }

    pub fn var(v: &Var) -> Self {
        let mut terms = HashMap::new();
        terms.insert(Monomial::from(vec![(v.clone(), 1)]), F::one());
        Polynomial { terms }
    }

    pub fn degree(&self) -> usize {
        self.terms.keys().map(|t| t.degree()).max().unwrap_or(0)
    }

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

    pub fn contains(&self, v: &Var) -> bool {
        self.vars().contains(v)
    }

    pub fn vars(&self) -> Set<Var> {
        self.terms.keys().flat_map(|t| t.vars()).collect()
    }

    pub fn square(&mut self) {
        *self *= self.clone();
    }

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
            *self *= mul.clone();
            i -= 1;
        }
    }

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
    pub fn inline_vars(self, substitutions: &Ctx<Var, Polynomial<F>>) -> (Self, bool) {
        let mut new_poly = Polynomial::zero();
        let mut did_change = false;
        for (term, coeff) in self.terms.into_iter() {
            let mut new_mono = Polynomial::lit(&coeff);
            for (var, power) in term.vars().into_iter().zip(term.powers()) {
                if let Some(sub) = substitutions.get(&var) {
                    did_change = true;
                    let mut p = sub.clone();
                    p.pow(power);
                    new_mono *= p;
                } else {
                    let mut p = Polynomial::var(&var);
                    p.pow(power);
                    new_mono *= p;
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

impl<'a, F, D, A> Pretty<'a, D, A> for Polynomial<F>
where
    F: Field,
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.text(format!("{}", self))
    }

    fn is_nil(&self) -> bool {
        false
    }
}
