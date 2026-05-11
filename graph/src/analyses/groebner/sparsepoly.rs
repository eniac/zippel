use crate::PRef;
use crate::analyses::groebner::monomial::Monomial;
use ark_ff::Field;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use share::{Ctx, DocAllocator, DocBuilder, Pretty, Set};
use std::fmt;
use std::fmt::Debug;
use std::iter::Sum;

#[cfg(test)]
use crate::analyses::groebner::monomial::{ElimTerm, GrevLexTerm};

/// A sparse polynomial is a polynomial represented as a map from terms to their coefficients.
/// The terms are stored in a sorted order, and the coefficients are stored in a field.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SparsePolynomial<F: Field, T: Monomial> {
    pub terms: Ctx<T, F>, // Coefficient and Term pairs
}

/// Algebraic operations on SparsePolynomial
impl<F: Field, T: Monomial> AddAssign for SparsePolynomial<F, T> {
    fn add_assign(&mut self, other: Self) {
        for (term, coef) in other.terms {
            *self.terms.entry(term).or_insert(F::zero()) += coef;
        }
        self.terms.retain(|_, c| !c.is_zero()); // Remove zero coefficients
    }
}

impl<F: Field, T: Monomial> SubAssign for SparsePolynomial<F, T> {
    fn sub_assign(&mut self, other: Self) {
        for (term, coef) in other.terms {
            *self.terms.entry(term).or_insert(F::zero()) -= coef;
        }
        self.terms.retain(|_, c| !c.is_zero()); // Remove zero coefficients
    }
}

impl<F: Field, T: Monomial> Neg for SparsePolynomial<F, T> {
    type Output = Self;

    fn neg(self) -> Self {
        let mut result = self.clone();
        result.terms.modify(|_, coeff| {
            *coeff = (*coeff).neg();
        });
        result
    }
}
impl<F: Field, T: Monomial> MulAssign for SparsePolynomial<F, T> {
    fn mul_assign(&mut self, other: Self) {
        let mut new_terms = Ctx::new();
        for (term1, coeff1) in self.terms.iter() {
            for (term2, coeff2) in other.terms.iter() {
                let new_term = term1.clone() * term2.clone();
                let new_coeff = coeff1.clone() * coeff2.clone();
                *new_terms.entry(new_term).or_insert(F::zero()) += new_coeff;
            }
        }
        self.terms = new_terms;
        self.terms.retain(|_, c| !c.is_zero()); // Remove zero coefficients
    }
}

impl<F: Field, T: Monomial> Add for SparsePolynomial<F, T> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let mut result = self.clone();
        result += other;
        result
    }
}

impl<F: Field, T: Monomial> Add for &SparsePolynomial<F, T> {
    type Output = SparsePolynomial<F, T>;

    fn add(self, other: Self) -> SparsePolynomial<F, T> {
        let mut result = self.clone();
        result += other.clone();
        result
    }
}

impl<F: Field, T: Monomial> Sub for &SparsePolynomial<F, T> {
    type Output = SparsePolynomial<F, T>;

    fn sub(self, other: Self) -> SparsePolynomial<F, T> {
        let mut result = self.clone();
        result -= other.clone();
        result
    }
}

impl<F: Field, T: Monomial> Mul for &SparsePolynomial<F, T> {
    type Output = SparsePolynomial<F, T>;

    fn mul(self, other: Self) -> SparsePolynomial<F, T> {
        let mut result = self.clone();
        result *= other.clone();
        result
    }
}

impl<F: Field, T: Monomial> Sub for SparsePolynomial<F, T> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        let mut result = self.clone();
        result -= other;
        result
    }
}

impl<F: Field, T: Monomial> Mul for SparsePolynomial<F, T> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        let mut result = self.clone();
        result *= other;
        result
    }
}

impl<F: Field, T: Monomial> Sum for SparsePolynomial<F, T> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        let mut s = SparsePolynomial::zero();
        for x in iter {
            s += x;
        }
        s
    }
}

impl<F: Field, T: Monomial> From<Vec<(&T, F)>> for SparsePolynomial<F, T> {
    fn from(terms: Vec<(&T, F)>) -> Self {
        let mut poly = SparsePolynomial::zero();
        for (term, coeff) in terms {
            *poly.terms.entry(term.clone()).or_insert(F::zero()) += coeff;
        }
        poly.terms.retain(|_, c| !c.is_zero()); // Remove zero coefficients

        poly
    }
}

impl<F: Field, T: Monomial> fmt::Display for SparsePolynomial<F, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "0")
        } else {
            let mut terms: Vec<String> = Vec::new();
            let mut first = true;
            for (term, coeff) in self.terms.iter() {
                if coeff.is_one() && first {
                    terms.push(format!("{}", term));
                    first = false;
                } else if coeff.is_one() {
                    terms.push(format!("+ {}", term));
                } else if coeff.is_zero() {
                    continue;
                } else if coeff.clone().neg().is_one() {
                    terms.push(format!("- {}", term));
                    first = false;
                } else if first {
                    let term_str = format!("{}*{}", coeff, term);
                    terms.push(term_str);
                    first = false;
                } else {
                    let term_str = format!("+ {}*{}", coeff, term);
                    terms.push(term_str);
                }
            }
            write!(f, "{}", terms.join(" "))
        }
    }
}

/// Ad-hoc interface to SparsePolynomial with vector field coefficients
impl<F: Field, T: Monomial> SparsePolynomial<F, T> {
    pub fn zero() -> Self {
        SparsePolynomial { terms: Ctx::new() }
    }

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    pub fn lit(f: &F) -> SparsePolynomial<F, T> {
        let mut terms = Ctx::new();
        terms.insert(&T::from(vec![]), f);
        SparsePolynomial { terms }
    }

    pub fn var(v: &PRef) -> SparsePolynomial<F, T> {
        let mut terms = Ctx::new();
        terms.insert(&T::from(vec![(v.clone(), 1)]), &F::one());
        SparsePolynomial { terms }
    }

    pub fn degree(&self) -> usize {
        self.terms
            .iter()
            .map(|(t, _)| t.degree())
            .max()
            .unwrap_or(0)
    }

    pub fn is_constant(&self) -> bool {
        self.degree() == 0
    }

    pub fn leading_term(&self) -> Option<(F, T)> {
        self.terms.first().map(|(t, c)| (c.clone(), t.clone()))
    }

    pub fn contains(&self, v: &PRef) -> bool {
        self.vars().contains(v)
    }

    pub fn square(&mut self) {
        *self *= self.clone();
    }

    pub fn pow(&mut self, exp: usize) {
        if exp == 0 {
            *self = SparsePolynomial::lit(&F::one());
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

    pub fn vars(&self) -> Set<PRef> {
        self.terms
            .keys()
            .into_iter()
            .flat_map(|t| t.vars())
            .collect()
    }

    pub fn flat_map_vars<FF: Fn(PRef) -> Self>(self, f: &FF) -> SparsePolynomial<F, T> {
        let mut new_poly = SparsePolynomial::zero();
        for (term, coeff) in self.terms.into_iter() {
            // Start with the coefficient
            let mut new_mono = SparsePolynomial::lit(&coeff);
            // Apply the mapping function to each variable in the term
            for (var, power) in term.vars().into_iter().zip(term.powers().into_iter()) {
                let mut p = f(var);
                p.pow(power);
                new_mono *= p;
            }
            new_poly += new_mono;
        }
        new_poly
    }

    pub fn mul_by_term_and_scalar(&self, scalar: F, term: &T) -> SparsePolynomial<F, T> {
        if scalar.is_zero() {
            return SparsePolynomial::zero();
        }
        let new_terms: Vec<(T, F)> = self
            .terms
            .iter()
            .map(|(t, coeff)| (term.clone() * t.clone(), coeff.clone() * scalar.clone()))
            .collect();

        // Need to handle combining like terms and sorting.
        let mut combined_terms: Ctx<T, F> = Ctx::new(); // BTreeMap keeps terms sorted
        for (t, coeff) in new_terms {
            *combined_terms.entry(t).or_insert(F::zero()) += coeff;
        }
        combined_terms.retain(|_, c| !c.is_zero()); // Remove zero coefficients

        SparsePolynomial {
            terms: combined_terms,
        }
    }

    /// Compute the "syzygy" polynomial of two sparse polynomials
    /// for Buchberger's algorithm.
    pub fn s_poly(&self, other: &SparsePolynomial<F, T>) -> SparsePolynomial<F, T> {
        if self.is_zero() || other.is_zero() {
            return SparsePolynomial::zero();
        }

        let lt_self = self.leading_term().unwrap();
        let lt_other = other.leading_term().unwrap();

        let term_self = &lt_self.1;
        let coeff_self = lt_self.0;

        let term_other = &lt_other.1;
        let coeff_other = lt_other.0;

        let lcm_t = term_self.lcm(term_other);

        // Multiplier for self: (lcm_t / term_self) * (1 / coeff_self)
        let multiplier_term_self =
            (lcm_t.clone() / term_self.clone()).expect("Term division failed for LCM/LT");
        let multiplier_scalar_self = coeff_self
            .inverse()
            .expect("Leading coefficient must be non-zero");

        // Multiplier for other: (lcm_t / term_other) * (1 / coeff_other)
        let multiplier_term_other =
            (lcm_t.clone() / term_other.clone()).expect("Term division failed for LCM/LT");
        let multiplier_scalar_other = coeff_other
            .inverse()
            .expect("Leading coefficient must be non-zero");

        let mut poly_self_scaled =
            self.mul_by_term_and_scalar(multiplier_scalar_self, &multiplier_term_self);
        let poly_other_scaled =
            other.mul_by_term_and_scalar(multiplier_scalar_other, &multiplier_term_other);

        // S = poly_self_scaled - poly_other_scaled
        poly_self_scaled -= poly_other_scaled;
        poly_self_scaled
    }

    /// Splits the polynomial `P` (implicitly `P=0`) into `lhs` and `rhs` such that
    /// `M_gcd * lhs = -rhs`, where `lhs` contains terms derived from the original
    /// terms having only `factor(v) = true` variables, factored by the monomial GCD (`M_gcd`).
    /// `rhs` contains the negation of the terms having at least one `eliminate=false` variable.
    ///
    /// Assumes the `Monomial` trait provides a `gcd` method.
    ///
    /// # Returns
    ///
    /// A tuple `(lhs, rhs, divided_vars)` where:
    /// - `lhs`: The factored polynomial part with `eliminate=true` variables.
    /// - `rhs`: The negated polynomial part with `eliminate=false` variables.
    /// - `divided_vars`: A `HashSet` of variables present in the `M_gcd` that was factored out.
    pub fn isolate_elimination_vars<FF: Fn(&PRef) -> bool>(
        &self,
        factor: &FF,
    ) -> (Self, Self, Set<PRef>) {
        let mut tmp_lhs_terms: Ctx<T, F> = Ctx::new();
        let mut tmp_rhs_terms: Ctx<T, F> = Ctx::new();

        // 1. Initial Split
        for (monomial, coefficient) in self.terms.iter() {
            let vars = monomial.vars();
            // Constants assigned to LHS, check if this is desired.
            let is_lhs_term = vars.is_empty() || vars.iter().any(factor);

            if is_lhs_term {
                tmp_lhs_terms.insert(monomial, coefficient);
            } else {
                tmp_rhs_terms.insert(monomial, coefficient);
            }
        }

        // 2. Find LHS Monomial GCD using Monomial::gcd
        let mut m_gcd = tmp_lhs_terms
            .keys()
            .iter()
            .cloned()
            .reduce(|acc, item| acc.gcd(&item)) // Use the gcd method
            .unwrap_or_default(); // Default to constant if tmp_lhs_terms is empty

        // 2.5: Remove factored variables from gcd by dividing
        for pv in tmp_lhs_terms.keys().iter().flat_map(|pv| pv.vars()) {
            let m_pv = T::from(vec![(pv.clone(), 1)]);
            if let Some(new_gcd) = m_gcd.clone() / m_pv {
                m_gcd = new_gcd;
            }
        }

        let mut final_lhs_terms: Ctx<T, F>;
        let divided_vars: Set<PRef>;

        // 3. Factor LHS & Track Variables (if GCD is not constant)
        if !m_gcd.is_constant() {
            final_lhs_terms = Ctx::new();
            for (monomial, coefficient) in tmp_lhs_terms.into_iter() {
                // Perform division: monomial / m_gcd
                match monomial.div(m_gcd.clone()) {
                    Some(factored_monomial) => {
                        final_lhs_terms.insert(&factored_monomial, &coefficient)
                    }
                    None => panic!("Failed to divide monomial by GCD"),
                };
            }
            divided_vars = m_gcd.vars().into_iter().collect();
        } else {
            // No factoring needed if GCD is constant
            final_lhs_terms = tmp_lhs_terms;
            divided_vars = Set::new();
        }

        // 4. Construct final polynomials
        let final_lhs = SparsePolynomial {
            terms: final_lhs_terms,
        };

        let initial_rhs = SparsePolynomial {
            terms: tmp_rhs_terms,
        };

        // 5. Negate RHS
        let final_rhs = -initial_rhs;

        // 6. Return
        (final_lhs, final_rhs, divided_vars)
    }
}

impl<'a, D, A, F, T> Pretty<'a, D, A> for SparsePolynomial<F, T>
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    F: Field,
    T: Monomial,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.text(format!("{}", self))
    }

    fn is_nil(&self) -> bool {
        false
    }
}

#[cfg(test)]
pub fn elim_sparse_poly<F: Field>(
    terms: Vec<(F, Vec<(&PRef, usize)>)>,
) -> SparsePolynomial<F, ElimTerm> {
    let mut vars = Set::new();

    let processed_terms = terms
        .into_iter()
        .map(|(coeff, term_vec)| {
            (
                ElimTerm::from(
                    term_vec
                        .into_iter()
                        .map(|(k, v)| {
                            let var = k.clone();
                            vars.insert(var.clone());
                            (var, v)
                        })
                        .collect::<Vec<_>>(),
                ),
                coeff,
            )
        })
        .collect();

    SparsePolynomial {
        terms: processed_terms,
    }
}

#[cfg(test)]
pub fn grevlex_sparse_poly<F: Field>(
    terms: Vec<(F, Vec<(&PRef, usize)>)>,
) -> SparsePolynomial<F, GrevLexTerm> {
    let mut vars = Set::new();

    let processed_terms = terms
        .into_iter()
        .map(|(coeff, term_vec)| {
            (
                GrevLexTerm::from(
                    term_vec
                        .into_iter()
                        .map(|(k, v)| {
                            let var = k.clone();
                            vars.insert(var.clone());
                            (var, v)
                        })
                        .collect::<Vec<_>>(),
                ),
                coeff,
            )
        })
        .collect();

    SparsePolynomial {
        terms: processed_terms,
    }
}
