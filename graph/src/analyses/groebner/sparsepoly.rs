use ark_ff::Field;
use backend::{Value, ArkConfig};
use crate::GOp;
use core::cmp::Ordering;
use core::ops::{Add, Neg, Sub, Mul, Div, AddAssign, MulAssign, SubAssign};
use share::{Ctx, Set, Pretty, DocAllocator, DocBuilder};
use std::fmt::Debug;
use std::fmt;

/// For elimination order we need a classification of variables into
/// two classes. The ones which map to [true] are eliminated before
/// those which map to [false].
pub trait Var: Clone + PartialEq + Eq + PartialOrd + Ord + fmt::Display {
    fn eliminate(&self) -> bool;
}

/// A monomial trait that represents a term in a polynomial.
pub trait Monomial<V: Var>:
    Clone
    + PartialEq
    + Eq
    + Default
    + fmt::Display
    + MulAssign
    + Mul<Output = Self>
    + Div<Output = Option<Self>>
    + From<Vec<(V, usize)>>
    + Ord {

    fn vars(&self) -> Vec<V>;
    fn powers(&self) -> Vec<usize>;
    fn degree(&self) -> usize {
        self.powers().iter().sum()
    }
    fn is_constant(&self) -> bool {
        self.vars().is_empty()
    }
    fn evaluate<F: Field>(&self, p: &Ctx<V, F>) -> F;

    fn is_divided(&self, other: &Self) -> bool;

    fn lcm(&self, other: &Self) -> Self;
    fn gcd(&self, other: &Self) -> Self;

    fn grevlex(&self, other: &Self) -> Ordering;
}

/// A sparse polynomial is a polynomial represented as a map from terms to their coefficients.
/// The terms are stored in a sorted order, and the coefficients are stored in a field.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SparsePolynomial<F: Field, V: Var, T: Monomial<V>> {
    pub terms: Ctx<T, F>, // Coefficient and Term pairs
    _marker: std::marker::PhantomData<V>,
}

/// Algebraic operations on SparsePolynomial
impl<F: Field, V: Var, T: Monomial<V>> AddAssign for SparsePolynomial<F, V, T> {
    fn add_assign(&mut self, other: Self) {
        for (term, coef) in other.terms {
            *self.terms.entry(term).or_insert(F::zero()) += coef;
        }
        self.terms.retain(|_, c| !c.is_zero()); // Remove zero coefficients
    }
}

impl<F: Field, V: Var, T: Monomial<V>> SubAssign for SparsePolynomial<F, V, T> {
    fn sub_assign(&mut self, other: Self) {
        for (term, coef) in other.terms {
            *self.terms.entry(term).or_insert(F::zero()) -= coef;
        }
        self.terms.retain(|_, c| !c.is_zero()); // Remove zero coefficients
    }
}

impl<F: Field, V: Var, T: Monomial<V>> Neg for SparsePolynomial<F, V, T> {
    type Output = Self;

    fn neg(self) -> Self {
        let mut result = self.clone();
        for (_, coeff) in result.terms.iter_mut() {
            *coeff = (*coeff).neg();
        }
        result
    }
}
impl<F: Field, V: Var, T: Monomial<V>> MulAssign for SparsePolynomial<F, V, T> {
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

impl<C: ArkConfig> From<SparsePolynomial<C::F, GOp<C>, LexDegTerm<GOp<C>>>> for GOp<C> {
    fn from(p: SparsePolynomial<C::F, GOp<C>, LexDegTerm<GOp<C>>>) -> Self {
        let mut result = p.terms.first().unwrap().0.clone().into();
        for (term, coeff) in p.terms.into_iter().skip(1) {
            result += GOp::from(term) * GOp::Value(Value::Scalar(coeff));
        }
        result
    }
}

impl<C: ArkConfig> From<LexDegTerm<GOp<C>>> for GOp<C> {
    fn from(t: LexDegTerm<GOp<C>>) -> Self {
        let mut result = t.vars.first().unwrap().0.clone();
        for (var, power) in t.vars.into_iter().skip(1) {
            let gpow : GOp<C>= power.into();
            result *= var ^ gpow;
        }
        result
    }
}

impl<F: Field, V: Var, T: Monomial<V>> Add for SparsePolynomial<F, V, T> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let mut result = self.clone();
        result += other;
        result
    }
}

impl<F: Field, V: Var, T: Monomial<V>> Sub for SparsePolynomial<F, V, T> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        let mut result = self.clone();
        result -= other;
        result
    }
}

impl<F: Field, V: Var, T: Monomial<V>> Mul for SparsePolynomial<F, V, T> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        let mut result = self.clone();
        result *= other;
        result
    }
}

impl<F: Field, V: Var, T: Monomial<V>> From<Vec<(&T, F)>> for SparsePolynomial<F, V, T> {
    fn from(terms: Vec<(&T, F)>) -> Self {
        let mut poly = SparsePolynomial::zero();
        for (term, coeff) in terms {
            *poly.terms.entry(term.clone()).or_insert(F::zero()) += coeff;
        }
        poly.terms.retain(|_, c| !c.is_zero()); // Remove zero coefficients

        poly
    }
}

impl<F: Field, V: Var, T: Monomial<V>> From<Vec<(F, Vec<(&V, usize)>)>> for SparsePolynomial<F, V, T> {
    fn from(terms: Vec<(F, Vec<(&V, usize)>)>) -> Self {
        let mut vars = Set::new();

        let processed_terms =
            terms.into_iter()
            .map(|(coeff, term_vec)|
                (T::from(term_vec.into_iter().map(|(k, v)| {
                    let var = k.clone();
                    vars.insert(var.clone());
                    (var, v)
                }).collect()), coeff.into()))
            .collect();

        SparsePolynomial {
            terms: processed_terms,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<F: Field, V: Var, T: Monomial<V>> fmt::Display for SparsePolynomial<F, V, T> {
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
                    continue
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
impl<F: Field, V: Var, T: Monomial<V>> SparsePolynomial<F, V, T> {
    pub fn zero() -> Self {
        SparsePolynomial {
            terms: Ctx::new(),
            _marker: std::marker::PhantomData,
        }
    }

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    pub fn lit(f: &F) -> SparsePolynomial<F, V, T> {
        let mut terms = Ctx::new();
        terms.insert(&T::from(vec![]), f);
        SparsePolynomial {
            terms,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn var(v: &V) -> SparsePolynomial<F, V, T> {
        let mut terms = Ctx::new();
        terms.insert(&T::from(vec![(v.clone(), 1)]), &F::one());
        SparsePolynomial {
            terms,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn degree(&self) -> usize {
        self.terms.iter().map(|(t, _)| t.degree()).max().unwrap_or(0)
    }

    pub fn is_constant(&self) -> bool {
        self.degree() == 0
    }

    pub fn leading_term(&self) -> Option<(F, T)> {
        self.terms.first().map(|(t, c)| (c.clone(), t.clone()))
    }

    pub fn contains(&self, v: &V) -> bool {
        self.vars().contains(v)
    }

    pub fn square(&mut self) {
        *self *= self.clone();
    }

    pub fn pow(&mut self, exp: usize) {
        let mut i = exp;
        while (i % 2) == 0 {
            self.square();
            i /= 2;
        }
        let mul = self.clone();
        while i > 0 {
            *self *= mul.clone();
            i -= 1;
        }
    }

    pub fn vars(&self) -> Set<V> {
        self.terms.keys().iter().flat_map(|t| t.vars()).collect()
    }

    pub fn map_vars<VV: Var, TT: Monomial<VV>, FF: Fn(V) -> VV>(self, f: &FF) -> SparsePolynomial<F, VV, TT> {
        let mut new_terms = Ctx::new();
        for (term, coeff) in self.terms.into_iter() {
            let new_term: Vec<(VV, usize)> = term.vars().into_iter().map(|v | f(v)).zip(term.powers().into_iter()).collect();
            new_terms.insert(&TT::from(new_term), &coeff);
        }
        SparsePolynomial {
            terms: new_terms,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn flat_map_vars<FF: Fn(V) -> Self>(self, f: &FF) -> SparsePolynomial<F, V, T> {
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

    pub fn mul_by_term_and_scalar(
        &self,
        scalar: F,
        term: &T,
    ) -> SparsePolynomial<F, V, T> {
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
            _marker: std::marker::PhantomData,
        }
    }

    /// Compute the "syzygy" polynomial of two sparse polynomials
    /// for Buchberger's algorithm.
    pub fn s_poly(
        &self,
        other: &SparsePolynomial<F, V, T>,
    ) -> SparsePolynomial<F, V, T> {
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
        let multiplier_term_self = (lcm_t.clone() / term_self.clone()).expect("Term division failed for LCM/LT");
        let multiplier_scalar_self = coeff_self.inverse().expect("Leading coefficient must be non-zero");

        // Multiplier for other: (lcm_t / term_other) * (1 / coeff_other)
        let multiplier_term_other = (lcm_t.clone() / term_other.clone()).expect("Term division failed for LCM/LT");
        let multiplier_scalar_other = coeff_other.inverse().expect("Leading coefficient must be non-zero");

        let mut poly_self_scaled = self.mul_by_term_and_scalar(multiplier_scalar_self, &multiplier_term_self);
        let poly_other_scaled = other.mul_by_term_and_scalar(multiplier_scalar_other, &multiplier_term_other);

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
    pub fn isolate_elimination_vars<FF: Fn(&V)->bool>(&self, factor: &FF) -> (Self, Self, Set<V>) {
        let mut tmp_lhs_terms: Ctx<T, F> = Ctx::new();
        let mut tmp_rhs_terms: Ctx<T, F> = Ctx::new();

        // 1. Initial Split
        for (monomial, coefficient) in self.terms.iter() {
            let vars = monomial.vars();
            // Constants assigned to LHS, check if this is desired.
            let is_lhs_term = vars.is_empty() || vars.iter().any(|v| factor(v));

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
        let divided_vars: Set<V>;

        // 3. Factor LHS & Track Variables (if GCD is not constant)
        if !m_gcd.is_constant() {
            final_lhs_terms = Ctx::new();
            for (monomial, coefficient) in tmp_lhs_terms.into_iter() {
                // Perform division: monomial / m_gcd
                match monomial.div(m_gcd.clone()) {
                    Some(factored_monomial) =>
                        final_lhs_terms.insert(&factored_monomial, &coefficient),
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
            _marker: std::marker::PhantomData,
        };

        let initial_rhs = SparsePolynomial {
            terms: tmp_rhs_terms,
            _marker: std::marker::PhantomData,
        };

        // 5. Negate RHS
        let final_rhs = -initial_rhs;

        // 6. Return
        (final_lhs, final_rhs, divided_vars)
    }
}

impl<'a, D, A, F, V, T> Pretty<'a, D, A> for SparsePolynomial<F, V, T>
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    F: Field,
    V: Var,
    T: Monomial<V>,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.text(format!("{}", self))
    }

    fn is_nil(&self) -> bool {
        false
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Debug)]
pub struct LexDegTerm<V: Var> {
    pub vars: Ctx<V, usize>, // (var index, power)
}

impl<V: Var> LexDegTerm<V> {
    pub fn new(vars: Ctx<V, usize>) -> Self {
        LexDegTerm { vars }
    }


}

impl<V: Var> Default for LexDegTerm<V> {
    fn default() -> Self {
        LexDegTerm::new(Ctx::new())
    }
}

/// Multiplies two terms. (var, power) pairs are combined by adding powers
/// for common variables.
impl<V: Var> MulAssign for LexDegTerm<V> {
    fn mul_assign(&mut self, other: Self) {
        for (var, power) in other.vars.iter() {
            *self.vars.entry(var.clone()).or_insert(0) += power;
        }
    }
}

impl<V: Var> Mul for LexDegTerm<V> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        let mut result = self.clone();
        result *= other;
        result
    }
}

impl<'a, V: Var> Mul for &'a LexDegTerm<V> {
    type Output = LexDegTerm<V>;

    fn mul(self, other: &'a LexDegTerm<V>) -> LexDegTerm<V> {
        self.clone() * other.clone()
    }
}

impl<V: Var> fmt::Display for LexDegTerm<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_constant() {
            write!(f, "1")
        } else {
            let mut terms: Vec<String> = Vec::new();
            for (var, power) in self.vars.iter() {
                if *power == 1 {
                    terms.push(format!("{}", var));
                } else if *power > 0 {
                    terms.push(format!("{}^{}", var, power));
                }
            }
            write!(f, "{}", terms.join("*"))
        }
    }
}

impl<V: Var> Div for LexDegTerm<V> {
    type Output = Option<Self>;

    fn div(self, other: Self) -> Option<Self> {
        if !self.is_divided(&other) {
            return None;
        }

        let mut powers1 = self.vars.iter().map(|(v, p)| (v.clone(), *p)).collect::<Vec<_>>();
        for (var, power2) in other.vars.iter() {
            // We know var is in powers1 with sufficient power because term_is_divided was true
            if let Some(power1) = powers1.iter_mut().find(|(v, _)| v == var) {
                power1.1 -= power2;
            }
        }

        Some(Self::new(powers1.into_iter().filter(|(_, p)| *p > 0).collect()))
    }
}

impl<'a, V: Var> Div for &'a LexDegTerm<V> {
    type Output = Option<LexDegTerm<V>>;

    fn div(self, other: &'a LexDegTerm<V>) -> Option<LexDegTerm<V>> {
        self.clone() / other.clone()
    }
}

impl<V: Var> From<Vec<(V, usize)>> for LexDegTerm<V> {
    fn from(vars: Vec<(V, usize)>) -> Self {
        LexDegTerm::new(vars.into_iter().collect())
    }
}

impl<'a, V: Var> From<Vec<(&'a V, usize)>> for LexDegTerm<V> {
    fn from(vars: Vec<(&'a V, usize)>) -> Self {
        LexDegTerm::new(vars.into_iter().map(|(v, p)| (v.clone(), p)).collect())
    }
}

impl<V: Var> Monomial<V> for LexDegTerm<V> {
    fn vars(&self) -> Vec<V> {
        self.vars.iter().map(|(v, _)| v.clone()).collect()
    }
    fn powers(&self) -> Vec<usize> {
        self.vars.iter().map(|(_, p)| *p).collect()
    }
    fn is_constant(&self) -> bool {
        self.vars.iter().next().is_none() // Empty vec means the term is 1 (constant)
    }

    fn evaluate<F: Field>(&self, p: &Ctx<V, F>) -> F {
        let mut result = F::one();
        for (var, power) in self.vars.iter() {
            if let Some(value) = p.get(&var) {
                for _ in 0..*power {
                    result *= value;
                }
            } else {
                // Variable not found in context, assume it evaluates to 1
            }
        }
        result
    }
    fn is_divided(&self, other: &Self) -> bool {
        for (var, power2) in other.vars.iter() {
            match self.vars.get(var) {
                Some(power1) => {
                    if power1 < power2 {
                        return false;
                    }
                }
                None => return false, // other has a variable self doesn't have
            }
        }
        true // All variables in other are in self with sufficient power
    }

    fn lcm(&self, other: &Self) -> Self {
        let mut lcm_powers: Vec<(V, usize)> = self.vars.iter().map(|(v, p)| (v.clone(), *p)).collect();
        for (var, power2) in other.vars.iter() {
            match lcm_powers.iter_mut().find(|(v, _)| v == var) {
                Some((_, power1)) => *power1 = (*power1).max(*power2),
                None => lcm_powers.push((var.clone(), *power2)),
            }
        }
        Self::new(lcm_powers.into_iter().collect())
    }

    fn gcd(&self, other: &Self) -> Self {
        let mut gcd_powers: Vec<(V, usize)> = Vec::new();
        for (var1, power1) in self.vars.iter() {
            if let Some((_, power2)) = other.vars.iter().find(|(v, _p)| v == &var1) {
                let min_power = (*power1).min(*power2);
                if min_power > 0 {
                    gcd_powers.push((var1.clone(), min_power));
                }
            }
        }
        Self::new(gcd_powers.into_iter().collect())
    }


    // Graded reverse lexicographic order (grevlex, or degrevlex for degree reverse lexicographic order)
    // compares the total degree first, then uses a lexicographic order as tie-breaker, but it reverses
    // the outcome of the lexicographic comparison so that lexicographically larger monomials of the same
    // degree are considered to be degrevlex smaller.
    fn grevlex(&self, other: &Self) -> Ordering {
        // Compare total degrees of the monomials
        match self.degree().cmp(&other.degree()) {
            Ordering::Equal => {},
            order => return order.reverse(),
        };

        // Compare powers in reverse lexicographic order
        for ((v1, p1), (v2, p2)) in self.vars.iter().zip(other.vars.iter()) {
            match (v1.cmp(v2), p1.cmp(p2)) {
                (Ordering::Equal, Ordering::Equal) => continue,
                (Ordering::Equal, order) => return order.reverse(),
                (order, _) => return order
            }
        }
        Ordering::Equal
    }
}

/// Define elimination order comparison. First, we compare principals such that if any variable has
/// Principal::Any > Principal::Verifier and Principal::Any > Principal::Prover, then the same is true for LexDegTerm.
/// If the principals are equal, then perform a grevlex comparison on the powers of the variables (graded, reverse lexicographic order).
impl<V: Var> Ord for LexDegTerm<V> {
    fn cmp(&self, other: &Self) -> Ordering {
        let elim_self = LexDegTerm {
            vars: self.vars.iter()
                .filter(|(var, _)| var.eliminate())
                .map(|(var, power)| (var.clone(), *power))
                .collect::<Ctx<V, usize>>()
        };

        let elim_other = LexDegTerm {
            vars: other.vars.iter()
                .filter(|(var, _)| var.eliminate())
                .map(|(var, power)| (var.clone(), *power))
                .collect::<Ctx<V, usize>>()
        };

        // Compare the variables we prefer to eliminate first, using the grevlex monomial order
        match elim_self.grevlex(&elim_other) {
            Ordering::Equal => {},
            order => return order
        };

        // If they are equal, compare the remaining variables
        let other_self = LexDegTerm {
            vars: self.vars.iter()
                .filter(|(var, _)| !var.eliminate())
                .map(|(var, power)| (var.clone(), *power))
                .collect::<Ctx<V, usize>>()
        };
        let other_other = LexDegTerm {
            vars: other.vars.iter()
                .filter(|(var, _)| !var.eliminate())
                .map(|(var, power)| (var.clone(), *power))
                .collect::<Ctx<V, usize>>()
        };

        // If they are equal, compare the remaining variables
        other_self.grevlex(&other_other)
    }
}

/// To report back results to the user, we need to substitute GOp<C> in the
/// place of variables. Instantiate Var with GOp<C>
impl<C: ArkConfig> Var for GOp<C> {
    fn eliminate(&self) -> bool {
        match self {
            GOp::Random(_, _) => true,
            _ => false
        }
    }
}