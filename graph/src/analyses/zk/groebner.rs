use ark_ff::Field;
use crate::principal::Principal;
use crate::Ref;
use core::cmp::Ordering;
use core::ops::{Add, Sub, Mul, Div, AddAssign, MulAssign, DivAssign, SubAssign};
use share::{Ctx, Set, Pretty, BoxAllocator, DocAllocator, DocBuilder};
use ark_ff::{One, Zero};
use std::collections::VecDeque;
use std::fmt::Debug;
use std::fmt;
use log::debug;

pub trait Var = Clone + PartialEq + Eq + PartialOrd + Ord + Debug;

pub trait Monomial<V: Var>:
    Debug
    + Clone
    + PartialEq
    + Eq
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
    fn grevlex(&self, other: &Self) -> Ordering;
}

/// A sparse polynomial is a polynomial represented as a map from terms to their coefficients.
/// The terms are stored in a sorted order, and the coefficients are stored in a field.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SparsePolynomial<F: Field, V: Var, T: Monomial<V>> {
    pub num_vars: usize,
    pub terms: Ctx<T, VecField<F>>, // Coefficient and Term pairs
    _marker: std::marker::PhantomData<V>,
}

/// Coefficients are vectors of scalars
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub struct VecField<F: Field>(Vec<F>);

impl<F: Field> From<F> for VecField<F> {
    fn from(value: F) -> Self {
        VecField(vec![value])
    }
}

impl<F: Field> fmt::Display for VecField<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "0[{}]", self.0.len())
        } else if self.0.len() == 1 {
            write!(f, "{}", self.0[0])
        } else {
            write!(f, "[{}", self.0[0])?;
            for coeff in self.0.iter().skip(1) {
                write!(f, ", {}", coeff)?;
            }
            write!(f, "]")
        }
    }
}

/// Algebraic operations on VecField
impl<F: Field> Zero for VecField<F> {
    fn zero() -> Self {
        VecField(vec![F::zero()])
    }
    fn is_zero(&self) -> bool {
        self.0.iter().all(|c| c.is_zero())
    }
}

impl<F: Field> One for VecField<F> {
    fn one() -> Self {
        VecField(vec![F::one()])
    }
}

impl<F: Field> AddAssign for VecField<F> {
    fn add_assign(&mut self, other: Self) {
        let mut other = other;
        if self.0.len() < other.0.len() {
            self.0.extend(vec![self.0[0]; other.0.len()-self.0.len()]);
        } else if other.0.len() < self.0.len() {
            other.0.extend(vec![other.0[0]; self.0.len()-other.0.len()]);
        }
        for (a, b) in self.0.iter_mut().zip(other.0.iter_mut()) {
            *a += *b;
        }
    }
}

impl<F: Field> Add for VecField<F> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let mut result = self.clone();
        result += other;
        result
    }
}

impl<F: Field> SubAssign for VecField<F> {
    fn sub_assign(&mut self, other: Self) {
        let mut other = other;
        if self.0.len() < other.0.len() {
            self.0.extend(vec![self.0[0]; other.0.len()-self.0.len()]);
        } else if other.0.len() < self.0.len() {
            other.0.extend(vec![other.0[0]; self.0.len()-other.0.len()]);
        }
        for (a, b) in self.0.iter_mut().zip(other.0.iter_mut()) {
            *a -= *b;
        }
    }
}

impl<F: Field> Sub for VecField<F> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        let mut result = self.clone();
        result -= other;
        result
    }
}

impl<F: Field> MulAssign for VecField<F> {
    fn mul_assign(&mut self, other: Self) {
        let mut other = other;
        if self.0.len() < other.0.len() {
            self.0.extend(vec![self.0[0]; other.0.len()-self.0.len()]);
        } else if other.0.len() < self.0.len() {
            other.0.extend(vec![other.0[0]; self.0.len()-other.0.len()]);
        }
        for (a, b) in self.0.iter_mut().zip(other.0.iter_mut()) {
            *a *= *b;
        }
    }
}

impl<F: Field> Mul for VecField<F> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        let mut result = self.clone();
        result *= other;
        result
    }
}

impl<F: Field> DivAssign for VecField<F> {
    fn div_assign(&mut self, other: Self) {
        let mut other = other;
        if self.0.len() < other.0.len() {
            self.0.extend(vec![self.0[0]; other.0.len()-self.0.len()]);
        } else if other.0.len() < self.0.len() {
            other.0.extend(vec![other.0[0]; self.0.len()-other.0.len()]);
        }
        for (a, b) in self.0.iter_mut().zip(other.0.iter_mut()) {
            *a /= *b;
        }
    }
}

impl<F: Field> Div for VecField<F> {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        let mut result = self.clone();
        result /= other;
        result
    }
}

impl<F: Field> VecField<F> {
    pub fn inverse(&self) -> Option<Self> {
        self.0.iter().map(|c| c.inverse()).collect::<Option<Vec<_>>>().map(|v| VecField(v))
    }
}

impl<F: Field> From<Vec<F>> for VecField<F> {
    fn from(value: Vec<F>) -> Self {
        VecField(value)
    }
}

/// Algebraic operations on SparsePolynomial
impl<F: Field, V: Var, T: Monomial<V>> AddAssign for SparsePolynomial<F, V, T> {
    fn add_assign(&mut self, other: Self) {
        for (term, coef) in other.terms {
            *self.terms.entry(term).or_insert(VecField::zero()) += coef;
        }
        self.terms.retain(|_, c| !c.is_zero()); // Remove zero coefficients
    }
}

impl<F: Field, V: Var, T: Monomial<V>> SubAssign for SparsePolynomial<F, V, T> {
    fn sub_assign(&mut self, other: Self) {
        for (term, coef) in other.terms {
            *self.terms.entry(term).or_insert(VecField::zero()) -= coef;
        }
        self.terms.retain(|_, c| !c.is_zero()); // Remove zero coefficients
    }
}

impl<F: Field, V: Var, T: Monomial<V>> MulAssign for SparsePolynomial<F, V, T> {
    fn mul_assign(&mut self, other: Self) {
        let mut new_terms = Ctx::new();
        for (term1, coeff1) in self.terms.iter() {
            for (term2, coeff2) in other.terms.iter() {
                let new_term = term1.clone() * term2.clone();
                let new_coeff = coeff1.clone() * coeff2.clone();
                *new_terms.entry(new_term).or_insert(VecField::zero()) += new_coeff;
            }
        }
        self.terms = new_terms;
        self.terms.retain(|_, c| !c.is_zero()); // Remove zero coefficients
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

impl<F: Field, V: Var, T: Monomial<V>> From<Vec<(T, F)>> for SparsePolynomial<F, V, T> {
    fn from(terms: Vec<(T, F)>) -> Self {
        let mut poly = SparsePolynomial::zero();
        for (term, coeff) in terms {
            *poly.terms.entry(term).or_insert(VecField::zero()) += coeff.into();
        }
        poly.terms.retain(|_, c| !c.is_zero()); // Remove zero coefficients

        let keys = poly.terms.keys().iter().flat_map(|t| t.vars()).collect::<Set<_>>();
        // Set num_vars based on the terms
        poly.num_vars = keys.len();
        poly
    }
}

impl<F: Field, V: Var, T: Monomial<V>> fmt::Display for SparsePolynomial<F, V, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "0")
        } else {
            let mut terms: Vec<String> = Vec::new();
            for (term, coeff) in self.terms.iter() {
                if !coeff.is_zero() {
                    let term_str = format!("{}*{}", coeff, term);
                    terms.push(term_str);
                }
            }
            write!(f, "{}", terms.join(" + "))
        }
    }
}

/// Ad-hoc interface to SparsePolynomial with vector field coefficients
impl<F: Field, V: Var, T: Monomial<V>> SparsePolynomial<F, V, T> {
    pub fn new(num_vars: usize, terms: Vec<(F, Vec<(V, usize)>)>) -> SparsePolynomial<F, V, T> {
         let processed_terms =
             terms.into_iter()
             .map(|(coeff, term_vec)| (T::from(term_vec), coeff.into()))
             .collect();
         SparsePolynomial {
             num_vars,
             terms: processed_terms,
             _marker: std::marker::PhantomData,
         }
    }

    pub fn zero() -> Self {
        SparsePolynomial {
            num_vars: 0,
            terms: Ctx::new(),
            _marker: std::marker::PhantomData,
        }
    }

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    pub fn lit(f: &VecField<F>) -> SparsePolynomial<F, V, T> {
        let mut terms = Ctx::new();
        terms.insert(&T::from(vec![]), f);
        SparsePolynomial {
            num_vars: 0,
            terms,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn var(v: &V) -> SparsePolynomial<F, V, T> {
        let mut terms = Ctx::new();
        terms.insert(&T::from(vec![(v.clone(), 1)]), &VecField::one());
        SparsePolynomial {
            num_vars: 1,
            terms,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn degree(&self) -> usize {
        self.terms.iter().map(|(t, _)| t.degree()).max().unwrap_or(0)
    }

    pub fn leading_term(&self) -> Option<(VecField<F>, T)> {
        self.terms.iter().find_map(|(k, v)| if !k.is_constant() { Some((v.clone(), k.clone())) } else { None })
    }

    pub fn contains(&self, v: &V) -> bool {
        self.vars().contains(v)
    }

    pub fn vars(&self) -> Set<V> {
        self.terms.keys().iter().flat_map(|t| t.vars()).collect()
    }

    pub fn mul_by_term_and_scalar(
        &self,
        scalar: VecField<F>,
        term: &T,
    ) -> SparsePolynomial<F, V, T> {
        if scalar.is_zero() {
            return SparsePolynomial::zero();
        }
        let new_terms: Vec<(T, VecField<F>)> = self
            .terms
            .iter()
            .map(|(t, coeff)| (term.clone() * t.clone(), coeff.clone() * scalar.clone()))
            .collect();

        // Need to handle combining like terms and sorting.
        let mut combined_terms: Ctx<T, VecField<F>> = Ctx::new(); // BTreeMap keeps terms sorted
        for (t, coeff) in new_terms {
            *combined_terms.entry(t).or_insert(VecField::zero()) += coeff;
        }
        combined_terms.retain(|_, c| !c.is_zero()); // Remove zero coefficients

        SparsePolynomial {
            num_vars: self.num_vars,
            terms: combined_terms,
            _marker: std::marker::PhantomData,
        }
    }

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
}

/// Reduces polynomial `p` with respect to the basis `G`.
/// Returns the remainder `r` such that `p = sum(q_i * g_i) + r`, and no term in `r`
/// is divisible by the leading term of any `g_i` in `G`.
/// Assumes `G` does not contain the zero polynomial.
pub fn reduce<F, V, T>(
    mut p: SparsePolynomial<F, V, T>,
    basis: &[SparsePolynomial<F, V, T>],
) -> SparsePolynomial<F, V, T>
where
    F: Field,
    V: Var,
    T: Monomial<V>,
{
    let mut remainder = SparsePolynomial::zero();
    remainder.num_vars = p.num_vars; // Inherit num_vars

    // While p is not zero
    while let Some((p_lc, p_lt)) = p.leading_term() {
        let mut division_occurred = false;
        for g in basis {
            if g.is_zero() { continue; } // Skip zero polynomials in basis if any

            if let Some((g_lc, g_lt)) = g.leading_term() {
                // Check if LM(p) is_divided LM(g)
                if p_lt.is_divided(&g_lt) {
                    // Calculate multiplier term and scalar
                    let multiplier_term = (p_lt / g_lt).expect("Division should succeed if is_divided is true");
                    // Need coeff division: p_lc / g_lc
                    let g_lc_inv = g_lc.inverse().expect("Leading coefficient must be invertible");
                    let multiplier_scalar = p_lc * g_lc_inv;

                    // Calculate the polynomial to subtract: scalar * term * g
                    let to_subtract = g.mul_by_term_and_scalar(multiplier_scalar, &multiplier_term);

                    // p = p - to_subtract
                    p -= to_subtract;
                    division_occurred = true;
                    break; // Restart the check with the new p from the beginning of the basis
                }
            } else {
                 // Basis element g is zero, should ideally not happen in a cleaned basis
                 // or should be filtered out beforehand.
                 eprintln!("Warning: Encountered zero polynomial in basis during reduction.");
            }
        } // End for g in basis

        if !division_occurred {
            // Leading term of p is not divisible by any leading term in basis.
            // Move LT(p) to the remainder.
            // Safe to unwrap, we checked p.leading_term() in the while condition
            let (lt, lc) = p.terms.pop_first().unwrap(); // BTreeMap specific method
            remainder.terms.insert(&lt, &lc); // Add to remainder

            // p has been modified by removing its leading term implicitly via pop_first()
            // No explicit subtraction needed here.
        }
        // Loop continues with the modified p
    }

    remainder
}


/// Computes a Gröbner basis for the ideal generated by `F` using Buchberger's algorithm.
/// `F` is the initial set of generator polynomials.
pub fn buchberger<F, V, T>(
    initial_basis: Vec<SparsePolynomial<F, V, T>>,
) -> Vec<SparsePolynomial<F, V, T>>
where
    F: Field,
    V: Var,
    T: Monomial<V>,
{
    if initial_basis.is_empty() {
        return vec![];
    }

    // G starts as a mutable copy of the input, removing zero polynomials
    let mut g: Vec<SparsePolynomial<F, V, T>> = initial_basis.into_iter().filter(|p| !p.is_zero()).collect();

    // Initialize the set of critical pairs (indices into G)
    let mut pairs: VecDeque<(usize, usize)> = VecDeque::new();
    for i in 0..g.len() {
        for j in (i + 1)..g.len() {
            pairs.push_back((i, j));
        }
    }

    while let Some((i, j)) = pairs.pop_front() {
        // Ensure indices are still valid (G might grow)
        if i >= g.len() || j >= g.len() {
            continue; // Should not happen if pairs are added correctly, but safeguard
        }

        let g_i = &g[i];
        let g_j = &g[j];

        debug!("Processing pair ({}, {})", i, j); // Debug output

        // Compute S-polynomial
        let s_poly = g_i.s_poly(g_j);

        if s_poly.is_zero() {
            debug!("  S(G[{}], G[{}]) = 0", i, j);
            continue; // S-polynomial reduced to zero immediately
        }

        // Reduce the S-polynomial with respect to the current basis G
        let s_reduced = reduce(s_poly, &g);

        // If the reduced S-polynomial is not zero, add it to the basis
        if !s_reduced.is_zero() {
            debug!("  S(G[{}], G[{}]) reduces to non-zero polynomial.", i, j);
            // Add the new polynomial h to G
            g.push(s_reduced);
            let k = g.len() - 1; // Index of the newly added polynomial

            // Add new critical pairs involving the new polynomial h (index k)
            // with all existing polynomials in G (indices 0 to k-1)
            for l in 0..k {
                 // TODO: Add Buchberger's criteria checks here later for optimization
                 // if !skip_pair(l, k, &G) {
                    pairs.push_back((l, k));
                 // }
            }
        } else {
             debug!("  S(G[{}], G[{}]) reduces to 0", i, j);
        }
    }

    g // Return the computed Gröbner basis (not necessarily minimal/reduced yet)
}

/// Reduces a computed Gröbner basis `G` to a minimal, reduced Gröbner basis.
/// 1. Makes all polynomials monic.
/// 2. Removes redundant polynomials (whose LT is divisible by another's LT).
/// 3. Reduces each polynomial against the others.
pub fn reduce_groebner_basis<F, V, T>(
    mut g: Vec<SparsePolynomial<F, V, T>>,
) -> Vec<SparsePolynomial<F, V, T>>
where
    F: Field,
    V: Var,
    T: Monomial<V>,
{
    // --- Step 1: Make polynomials monic & initial cleanup ---
    let mut g_monic: Vec<SparsePolynomial<F, V, T>> = Vec::new();
    for p in g.into_iter() {
        if p.is_zero() { continue; } // Remove zero polynomials

        if let Some((lc, _)) = p.leading_term() {
            let lc_inv = lc.inverse().expect("Leading coefficient must be invertible in a Field for non-zero poly");

            // Multiply the entire polynomial by lc_inv
            let mut monic_p = SparsePolynomial::zero(); // Start fresh
            monic_p.num_vars = p.num_vars;
            for (term, coeff) in p.terms {
                monic_p.terms.insert(&term, &(coeff * lc_inv.clone()));
            }

            // Ensure it's still not zero after making monic (unlikely but possible with weird fields)
            if !monic_p.is_zero() {
                g_monic.push(monic_p);
            }
        }
        // else: p was zero, already skipped
    }
    g = g_monic; // Replace G with the monic version

    // Sort by leading term order (important for the next step)
    // This assumes the Ord trait on Monomial defines the term order used.
    g.sort_unstable_by(|p1, p2| {
        let lt1 = p1.leading_term().map(|(_, t)| t);
        let lt2 = p2.leading_term().map(|(_, t)| t);
        lt1.cmp(&lt2) // Compare leading terms
    });


    // --- Step 2: Remove polynomials whose leading term is divisible by another's LT ---
    // This step creates a "minimal" basis (but not yet "reduced")
    let mut g_minimal: Vec<SparsePolynomial<F, V, T>> = Vec::new();
    let mut discarded = vec![false; g.len()];

    for i in 0..g.len() {
        if discarded[i] { continue; }
        let lt_i = g[i].leading_term().unwrap().1; // Safe unwrap: non-zero polys

        for j in (i + 1)..g.len() {
            if discarded[j] { continue; }
            let lt_j = g[j].leading_term().unwrap().1;

            // If LT(j) is_divided LT(i), mark j for removal (since G is sorted by LT)
            // Note: If LT(i) == LT(j), this should theoretically not happen if basis elements are distinct
            // and monic, but we handle it by discarding j.
            if lt_j.is_divided(&lt_i) {
                discarded[j] = true;
            }
            // We don't need to check if LT(i) is_divided LT(j) because G is sorted by LT.
        }
    }

    // Collect non-discarded polynomials
    for i in 0..g.len() {
        if !discarded[i] {
            g_minimal.push(g[i].clone()); // Clone necessary as we modify below
        }
    }
    g = g_minimal; // Update G

    // --- Step 3: Inter-reduce the basis (Full Reduction) ---
    // For each g in G, reduce it by G \ {g}.
    let mut g_reduced: Vec<SparsePolynomial<F, V, T>> = Vec::with_capacity(g.len());
    for i in 0..g.len() {
        let current_g = g[i].clone();

        // Create basis for reduction: G excluding current_g
        let mut reduction_basis: Vec<SparsePolynomial<F, V, T>> = Vec::new();
        for j in 0..g.len() {
            if i != j {
                reduction_basis.push(g[j].clone());
            }
        }

        // Reduce current_g by the rest of the basis
        let reduced_g = reduce(current_g, &reduction_basis);

        // Add the fully reduced polynomial (it should still be monic and non-zero
        // unless the basis was {c} -> {1} and reduction makes it 0, which we filter)
        if !reduced_g.is_zero() {
             g_reduced.push(reduced_g);
        }
    }

    // Final sort (optional, but good practice)
    g_reduced.sort_unstable_by(|p1, p2| {
        let lt1 = p1.leading_term().map(|(_, t)| t);
        let lt2 = p2.leading_term().map(|(_, t)| t);
        lt1.cmp(&lt2)
    });


    g_reduced
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

// --- Example Usage ---
// To make this example runnable, we need a concrete Term implementation
// that satisfies the trait bounds and uses [(usize, usize)] internally
// for lexicographic ordering.
#[cfg(test)]
mod groebner_test {
    use ark_bls12_381::Fr as Fp; // Using a prime field
        use super::*;
        use ark_ff::One;
        use share::assert_deq;
    // For testing we have concrete variables and monomial terms
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
    pub struct PVar {
        pub index: usize,
        pub principal: Principal,
    }

    impl PVar {
        pub fn new(index: usize, principal: Principal) -> Self {
            PVar { index, principal }
        }

        pub fn any(index: usize) -> Self {
            PVar::new(index, Principal::Any)
        }

        pub fn prover(index: usize) -> Self {
            PVar::new(index, Principal::Prover)
        }

        pub fn verifier(index: usize) -> Self {
            PVar::new(index, Principal::Verifier)
        }
    }

    impl fmt::Display for PVar {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "#{}", self.index)
        }
    }
    #[derive(Clone, PartialEq, Eq, PartialOrd, Debug)]
    pub struct LexDegTerm {
        pub vars: Ctx<PVar, usize>, // (var index, power)
    }

    impl LexDegTerm {
        pub fn new(term: Ctx<PVar, usize>) -> Self {
            LexDegTerm { vars: term }
        }

    }

    /// Multiplies two terms. (var, power) pairs are combined by adding powers
    /// for common variables.
    impl MulAssign for LexDegTerm {
        fn mul_assign(&mut self, other: Self) {
            for (var, power) in other.vars.iter() {
                *self.vars.entry(*var).or_insert(0) += power;
            }
        }
    }

    impl Mul for LexDegTerm {
        type Output = Self;

        fn mul(self, other: Self) -> Self {
            let mut result = self.clone();
            result *= other;
            result
        }
    }

    impl<'a> Mul for &'a LexDegTerm {
        type Output = LexDegTerm;

        fn mul(self, other: &'a LexDegTerm) -> LexDegTerm {
            self.clone() * other.clone()
        }
    }

    impl fmt::Display for LexDegTerm {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            if self.is_constant() {
                write!(f, "1")
            } else {
                let mut terms: Vec<String> = Vec::new();
                for (var, power) in self.vars.iter() {
                    if *power > 0 {
                        terms.push(format!("{}^{}", var, power));
                    }
                }
                write!(f, "{}", terms.join(" * "))
            }
        }
    }

    impl Div for LexDegTerm {
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

    impl<'a> Div for &'a LexDegTerm {
        type Output = Option<LexDegTerm>;

        fn div(self, other: &'a LexDegTerm) -> Option<LexDegTerm> {
            self.clone() / other.clone()
        }
    }

    impl From<Vec<(PVar, usize)>> for LexDegTerm {
        fn from(vars: Vec<(PVar, usize)>) -> Self {
            LexDegTerm::new(vars.into_iter().collect())
        }
    }

    impl Monomial<PVar> for LexDegTerm {
        fn vars(&self) -> Vec<PVar> {
            self.vars.iter().map(|(v, _)| v.clone()).collect()
        }
        fn powers(&self) -> Vec<usize> {
            self.vars.iter().map(|(_, p)| *p).collect()
        }
        fn is_constant(&self) -> bool {
            self.vars.iter().next().is_none() // Empty vec means the term is 1 (constant)
        }

        fn evaluate<F: Field>(&self, p: &Ctx<PVar, F>) -> F {
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
            let mut lcm_powers: Vec<(PVar, usize)> = self.vars.iter().map(|(v, p)| (v.clone(), *p)).collect();
            for (var, power2) in other.vars.iter() {
                match lcm_powers.iter_mut().find(|(v, _)| v == var) {
                    Some((_, power1)) => *power1 = (*power1).max(*power2),
                    None => lcm_powers.push((var.clone(), *power2)),
                }
            }
            Self::new(lcm_powers.into_iter().collect())
        }
        // Ignore principals, we only care about the powers for comparison
        fn grevlex(&self, other: &Self) -> Ordering {
            match other.degree().cmp(&self.degree()) {
                Ordering::Equal => {},
                order => return order,
            };

            // Compare powers in reverse lexicographic order
            for ((v1, p1), (v2, p2)) in self.vars.iter().zip(other.vars.iter()).rev() {
                match (v1.cmp(v2), p1.cmp(p2)) {
                    (Ordering::Equal, Ordering::Equal) => continue,
                    (order, Ordering::Equal) => return order,
                    (_, order) => return order,
                }
            }
            Ordering::Equal
        }
    }

    /// Define elimination order comparison. First, we compare principals such that if any variable has
    /// Principal::Any > Principal::Verifier and Principal::Any > Principal::Prover, then the same is true for LexDegTerm.
    /// If the principals are equal, then perform a grevlex comparison on the powers of the variables (graded, reverse lexicographic order).
    impl Ord for LexDegTerm {
        fn cmp(&self, other: &Self) -> Ordering {
            let any_self = LexDegTerm {
                vars: self.vars.iter()
                    .filter(|(var, _)| var.principal == Principal::Any)
                    .map(|(var, power)| (var.clone(), *power))
                    .collect::<Ctx<PVar, usize>>()
            };

            let any_other = LexDegTerm {
                vars: other.vars.iter()
                    .filter(|(var, _)| var.principal == Principal::Any)
                    .map(|(var, power)| (var.clone(), *power))
                    .collect::<Ctx<PVar, usize>>()
            };

            // Compare the Principal::Any variables first using grevlex
            match any_self.grevlex(&any_other) {
                Ordering::Equal => {},
                order => return order,
            };

            // If they are equal, compare the remaining variables
            let other_self = LexDegTerm {
                vars: self.vars.iter()
                    .filter(|(var, _)| var.principal != Principal::Any)
                    .map(|(var, power)| (var.clone(), *power))
                    .collect::<Ctx<PVar, usize>>()
            };
            let other_other = LexDegTerm {
                vars: other.vars.iter()
                    .filter(|(var, _)| var.principal != Principal::Any)
                    .map(|(var, power)| (var.clone(), *power))
                    .collect::<Ctx<PVar, usize>>()
            };

            // If they are equal, compare the remaining variables
            other_self.grevlex(&other_other)
        }
    }

    #[test]
    fn test_term_ops() {
        let x = PVar::any(0);
        let y = PVar::any(1);
        let z = PVar::any(2);

        let t1 = LexDegTerm::from(vec![(x, 2), (y, 3)]); // x^2 y^3 (vars 0, 1)
        let t2 = LexDegTerm::from(vec![(x, 1), (y, 2)]); // x y^2
        let t3 = LexDegTerm::from(vec![(z, 1)]); // z

        // term_mult
        let t1_t2_mult = &t1 * &t2; // x^3 y^5
        assert_deq!(t1_t2_mult, LexDegTerm::from(vec![(x, 3), (y, 5)]));

        let t1_t3_mult = &t1 * &t3; // x^2 y^3 z
        assert_deq!(t1_t3_mult, LexDegTerm::from(vec![(x, 2), (y, 3), (z, 1)]));

        // term_is_divided
        assert!(t1.is_divided(&t2));
        assert!(!t2.is_divided(&t1));
        assert!(!t1.is_divided(&t3));

        // term_div
        let t1_div_t2 = (&t1 / &t2).unwrap(); // x y
        assert_deq!(t1_div_t2, LexDegTerm::from(vec![(x, 1), (y, 1)]));
        assert!((&t2 / &t1).is_none());

        // lcm_terms
        let lcm_t1_t2 = t1.lcm(&t2); // x^2 y^3
        assert_deq!(lcm_t1_t2, t1);

        let t4 = LexDegTerm::from(vec![(x, 3), (y, 1)]); // x^3 y
        let lcm_t1_t4 = t1.lcm(&t4); // x^3 y^3
        assert_deq!(lcm_t1_t4, LexDegTerm::from(vec![(x, 3), (y, 3)]));
    }

    #[test]
    fn test_s_polynomial() {
        let x = PVar::any(0);
        let y = PVar::any(1);

        let num_vars = 2; // x, y (indices 0, 1)
        let f: SparsePolynomial<_, _, LexDegTerm> = SparsePolynomial::new(num_vars, vec![
            (Fp::one(), vec![(x, 2)]), // x^2
            (-Fp::one(), vec![(y, 1)]), // -y
        ]); // x^2 - y

        let g = SparsePolynomial::new(num_vars, vec![
            (Fp::one(), vec![(x, 1), (y, 1)]), // xy
            (Fp::one(), vec![]), // +1
        ]); // xy + 1

        // LT(f) = x^2, LT(g) = xy
        // lcm(LT(f), LT(g)) = x^2 y
        // multiplier_f = (x^2 y / x^2) * (1/-1) = y
        // multiplier_g = (x^2 y / xy) * (1/1) = x
        // S(f, g) = y * (x^2 - y) - x * (xy + 1)
        //         = x^2 y - y^2 - x^2 y - x
        //         = -y^2 - x
        // Leading term (lexicographic, y < x): -x

        let s = f.s_poly(&g);

        let expected_s = SparsePolynomial::new(num_vars, vec![
            (-Fp::one(), vec![(x, 1)]), // -x
            (-Fp::one(), vec![(y, 2)]), // -y^2
        ]);

        assert_deq!(s, expected_s);
    }

    // A simple test case for F4 based on a known example (e.g., generators of the twisted cubic)
    #[test]
    fn test_linear() {
        let a = PVar::verifier(0);
        let b = PVar::verifier(1);
        let s1 = PVar::prover(2);
        let s2 = PVar::prover(3);
        let r = PVar::any(4);

        // Ideal
        let num_vars = 5;
        // s1 + r - a
        let f1: SparsePolynomial<_, _, LexDegTerm> = SparsePolynomial::new(num_vars, vec![
            (-Fp::one(), vec![(a, 1)]), // -a
            (Fp::one(), vec![(s1, 1)]), // s1
            (Fp::one(), vec![(r, 1)]),  // r
        ]);

        // s2 + r - b
        let f2 = SparsePolynomial::new(num_vars, vec![
            (-Fp::one(), vec![(b, 1)]), // -b
            (Fp::one(), vec![(s2, 1)]), // s2
            (Fp::one(), vec![(r, 1)]), // r
        ]);

        let initial_basis = vec![f1, f2];
        let groebner_basis = buchberger(initial_basis.clone());

        println!("Ideal:");
        for p in &initial_basis {
            println!("{}", p);
        }

        println!("Computed Gröbner Basis:");
        for p in &groebner_basis {
            println!("{}", p);
        }
    }
}
