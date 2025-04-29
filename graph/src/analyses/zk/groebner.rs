use ark_ff::Field;
use crate::principal::Principal;
use crate::Ref;
use core::cmp::Ordering;
use core::ops::{Add, Neg, Sub, Mul, Div, AddAssign, MulAssign, DivAssign, SubAssign};
use share::{Ctx, Set, Pretty, BoxAllocator, DocAllocator, DocBuilder};
use ark_ff::{One, Zero};
use ark_ec::AdditiveGroup;
use std::collections::VecDeque;
use std::fmt::Debug;
use std::ops::Index;
use std::fmt;

use crate::zk::sparsepoly::{Var, Monomial, LexDegTerm, SparsePolynomial};
use log::debug;

/// A struct representing a Gröbner basis.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GroebnerBasis<F: Field, V: Var, T: Monomial<V>> {
    pub basis: Vec<SparsePolynomial<F, V, T>>,
    pub num_vars: usize,
}

impl<F: Field, V: Var, T: Monomial<V>> Index<usize> for GroebnerBasis<F, V, T> {
    type Output = SparsePolynomial<F, V, T>;

    fn index(&self, index: usize) -> &Self::Output {
        &self.basis[index]
    }
}

impl<F: Field, V: Var, T: Monomial<V>> IntoIterator for GroebnerBasis<F, V, T> {
    type Item = SparsePolynomial<F, V, T>;
    type IntoIter = std::vec::IntoIter<SparsePolynomial<F, V, T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.basis.into_iter()
    }
}

impl<F: Field, V: Var, T: Monomial<V>> From<Vec<SparsePolynomial<F, V, T>>> for GroebnerBasis<F, V, T> {
    fn from(basis: Vec<SparsePolynomial<F, V, T>>) -> Self {
        let num_vars = basis.iter().map(|p| p.num_vars).max().unwrap_or(0);
        let mut basis = basis;
        basis.iter_mut().for_each(|p| p.num_vars = num_vars);
        Self { basis, num_vars }
    }
}

impl<F: Field, V: Var, T: Monomial<V>> GroebnerBasis<F, V, T> {
    pub fn new(num_vars: usize, basis: Vec<SparsePolynomial<F, V, T>>) -> Self {
        let mut basis = basis;
        basis.iter_mut().for_each(|p| p.num_vars = num_vars);
        Self { basis, num_vars }
    }

    pub fn empty(num_vars: usize) -> Self {
        Self {
            basis: Vec::new(),
            num_vars,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.basis.is_empty()
    }

    pub fn len(&self) -> usize {
        self.basis.len()
    }

    pub fn iter(&self) -> impl Iterator<Item = &SparsePolynomial<F, V, T>> {
        self.basis.iter()
    }

    pub fn push(&mut self, poly: SparsePolynomial<F, V, T>) {
        self.basis.push(poly);
    }
    /// Reduces polynomial `p` with respect to the basis `G`.
    /// Returns the remainder `r` such that `p = sum(q_i * g_i) + r`, and no term in `r`
    /// is divisible by the leading term of any `g_i` in `G`.
    /// Assumes `G` does not contain the zero polynomial.
    pub fn reduce(&self, mut p: SparsePolynomial<F, V, T>) -> SparsePolynomial<F, V, T> {
        let mut remainder = SparsePolynomial::zero();
        remainder.num_vars = self.num_vars;

        // While p is not zero
        while let Some((p_lc, p_lt)) = p.leading_term() {
            let mut division_occurred = false;
            for g in self.basis.iter() {
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
    pub fn buchberger(self) -> Self {
        if self.basis.is_empty() {
            return self;
        }

        // G starts as a mutable copy of the input, removing zero polynomials
        let mut g: Self =
            Self::new(self.num_vars, self.basis.into_iter().filter(|p| !p.is_zero()).collect());

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
            let s_reduced = g.reduce(s_poly);

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

        // Return the computed Gröbner basis (not necessarily minimal/reduced yet)
        g
    }

    /// Reduces a computed Gröbner basis `G` to a minimal, reduced Gröbner basis.
    /// 1. Makes all polynomials monic.
    /// 2. Removes redundant polynomials (whose LT is divisible by another's LT).
    /// 3. Reduces each polynomial against the others.
    pub fn reduce_groebner_basis(&mut self) {
        // --- Step 0: Calculate the number of variables ---
        let num_vars = self.num_vars;

        // --- Step 1: Make polynomials monic & initial cleanup ---
        let mut g_monic = GroebnerBasis::empty(num_vars);
        for p in self.iter() {
            if p.is_zero() { continue; } // Remove zero polynomials

            if let Some((lc, _)) = p.leading_term() {
                let lc_inv = lc.inverse().expect("Leading coefficient must be invertible in a Field for non-zero poly");

                // Multiply the entire polynomial by lc_inv
                let mut monic_p = SparsePolynomial::zero(); // Start fresh
                monic_p.num_vars = num_vars;
                for (term, coeff) in p.terms.iter() {
                    monic_p.terms.insert(term, &(coeff * &lc_inv.clone()));
                }

                // Ensure it's still not zero after making monic (unlikely but possible with weird fields)
                if !monic_p.is_zero() {
                    g_monic.push(monic_p);
                }
            }
            // else: p was zero, already skipped
        }
        *self = g_monic; // Replace G with the monic version

        // Sort by leading term order (important for the next step)
        // This assumes the Ord trait on Monomial defines the term order used.
        self.basis.sort_unstable_by(|p1, p2| {
            let lt1 = p1.leading_term().map(|(_, t)| t);
            let lt2 = p2.leading_term().map(|(_, t)| t);
            lt1.cmp(&lt2) // Compare leading terms
        });


        // --- Step 2: Remove polynomials whose leading term is divisible by another's LT ---
        // This step creates a "minimal" basis (but not yet "reduced")
        let mut g_minimal = GroebnerBasis::empty(num_vars);
        let mut discarded = vec![false; self.len()];

        for i in 0..self.len() {
            if discarded[i] { continue; }
            let lt_i = self[i].leading_term().unwrap().1; // Safe unwrap: non-zero polys

            for j in (i + 1)..self.len() {
                if discarded[j] { continue; }
                let lt_j = self[j].leading_term().unwrap().1;

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
        for i in 0..self.len() {
            if !discarded[i] {
                g_minimal.push(self[i].clone()); // Clone necessary as we modify below
            }
        }
        *self = g_minimal; // Update G

        // --- Step 3: Inter-reduce the basis (Full Reduction) ---
        // For each g in G, reduce it by G \ {g}.
        let mut g_reduced = GroebnerBasis::new(num_vars, Vec::with_capacity(self.len()));
        for i in 0..self.len() {
            let current_g = self[i].clone();

            // Create basis for reduction: G excluding current_g
            let mut reduction_basis = GroebnerBasis::empty(num_vars);
            for j in 0..self.len() {
                if i != j {
                    reduction_basis.push(self[j].clone());
                }
            }

            // Reduce current_g by the rest of the basis
            let reduced_g = reduction_basis.reduce(current_g);

            // Add the fully reduced polynomial (it should still be monic and non-zero
            // unless the basis was {c} -> {1} and reduction makes it 0, which we filter)
            if !reduced_g.is_zero() {
                 g_reduced.push(reduced_g);
            }
        }

        // Final sort (optional, but good practice)
        g_reduced.basis.sort_unstable_by(|p1, p2| {
            let lt1 = p1.leading_term().map(|(_, t)| t);
            let lt2 = p2.leading_term().map(|(_, t)| t);
            lt1.cmp(&lt2)
        });

        *self = g_reduced;
    }

    pub fn buchberger_and_reduce(self) -> Self {
        let mut g = self.buchberger();
        g.reduce_groebner_basis();
        g
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
    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
    pub struct PVar {
        pub index: String,
        pub elim: bool
    }

    impl PVar {
        pub fn new(index: String, elim: bool) -> Self {
            PVar { index, elim }
        }

        pub fn elim<'a>(index: &'a str) -> Self {
            PVar::new(index.to_string(), true)
        }

        pub fn noelim<'a>(index: &'a str) -> Self {
            PVar::new(index.to_string(), false)
        }
    }

    impl fmt::Display for PVar {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self.index)
        }
    }

    impl Var for PVar {
        fn eliminate(&self) -> bool {
            self.elim
        }
    }

    #[test]
    fn test_term_ops() {
        let x = PVar::elim("x");
        let y = PVar::elim("y");
        let z = PVar::elim("z");

        let t1 = LexDegTerm::from(vec![(&x, 2), (&y, 3)]); // x^2 y^3 (vars 0, 1)
        let t2 = LexDegTerm::from(vec![(&x, 1), (&y, 2)]); // x y^2
        let t3 = LexDegTerm::from(vec![(&z, 1)]); // z

        // term_mult
        let t1_t2_mult = &t1 * &t2; // x^3 y^5
        assert_deq!(t1_t2_mult, LexDegTerm::from(vec![(&x, 3), (&y, 5)]));

        let t1_t3_mult = &t1 * &t3; // x^2 y^3 z
        assert_deq!(t1_t3_mult, LexDegTerm::from(vec![(&x, 2), (&y, 3), (&z, 1)]));

        // term_is_divided
        assert!(t1.is_divided(&t2));
        assert!(!t2.is_divided(&t1));
        assert!(!t1.is_divided(&t3));

        // term_div
        let t1_div_t2 = (&t1 / &t2).unwrap(); // x y
        assert_deq!(t1_div_t2, LexDegTerm::from(vec![(&x, 1), (&y, 1)]));
        assert!((&t2 / &t1).is_none());

        // lcm_terms
        let lcm_t1_t2 = t1.lcm(&t2); // x^2 y^3
        assert_deq!(lcm_t1_t2, t1);

        let t4 = LexDegTerm::from(vec![(&x, 3), (&y, 1)]); // x^3 y
        let lcm_t1_t4 = t1.lcm(&t4); // x^3 y^3
        assert_deq!(lcm_t1_t4, LexDegTerm::from(vec![(&x, 3), (&y, 3)]));
    }

    #[test]
    fn test_s_polynomial() {
        let x = PVar::elim("x");
        let y = PVar::elim("y");

        let f: SparsePolynomial<_, _, LexDegTerm<PVar>> = SparsePolynomial::from(vec![
            (Fp::one(), vec![(&x, 2)]), // x^2
            (-Fp::one(), vec![(&y, 1)]), // -y
        ]); // x^2 - y

        let g = SparsePolynomial::from(vec![
            (Fp::one(), vec![(&x, 1), (&y, 1)]), // xy
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

        let expected_s = SparsePolynomial::from(vec![
            (-Fp::one(), vec![(&x, 1)]), // -x
            (-Fp::one(), vec![(&y, 2)]), // -y^2
        ]);

        assert_deq!(s, expected_s);
    }

    #[test]
    fn test_grevlex_ordering() {
        let x1 = PVar::elim("x1");
        let x2 = PVar::elim("x2");
        let x3 = PVar::elim("x3");

        let f1 = LexDegTerm::from(vec![(&x1, 2)]); // x1^2
        let f2 = LexDegTerm::from(vec![(&x1, 1), (&x2, 1)]); // x1 x2
        let f4 = LexDegTerm::from(vec![(&x2, 2)]); // x2^2
        let f3 = LexDegTerm::from(vec![(&x1, 1), (&x3, 1)]); // x1 x3
        let f5 = LexDegTerm::from(vec![(&x2, 1), (&x3, 1)]); // x2 x3
        let f6 = LexDegTerm::from(vec![(&x3, 2)]); // x3^2
        let f7 = LexDegTerm::new(Ctx::new()); // 1

        // Test with a random permutation
        let mut terms = vec![&f3, &f4, &f1, &f5, &f6, &f2, &f7]
            .into_iter()
            .map(|t| t.clone())
            .collect::<Vec<_>>();

        terms.sort_unstable_by(|a, b| a.cmp(b));
        assert_eq!(terms, vec![f1, f2, f3, f4, f5, f6, f7]);
    }

    // A simple test case for a linear system, this should work as Gaussian elimination
    #[test]
    fn test_linear() {
        let a = PVar::noelim("a");
        let b = PVar::noelim("b");
        let s1 = PVar::noelim("s1");
        let s2 = PVar::noelim("s2");
        let r = PVar::elim("r");
        let num_vars = 5;

        // s1 + r - a
        let f1: SparsePolynomial<_, _, LexDegTerm<PVar>> = SparsePolynomial::from(vec![
            (-Fp::one(), vec![(&a, 1)]), // -a
            (Fp::one(), vec![(&s1, 1)]), // s1
            (Fp::one(), vec![(&r, 1)]),  // r
        ]);

        // s2 + r - b
        let f2 = SparsePolynomial::from(vec![
            (-Fp::one(), vec![(&b, 1)]), // -b
            (Fp::one(), vec![(&s2, 1)]), // s2
            (Fp::one(), vec![(&r, 1)]), // r
        ]);

        let initial_basis = GroebnerBasis::new(num_vars, vec![f1, f2]);
        println!("Ideal:");
        for p in initial_basis.iter() {
            println!("{}", p);
        }

        let groebner_basis = initial_basis.buchberger();
        println!("Computed Gröbner Basis:");
        for p in groebner_basis.iter() {
            println!("{}", p);
        }
    }

    // A simple test case from the Maplesoft docs for Groebner LexDeg bases
    #[test]
    fn test_maple() {
        let t = PVar::elim("t");
        let x = PVar::noelim("x");
        let y = PVar::noelim("y");
        let num_vars = 3;

        // Ideal
        let f1: SparsePolynomial<_, _, LexDegTerm<PVar>> = SparsePolynomial::from(vec![
            (Fp::one(), vec![(&t, 2), (&y,1)]), // t^2 y
            (-Fp::one().double(), vec![(&t,1)]), // -2t
            (Fp::one(), vec![(&y,1)]),      // +y
        ]);

        let f2 = SparsePolynomial::from(vec![
            (Fp::one(), vec![(&t, 2), (&x, 1)]), // t^2 x
            (Fp::one(), vec![(&t, 2)]), // t^2
            (Fp::one(), vec![(&x, 1)]), // x
            (-Fp::one(), vec![]),      // -1
        ]);

        let mut terms: Vec<LexDegTerm<PVar>> = f1.terms.keys().into_iter()
            .chain(f2.terms.keys().into_iter())
            .collect();

        terms.sort_unstable_by(|a, b| a.cmp(b));

        let initial_basis = GroebnerBasis::new(num_vars, vec![f1, f2]);
        let groebner_basis = initial_basis.buchberger_and_reduce();

        // The correct result should be:
        // t*x + t - y
        // t*y + x - 1
        // x^2 + y^2 - 1
        let g1 = SparsePolynomial::from(vec![
            (Fp::one(), vec![(&t, 1), (&x, 1)]), // tx
            (Fp::one(), vec![(&t, 1)]), // t
            (-Fp::one(), vec![(&y, 1)]), // -y
        ]);

        let g2 = SparsePolynomial::from(vec![
            (Fp::one(), vec![(&t, 1), (&y, 1)]), // ty
            (Fp::one(), vec![(&x, 1)]), // x
            (-Fp::one(), vec![]),      // -1
        ]);

        let g3 = SparsePolynomial::from(vec![
            (Fp::one(), vec![(&x, 2)]), // x^2
            (Fp::one(), vec![(&y, 2)]), // y^2
            (-Fp::one(), vec![]),      // -1
        ]);

        assert_eq!(groebner_basis, GroebnerBasis::new(num_vars, vec![g1, g2, g3]));
    }
}
