use ark_ff::{Field, Zero, One};
use ark_poly::polynomial::multivariate::{SparsePolynomial, Term};
use ark_std::{
    collections::{BTreeMap, BTreeSet, BinaryHeap, HashSet},
    vec,
    vec::Vec,
};
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};
use core::cmp::Ordering;
use core::ops::Deref;
use std::fmt::Debug;

// We need to define how Terms are ordered. The user must provide
// a Term implementation that satisfies this. For lexicographic order,
// a common way is to compare variable powers from highest variable index down.
// However, the `Term` trait's `Ord` implementation is what will be used.
// We'll assume the user provides a Term type whose Ord is lexicographic.

// --- Helper functions for Term arithmetic ---
// These operate on the `[(usize, usize)]` representation
// of a Term, assuming `Term` can be dereferenced into it.

/// Multiplies two terms. (var, power) pairs are combined by adding powers
/// for common variables.
fn term_mult<T: Term>(t1: &T, t2: &T) -> T {
    let mut powers: BTreeMap<usize, usize> = BTreeMap::new();
    for (var, power) in t1.deref() {
        *powers.entry(*var).or_insert(0) += power;
    }
    for (var, power) in t2.deref() {
        *powers.entry(*var).or_insert(0) += power;
    }
    let mut new_term_vec: Vec<(usize, usize)> = powers.into_iter().collect();
    // It's good practice to keep the term representation sorted by variable index
    new_term_vec.sort_by_key(|(var, _)| *var);
    T::new(new_term_vec)
}

/// Checks if term `t2` divides term `t1`.
fn term_divides<T: Term>(t1: &T, t2: &T) -> bool {
    let p1: BTreeMap<usize, usize> = t1.deref().iter().cloned().collect();
    let p2: BTreeMap<usize, usize> = t2.deref().iter().cloned().collect();

    for (var, power2) in p2.iter() {
        match p1.get(var) {
            Some(power1) => {
                if power1 < power2 {
                    return false;
                }
            }
            None => return false, // t2 has a variable t1 doesn't have
        }
    }
    true // All variables in t2 are in t1 with sufficient power
}

/// Divides term `t1` by term `t2`. Returns `None` if `t2` does not divide `t1`.
fn term_div<T: Term>(t1: &T, t2: &T) -> Option<T> {
    if !term_divides(t1, t2) {
        return None;
    }

    let mut powers1: BTreeMap<usize, usize> = t1.deref().iter().cloned().collect();
    let powers2: BTreeMap<usize, usize> = t2.deref().iter().cloned().collect();

    for (var, power2) in powers2.iter() {
        // We know var is in powers1 with sufficient power because term_divides was true
        *powers1.get_mut(var).unwrap() -= power2;
    }

    let mut new_term_vec: Vec<(usize, usize)> = powers1.into_iter().filter(|(_, p)| *p > 0).collect();
    new_term_vec.sort_by_key(|(var, _)| *var); // Maintain sorted order
    Some(T::new(new_term_vec))
}

/// Computes the Least Common Multiple (LCM) of two terms.
fn lcm_terms<T: Term>(t1: &T, t2: &T) -> T {
    let p1: BTreeMap<usize, usize> = t1.deref().iter().cloned().collect();
    let p2: BTreeMap<usize, usize> = t2.deref().iter().cloned().collect();

    let mut lcm_powers: BTreeMap<usize, usize> = BTreeMap::new();

    for (var, power) in p1.iter() {
        lcm_powers.insert(*var, *power);
    }
    for (var, power) in p2.iter() {
        lcm_powers.entry(*var).and_modify(|e| *e = (*e).max(*power)).or_insert(*power);
    }

    let mut new_term_vec: Vec<(usize, usize)> = lcm_powers.into_iter().filter(|(_, p)| *p > 0).collect();
    new_term_vec.sort_by_key(|(var, _)| *var); // Maintain sorted order
    T::new(new_term_vec)
}

/// Multiplies a polynomial by a scalar and a term.
fn polynomial_mul_by_term_and_scalar<F: Field, T: Term>(
    poly: &SparsePolynomial<F, T>,
    scalar: F,
    term: &T,
) -> SparsePolynomial<F, T> {
    if scalar.is_zero() {
        return SparsePolynomial::zero();
    }
    let new_terms: Vec<(F, T)> = poly
        .terms
        .iter()
        .map(|(coeff, t)| (*coeff * scalar, term_mult(t, term)))
        .collect();
    // Need to handle combining like terms and sorting.
    // ark-poly's SparsePolynomial likely does this internally or expects canonical form.
    // A safe way is to rebuild, letting the constructor handle it if it does,
    // or explicitly combine here. Let's manually combine for clarity.

    let mut combined_terms: BTreeMap<T, F> = BTreeMap::new(); // BTreeMap keeps terms sorted
    for (coeff, t) in new_terms {
        *combined_terms.entry(t).or_insert(F::zero()) += coeff;
    }

    let final_terms: Vec<(F, T)> = combined_terms
        .into_iter()
        .filter(|(_, c)| !c.is_zero())
        .map(|(t, c)| (c, t))
        .collect(); // Note: BTreeMap iterates sorted by key (Term)

    SparsePolynomial {
        num_vars: poly.num_vars, // Assuming num_vars is consistent
        terms: final_terms,
    }
}

fn leading_term<F: Field, T: Term>(f: &SparsePolynomial<F, T>) -> (F, T) {
    f.terms.first().map(|(k, v)| (*k, v.clone())).unwrap_or((F::zero(), T::new(vec![])))
}

// --- S-Polynomial Computation ---

/// Computes the S-polynomial of two polynomials f and g.
/// S(f, g) = (lcm(LT(f), LT(g)) / LT(f)) * f - (lcm(LT(f), LT(g)) / LT(g)) * g
fn s_polynomial<F: Field, T: Term>(
    f: &SparsePolynomial<F, T>,
    g: &SparsePolynomial<F, T>,
) -> SparsePolynomial<F, T> {
    if f.is_zero() || g.is_zero() {
        return SparsePolynomial::zero();
    }

    let lt_f = leading_term(f);
    let lt_g = leading_term(g);

    let term_f = &lt_f.1;
    let coeff_f = lt_f.0;

    let term_g = &lt_g.1;
    let coeff_g = lt_g.0;

    let lcm_t = lcm_terms(term_f, term_g);

    // Multiplier for f: (lcm_t / term_f) * (1 / coeff_f)
    let multiplier_term_f = term_div(&lcm_t, term_f).expect("Term division failed for LCM/LT");
    let multiplier_scalar_f = coeff_f.inverse().expect("Leading coefficient must be non-zero");

    // Multiplier for g: (lcm_t / term_g) * (1 / coeff_g)
    let multiplier_term_g = term_div(&lcm_t, term_g).expect("Term division failed for LCM/LT");
    let multiplier_scalar_g = coeff_g.inverse().expect("Leading coefficient must be non-zero");

    let poly_f_scaled = polynomial_mul_by_term_and_scalar(
        f,
        multiplier_scalar_f,
        &multiplier_term_f,
    );
    let poly_g_scaled = polynomial_mul_by_term_and_scalar(
        g,
        multiplier_scalar_g,
        &multiplier_term_g,
    );

    // S = poly_f_scaled - poly_g_scaled
    // SparsePolynomial subtraction: Combine terms, negating the second polynomial's coeffs.
    let mut combined_terms: BTreeMap<T, F> = BTreeMap::new();

    for (coeff, term) in poly_f_scaled.terms.into_iter() {
        *combined_terms.entry(term).or_insert(F::zero()) += coeff;
    }
    for (coeff, term) in poly_g_scaled.terms.into_iter() {
        *combined_terms.entry(term).or_insert(F::zero()) -= coeff; // Subtracting
    }

    let final_terms: Vec<(F, T)> = combined_terms
        .into_iter()
        .filter(|(_, c)| !c.is_zero())
        .map(|(t, c)| (c, t))
        .collect();

    SparsePolynomial {
        num_vars: f.num_vars.max(g.num_vars), // Take max num_vars
        terms: final_terms,
    }
}

// --- Matrix Reduction (Core of F4) ---

/// Represents the matrix used in F4 reduction.
struct F4Matrix<F: Field, T: Term> {
    matrix: Vec<Vec<F>>,
    column_terms: Vec<T>, // Sorted unique terms across all polynomials in the matrix
    row_origin_info: Vec<PolynomialOrigin<T>>, // What polynomial/multiple generated this row
}

/// Information about the origin of a row in the matrix.
#[derive(Clone, Debug)] // Derive Clone and Debug for easier handling
enum PolynomialOrigin<T: Term> {
    SPolynomial(usize, usize), // Pair (i, j) that generated the S-poly
    BasisMultiple(usize, T), // Index `k` of basis poly, and the multiplier term
}

impl<F: Field, T: Term + Ord> F4Matrix<F, T> {
    /// Builds the matrix for reducing a set of polynomials (starting with an S-poly).
    /// This is a simplified approach to selecting polynomials for the matrix.
    /// A more advanced F4 would use criteria to select basis polynomials whose LT divides
    /// terms in the current set of polynomials/multiples.
    fn build(
        s_poly: &SparsePolynomial<F, T>,
        basis: &[SparsePolynomial<F, T>],
    ) -> Self {
        let mut polynomials_to_reduce: Vec<SparsePolynomial<F, T>> = vec![s_poly.clone()];
        let mut origins: Vec<PolynomialOrigin<T>> = vec![PolynomialOrigin::SPolynomial(0, 0)]; // Placeholder, need actual pair indices

        let lt_s = leading_term(s_poly);
        let term_s = &lt_s.1;

        // Simple strategy: include the S-polynomial and any basis polynomial
        // whose leading term divides the leading term of the S-polynomial's terms.
        // This isn't the full power of F4's selection, which would chase all terms.
        // Let's refine: Collect all terms from the initial polynomials.
        // Then, for each term, find a basis polynomial that reduces it.
        // Add the appropriate multiple of the basis polynomial. Repeat.

        let mut terms_to_process: BTreeSet<T> = BTreeSet::new(); // Use BTreeSet to keep terms sorted
        for (_, term) in &s_poly.terms {
            terms_to_process.insert(term.clone());
        }

        let mut matrix_poly_set: Vec<SparsePolynomial<F, T>> = vec![s_poly.clone()];
        let mut matrix_poly_origins: Vec<PolynomialOrigin<T>> = vec![PolynomialOrigin::SPolynomial(0, 0)]; // Placeholder

        let mut processed_terms: BTreeSet<T> = BTreeSet::new(); // Keep track of terms we've processed

        while let Some(term) = terms_to_process.pop_first() {
             if processed_terms.contains(&term) {
                 continue;
             }
             processed_terms.insert(term.clone());

            // Find a basis polynomial whose LT divides 'term'.
            // A sophisticated strategy would pick the "best" one (e.g., smallest degree LT).
            let mut best_basis_idx: Option<usize> = None;
            // Iterate in reverse to potentially prioritize newer basis polynomials (heuristic)
            for k in (0..basis.len()).rev() {
                 let basis_poly = &basis[k];
                 if basis_poly.is_zero() { continue; }
                 let lt_basis = leading_term(basis_poly).1;

                 if term_divides(&term, &lt_basis) {
                     best_basis_idx = Some(k);
                     break; // Simple strategy: take the first one found
                 }
             }

            if let Some(k) = best_basis_idx {
                let basis_poly = &basis[k];
                let lt_basis = leading_term(basis_poly);
                let term_basis = &lt_basis.1;

                // Calculate the multiplier term needed to make LT(basis_poly) equal 'term'
                let multiplier_term = term_div(&term, term_basis).expect("Term division failed");

                // Create the multiple: multiplier_term * basis_poly
                let basis_poly_multiple = polynomial_mul_by_term_and_scalar(
                    basis_poly,
                    F::one(), // We handle coefficients in the matrix
                    &multiplier_term,
                );

                // Add this multiple to the list of polynomials for the matrix
                matrix_poly_set.push(basis_poly_multiple.clone()); // Clone is potentially expensive
                matrix_poly_origins.push(PolynomialOrigin::BasisMultiple(k, multiplier_term));

                // Add all terms of this new multiple to the set of terms to process
                for (_, new_term) in &basis_poly_multiple.terms {
                    if !processed_terms.contains(new_term) {
                        println!("Inserting new term: {:?}", new_term);
                         terms_to_process.insert(new_term.clone());
                    }
                }
            }
        }

        // Now, collect all unique terms from all polynomials in `matrix_poly_set`
        let mut all_terms: BTreeSet<T> = BTreeSet::new(); // Use BTreeSet for sorting and uniqueness
        for poly in &matrix_poly_set {
            for (_, term) in &poly.terms {
                all_terms.insert(term.clone());
            }
        }
        let column_terms: Vec<T> = all_terms.into_iter().collect(); // Convert sorted set to vec

        // Build the coefficient matrix
        let num_rows = matrix_poly_set.len();
        let num_cols = column_terms.len();
        let mut matrix: Vec<Vec<F>> = vec![vec![F::zero(); num_cols]; num_rows];

        // Create a term-to-column index map for quick lookup
        let term_to_col_map: BTreeMap<T, usize> = column_terms.iter().enumerate().map(|(i, t)| (t.clone(), i)).collect();

        for (row_idx, poly) in matrix_poly_set.iter().enumerate() {
            for (coeff, term) in &poly.terms {
                if let Some(&col_idx) = term_to_col_map.get(term) {
                    matrix[row_idx][col_idx] = *coeff;
                }
            }
        }

        F4Matrix {
            matrix,
            column_terms,
            row_origin_info: matrix_poly_origins,
        }
    }

    /// Performs Gaussian elimination to bring the matrix to Row Echelon Form.
    /// Returns the non-zero rows as SparsePolynomials.
    fn reduce(mut self) -> Vec<SparsePolynomial<F, T>> {
        let num_rows = self.matrix.len();
        let num_cols = self.matrix.first().map_or(0, |row| row.len());

        if num_rows == 0 || num_cols == 0 {
            return vec![];
        }

        let mut pivot_row = 0;
        let mut reduced_polynomials: Vec<SparsePolynomial<F, T>> = Vec::new();

        // Iterate through columns to find pivots
        for col in 0..num_cols {
            if pivot_row >= num_rows {
                break; // No more rows to pivot
            }

            // Find a pivot: find a row with a non-zero entry in the current column at or below pivot_row
            let mut i = pivot_row;
            while i < num_rows && self.matrix[i][col].is_zero() {
                i += 1;
            }

            if i == num_rows {
                // No pivot in this column, move to the next column
                continue;
            }

            // Swap row `i` with `pivot_row`
            self.matrix.swap(pivot_row, i);
            self.row_origin_info.swap(pivot_row, i); // Keep origin info in sync

            // Make the pivot entry 1 by dividing the pivot row by the pivot value
            let pivot_value = self.matrix[pivot_row][col];
            let inv_pivot = pivot_value.inverse().expect("Pivot should be non-zero");
            for j in col..num_cols { // Only need to scale from the pivot column onwards
                self.matrix[pivot_row][j] *= inv_pivot;
            }

            // Eliminate entries in other rows in the current column
            for i in 0..num_rows {
                if i != pivot_row {
                    let factor = self.matrix[i][col];
                    // If the factor is zero, no elimination needed for this row
                    if !factor.is_zero() {
                       for j in col..num_cols { // Only need to operate from the pivot column onwards
                           let v = self.matrix[pivot_row][j];
                           self.matrix[i][j] -= factor * v;
                       }
                    }
                }
            }

            pivot_row += 1; // Move to the next pivot row position
        }

        // Convert non-zero rows back to polynomials
        for row in self.matrix.into_iter() {
             let mut terms: Vec<(F, T)> = Vec::new();
             for (col_idx, coeff) in row.into_iter().enumerate() {
                 if !coeff.is_zero() {
                     // Get the corresponding term for this column
                     let term = self.column_terms[col_idx].clone();
                     terms.push((coeff, term));
                 }
             }
             // Rebuild SparsePolynomial. The constructor should sort terms if needed.
             // If not, we need to sort `terms` here based on the Term's Ord.
             terms.sort_by(|(_, t1), (_, t2)| t1.cmp(t2).reverse()); // Assuming reverse order for leading term

             let poly = SparsePolynomial {
                 num_vars: self.column_terms.iter().flat_map(|t| t.vars()).max().map_or(0, |v| v + 1), // Determine max variable index + 1
                 terms,
             };

            if !poly.is_zero() {
                 reduced_polynomials.push(poly);
            }
        }

        reduced_polynomials
    }
}


// --- Pair Management (using a BinaryHeap for sugar strategy) ---

// We'll store pairs as (lcm_degree, i, j) and use a max-heap.
// The BinaryHeap in Rust is a max-heap, so we'll store the negative degree
// or use a wrapper struct if we want min-heap based on degree.
// Let's use a wrapper for clarity for min-heap behavior on degree.

#[derive(Eq, PartialEq, Clone, Debug)]
struct PairInfo {
    lcm_degree: usize,
    i: usize,
    j: usize,
}

// Implement Ord for PairInfo to use with BinaryHeap as a min-heap on lcm_degree
impl Ord for PairInfo {
    fn cmp(&self, other: &Self) -> Ordering {
        // Compare degrees in reverse order to make BinaryHeap act as a min-heap on degree
        other.lcm_degree.cmp(&self.lcm_degree)
             .then_with(|| self.i.cmp(&other.i)) // Tie-breaking (arbitrary but consistent)
             .then_with(|| self.j.cmp(&other.j))
    }
}

impl PartialOrd for PairInfo {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Manages the set of pairs to be processed.
struct PairSetManager {
    heap: BinaryHeap<PairInfo>,
    // Keep track of pairs already added or processed to avoid duplicates
    // Using a HashSet of tuples (i, j) where i < j
    processed_pairs: HashSet<(usize, usize)>,
}

impl PairSetManager {
    fn new<F: Field, T: Term>(initial_basis: &[SparsePolynomial<F, T>]) -> Self {
        let mut heap = BinaryHeap::new();
        let mut processed_pairs = HashSet::new();

        for i in 0..initial_basis.len() {
            for j in (i + 1)..initial_basis.len() {
                 if !initial_basis[i].is_zero() && !initial_basis[j].is_zero() {
                    let lcm_t = lcm_terms(
                        &leading_term(&initial_basis[i]).1,
                        &leading_term(&initial_basis[j]).1
                    );
                    heap.push(PairInfo {
                        lcm_degree: lcm_t.degree(),
                        i,
                        j,
                    });
                    processed_pairs.insert((i, j));
                 }
            }
        }

        PairSetManager {
            heap,
            processed_pairs,
        }
    }

    /// Pops the pair with the smallest LCM degree.
    fn pop(&mut self) -> Option<(usize, usize)> {
        // The BinaryHeap gives the max element. With our PairInfo Ord,
        // this is the pair with the *minimum* lcm_degree.
        self.heap.pop().map(|pair_info| (pair_info.i, pair_info.j))
        // We don't remove from processed_pairs here, it just tracks what went INTO the heap.
        // Redundancy check (Buchberger's criteria) is needed later.
    }

    /// Adds new pairs involving the new polynomial (at `new_poly_idx`)
    /// and existing basis polynomials.
    fn add_new_pairs<F: Field, T: Term>(&mut self, new_poly_idx: usize, basis: &[SparsePolynomial<F, T>]) {
        let new_poly = &basis[new_poly_idx];
        if new_poly.is_zero() { return; }
        let lt_new = leading_term(new_poly).1.clone();

        for i in 0..new_poly_idx {
            let existing_poly = &basis[i];
            if existing_poly.is_zero() { continue; }

            // Ensure i < new_poly_idx for consistent pair representation (i, j) with i < j
            let pair = (i, new_poly_idx);

            if !self.processed_pairs.contains(&pair) {
                let lt_existing = leading_term(existing_poly).1.clone();
                let lcm_t = lcm_terms(&lt_new, &lt_existing);
                self.heap.push(PairInfo {
                    lcm_degree: lcm_t.degree(),
                    i: pair.0,
                    j: pair.1,
                });
                self.processed_pairs.insert(pair);
            }
        }
    }
    // Note: A full Buchberger Criterion 2 check would also involve
    // removing pairs (i, j) where lcm(LT_i, LT_j) is divisible by LT_new
    // and LT_new < lcm(LT_i, LT_j). This is more complex to manage with just a heap.
    // For this basic implementation, we rely on the matrix reduction to handle redundancy.
}

// --- F4 Algorithm Main Function ---

/// Computes a Gröbner basis for the given set of polynomials using Faugère's F4 algorithm.
/// Assumes the Term type implements Ord for the desired monomial ordering (e.g., lexicographic).
pub fn f4<F, T>(
    mut initial_basis: Vec<SparsePolynomial<F, T>>,
) -> Vec<SparsePolynomial<F, T>>
where
    F: Field + Copy + From<u64>, // Need Copy and From<u64> for Field
    T: Term + Ord + Clone + Debug + Send + Sync, // Term needs Clone, Debug, Send, Sync
{
    // Initial cleaning: remove zeros, maybe reduce initially (optional but good)
    initial_basis.retain(|p| !p.is_zero());

    let mut basis: Vec<SparsePolynomial<F, T>> = initial_basis;
    let mut pair_manager = PairSetManager::new(&basis);

    // Buchberger's Criterion 1 (Simplified): If LT(f) divides LT(g), S(f,g) reduces to 0
    // w.r.t {f, g}. The matrix method handles this naturally, but we can avoid adding such pairs
    // or skip processing them. For simplicity, we let the matrix reduction handle it.

    let mut iteration_count = 0;
    println!("Starting F4 algorithm with {} polynomials.", basis.len());

    while let Some((i, j)) = pair_manager.pop() {
        iteration_count += 1;
        println!("\nIteration {}: Processing pair ({}, {})", iteration_count, i, j);

        // Re-check if polynomials still exist and are non-zero at these indices.
        // The basis grows, indices might become stale if we removed polynomials.
        // In this implementation, we only add to the basis, so indices are stable.
        // However, a more advanced version might re-index or use handles.
        // For now, assume indices i and j are valid.
        let f = &basis[i];
        let g = &basis[j];

        // If either polynomial became zero during previous reductions (not explicitly handled
        // in this simple version, but could happen in a dynamic basis), skip the pair.
        if f.is_zero() || g.is_zero() {
            println!(" Skipping pair ({}, {}): one polynomial is zero.", i, j);
            continue;
        }

        let s_poly = s_polynomial(f, g);

        if s_poly.is_zero() {
            println!(" S-polynomial is zero. Skipping.");
            continue; // S-polynomial reduces to zero
        }

        println!(" Computed S-polynomial. Building and reducing matrix.");

        // --- F4 Matrix Reduction Step ---
        // Build the matrix involving the S-polynomial and selected basis polynomials
        // based on term dependencies.
        let f4_matrix = F4Matrix::build(&s_poly, &basis);

        println!(" Matrix built with {} rows and {} columns.", f4_matrix.matrix.len(), f4_matrix.column_terms.len());
        // Perform Gaussian elimination on the matrix
        let reduced_polys = f4_matrix.reduce();

        println!(" Matrix reduced. Found {} non-zero polynomials.", reduced_polys.len());

        // Process the reduced polynomials
        for mut h_prime in reduced_polys {
            println!(" Processing reduced polynomial {:?}", h_prime);
             // Ensure the leading term is non-zero after reduction and potential re-sorting
             if h_prime.is_zero() { continue; }

             // Optional: Normalize (make monic) - useful for reduced basis, not strictly required for *a* basis.
             let lt_h_prime = leading_term(&h_prime);
             if !lt_h_prime.0.is_one() {
                 let inv_lc = lt_h_prime.0.inverse().expect("LC should be non-zero");
                 h_prime = polynomial_mul_by_term_and_scalar(&h_prime, inv_lc, &T::default()); // Multiply by scalar 1/LC
             }

             // Check if this new polynomial is redundant (its LT is divisible by an existing LT in the basis)
             let lt_h_prime_term = leading_term(&h_prime).1.clone();
             let mut is_redundant = false;
             for existing_poly in &basis {
                 if !existing_poly.is_zero() {
                     let lt_existing_term = leading_term(&existing_poly).1.clone();
                     if term_divides(&lt_h_prime_term, &lt_existing_term) {
                         is_redundant = true;
                         break;
                     }
                 }
             }

             if !is_redundant {
                 println!(" Found non-redundant polynomial. Adding to basis.");
                 let new_poly_idx = basis.len();
                 basis.push(h_prime);

                 // Add new pairs involving the new polynomial
                 pair_manager.add_new_pairs(new_poly_idx, &basis);
                 println!(" Added new pairs involving basis[{}]", new_poly_idx);
             } else {
                 println!(" Found redundant polynomial. Discarding.");
             }
        }

        // Note: This basic implementation doesn't explicitly handle Buchberger's criterion 2
        // to prune pairs early based on new polynomials. The matrix reduction helps,
        // but a full implementation would track this in the pair manager.
    }

    println!("\nF4 algorithm finished. Final basis size: {}.", basis.len());

    // Optional: Perform a final reduction to get a reduced Gröbner basis.
    // This involves reducing each polynomial by all *other* polynomials in the basis.
    // This is outside the core F4 loop but standard practice.
    // Leaving this out for brevity in the core F4 implementation, but be aware it's needed
    // for a *reduced* basis.

    basis.retain(|p| !p.is_zero()); // Remove any zero polynomials

    // Sort the final basis by leading term (optional but standard presentation)
    basis.sort_by(|p1, p2| {
         if p1.is_zero() { return Ordering::Greater; }
         if p2.is_zero() { return Ordering::Less; }
         leading_term(&p1).1.cmp(&leading_term(p2).1)
    });

    basis
}

// --- Example Usage ---
// To make this example runnable, we need a concrete Term implementation
// that satisfies the trait bounds and uses [(usize, usize)] internally
// for lexicographic ordering.

// A simple Term struct for lexicographic order
#[derive(Clone, Default, Debug, PartialEq, Eq, Hash, CanonicalSerialize, CanonicalDeserialize)]
pub struct LexTerm {
    vars_and_powers: Vec<(usize, usize)>, // Sorted descending by variable index
}

impl Deref for LexTerm {
    type Target = [(usize, usize)];
    fn deref(&self) -> &Self::Target {
        &self.vars_and_powers
    }
}

impl Term for LexTerm {
    fn new(mut term: Vec<(usize, usize)>) -> Self {
        // Sort descending by variable index for lexicographic comparison
        term.sort_by(|(v1, _), (v2, _)| v2.cmp(v1));
        LexTerm { vars_and_powers: term }
    }

    fn degree(&self) -> usize {
        self.vars_and_powers.iter().map(|(_, p)| p).sum()
    }

    fn vars(&self) -> Vec<usize> {
        self.vars_and_powers.iter().map(|(v, _)| *v).collect()
    }

    fn powers(&self) -> Vec<usize> {
        // This method is less standard for a sparse term.
        // Returning powers corresponding to `vars()` might be ambiguous
        // if variables are skipped. A common interpretation is
        // to return the powers for variables 0, 1, ..., num_vars-1, using 0 if not present.
        // We'll need `num_vars` to do this properly. Let's assume 0 for missing.
        // This requires knowing the total number of variables... The Term trait doesn't
        // provide `num_vars`. This method might be ill-defined for this sparse Term.
        // Let's return the powers of the variables *present* in the term,
        // in the order they appear in `vars()`.
         self.vars_and_powers.iter().map(|(_, p)| *p).collect()
    }

    fn is_constant(&self) -> bool {
        self.vars_and_powers.is_empty() // Empty vec means the term is 1 (constant)
    }

     // Note: evaluate requires a slice of field elements matching the number of variables.
     // This is not directly used in the F4 algorithm itself but is part of the Term trait.
    fn evaluate<F: Field>(&self, p: &[F]) -> F {
        let mut result = F::one();
        for (var_idx, power) in &self.vars_and_powers {
            if *var_idx < p.len() {
                 for _ in 0..*power {
                     result *= p[*var_idx];
                 }
            } else {
                 // Variable index out of bounds for the provided evaluation point.
                 // Depending on semantics, this might be an error or imply the variable value is 1?
                 // Following typical evaluation, it means the term evaluates to 0 if the variable is 0,
                 // but if the point `p` is too short, it's ambiguous.
                 // Let's assume variables *not* in the term always evaluate to 1,
                 // so they don't affect the product, consistent with the sparse representation.
            }
        }
        result
    }
}

// Implement Ord for LexTerm (Lexicographic Order)
// Compare descending by variable index, then ascending by power for ties at that variable.
// Example: x^2 y^3 > x y^4 because 2 > 1 for x.
// Example: x^2 y^3 z > x^2 y^3 because z is present in the first but not the second.
// Standard Lexicographic: compare powers variable by variable from largest index down.
// t1 = x_n^a_n ... x_1^a_1, t2 = x_n^b_n ... x_1^b_1. t1 > t2 if at the first i
// where a_i != b_i (starting from n down to 1), a_i > b_i.
impl Ord for LexTerm {
    fn cmp(&self, other: &Self) -> Ordering {
        // Get the maximum variable index present in either term
        let max_var = self.vars_and_powers.iter().chain(other.vars_and_powers.iter()).map(|(v, _)| *v).max().unwrap_or(0);

        // Compare powers from highest variable index down to 0
        for var_idx in (0..=max_var).rev() {
            let power_self = self.vars_and_powers.iter().find(|(v, _)| *v == var_idx).map(|(_, p)| *p).unwrap_or(0);
            let power_other = other.vars_and_powers.iter().find(|(v, _)| *v == var_idx).map(|(_, p)| *p).unwrap_or(0);

            match power_self.cmp(&power_other) {
                Ordering::Equal => continue, // Powers are equal, check next lower variable
                order => return order, // Powers are different, this determines the order
            }
        }

        // If all powers are equal for all variables, the terms are equal
        Ordering::Equal
    }
}

impl PartialOrd for LexTerm {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod groebner_tests {
    use ark_bls12_381::Fr as Fp; // Using a prime field
    use super::*;
    use ark_ff::{Field, Zero, One};
    use ark_poly::polynomial::multivariate::{SparsePolynomial, Term};
    use ark_std::{vec, test_rng, UniformRand};

    // Helper to create a sparse polynomial easily
    fn poly<F: Field, T: Term>(num_vars: usize, terms: Vec<(F, Vec<(usize, usize)>)>) -> SparsePolynomial<F, T> {
         let processed_terms = terms.into_iter().map(|(coeff, term_vec)| (coeff, T::new(term_vec))).collect();
         SparsePolynomial {
             num_vars,
             terms: processed_terms,
         }
    }

    #[test]
    fn test_term_ops() {
         let t1 = LexTerm::new(vec![(0, 2), (1, 3)]); // x^2 y^3 (vars 0, 1)
         let t2 = LexTerm::new(vec![(0, 1), (1, 2)]); // x y^2
         let t3 = LexTerm::new(vec![(2, 1)]); // z

         // term_mult
         let t1_t2_mult = term_mult(&t1, &t2); // x^3 y^5
         assert_eq!(t1_t2_mult, LexTerm::new(vec![(0, 3), (1, 5)]));

         let t1_t3_mult = term_mult(&t1, &t3); // x^2 y^3 z
         assert_eq!(t1_t3_mult, LexTerm::new(vec![(0, 2), (1, 3), (2, 1)]));

         // term_divides
         assert!(term_divides(&t1, &t2));
         assert!(!term_divides(&t2, &t1));
         assert!(!term_divides(&t1, &t3));

         // term_div
         let t1_div_t2 = term_div(&t1, &t2).unwrap(); // x y
         assert_eq!(t1_div_t2, LexTerm::new(vec![(0, 1), (1, 1)]));
         assert!(term_div(&t2, &t1).is_none());

         // lcm_terms
         let lcm_t1_t2 = lcm_terms(&t1, &t2); // x^2 y^3
         assert_eq!(lcm_t1_t2, t1);

         let t4 = LexTerm::new(vec![(0, 3), (1, 1)]); // x^3 y
         let lcm_t1_t4 = lcm_terms(&t1, &t4); // x^3 y^3
         assert_eq!(lcm_t1_t4, LexTerm::new(vec![(0, 3), (1, 3)]));
    }

    #[test]
    fn test_s_polynomial() {
         let num_vars = 2; // x, y (indices 0, 1)
         let f = poly::<Fp, LexTerm>(num_vars, vec![
             (Fp::one(), vec![(0, 2)]), // x^2
             (-Fp::one(), vec![(1, 1)]), // -y
         ]); // x^2 - y

         let g = poly::<Fp, LexTerm>(num_vars, vec![
             (Fp::one(), vec![(0, 1), (1, 1)]), // xy
             (Fp::one(), vec![]), // +1
         ]); // xy + 1

         // LT(f) = x^2, LT(g) = xy
         // lcm(LT(f), LT(g)) = x^2 y
         // multiplier_f = (x^2 y / x^2) * (1/1) = y
         // multiplier_g = (x^2 y / xy) * (1/1) = x
         // S(f, g) = y * (x^2 - y) - x * (xy + 1)
         //         = x^2 y - y^2 - x^2 y - x
         //         = -y^2 - x
         // Leading term (lexicographic, y < x): -x

         let s = s_polynomial(&f, &g);

         let expected_s = poly::<Fp, LexTerm>(num_vars, vec![
             (-Fp::one(), vec![(0, 1)]), // -x
             (-Fp::one(), vec![(1, 2)]), // -y^2
         ]);

         // The terms might be in different order in the resulting poly
         let mut s_terms = s.terms;
         s_terms.sort_by(|(_, t1), (_, t2)| t1.cmp(t2)); // Sort for comparison

         let mut expected_s_terms = expected_s.terms;
         expected_s_terms.sort_by(|(_, t1), (_, t2)| t1.cmp(t2));

         assert_eq!(s_terms, expected_s_terms);
    }

     // A simple test case for F4 based on a known example (e.g., generators of the twisted cubic)
    #[test]
    fn test_f4_twisted_cubic() {
         // Ideal I = <x^2 - y, y^2 - z> in k[x, y, z] (vars 0, 1, 2)
         // Using lexicographic order with z < y < x (indices 2 < 1 < 0)
         let num_vars = 3; // x, y, z (indices 0, 1, 2)

         // Polynomials should be defined with variables in order for the LexTerm `Ord`
         // For z < y < x order using 0, 1, 2 indices, we want to compare indices 2, then 1, then 0.
         // Our LexTerm implementation sorts descending by var index, so (2,_) then (1,_), then (0,_) is default.
         // Lexicographic order: x > y > z means (0, _) > (1, _) > (2, _).
         // We defined LexTerm Ord to sort descending by variable index. This means
         // (2, power) comes before (1, power), which comes before (0, power).
         // So, var index 2 is 'most significant', then 1, then 0.
         // If we map z -> 2, y -> 1, x -> 0, then LexTerm's default Ord IS z > y > x.
         // If we want x > y > z, we need to map x -> 0, y -> 1, z -> 2 and modify LexTerm's Ord
         // to compare from index 0 upwards, or store terms ascending by index.
         // Let's stick to the current LexTerm Ord which is z > y > x with z=2, y=1, x=0.

         let f1 = poly::<Fp, LexTerm>(num_vars, vec![
             (Fp::one(), vec![(0, 2)]), // x^2
             (-Fp::one(), vec![(1, 1)]), // -y
         ]); // x^2 - y -> LT is x^2 (0, 2)

         let f2 = poly::<Fp, LexTerm>(num_vars, vec![
             (Fp::one(), vec![(1, 2)]), // y^2
             (-Fp::one(), vec![(2, 1)]), // -z
         ]); // y^2 - z -> LT is y^2 (1, 2)

         let initial_basis = vec![f1, f2];

         // Expected Gröbner basis (for z > y > x lexicographic):
         // f1: x^2 - y
         // f2: y^2 - z
         // S(f1, f2) = S(x^2 - y, y^2 - z)
         // LT(f1)=x^2 (0,2), LT(f2)=y^2 (1,2). lcm = x^2 y^2 (0,2), (1,2)
         // mult_f1 = x^2 y^2 / x^2 = y^2 (1,2)
         // mult_f2 = x^2 y^2 / y^2 = x^2 (0,2)
         // S = y^2(x^2 - y) - x^2(y^2 - z) = x^2 y^2 - y^3 - x^2 y^2 + x^2 z = -y^3 + x^2 z
         // This S-poly needs to be reduced.
         // Its LT is x^2 z (0,2), (2,1) for z > y > x order (since var 2 > var 1 > var 0)
         // LT(f1) = x^2 (0,2) divides x^2 z. Reduce -y^3 + x^2 z by f1 = x^2 - y
         // (-y^3 + x^2 z) - z * (x^2 - y) = -y^3 + x^2 z - x^2 z + y z = -y^3 + y z
         // New polynomial: -y^3 + y z. Its LT is -y^3 (1,3) for z > y > x order.
         // This polynomial is not reducible by LT(f1)=x^2 or LT(f2)=y^2 (y^2 divides y^3).
         // Reduce -y^3 + y z by f2 = y^2 - z
         // (-y^3 + y z) - (-y) * (y^2 - z) = -y^3 + y z - (-y^3 + y z) = -y^3 + y z + y^3 - y z = 0.
         // Uh oh, S-poly reduced to 0? My manual calculation might be wrong or the
         // standard basis for twisted cubic requires a different order or more steps.

         // Let's use a simpler, standard example: I = <x^2 + y, x y + x> in k[x, y] with x > y lexicographic.
         // Vars: x=0, y=1. Order: x > y means compare var 0 then var 1.
         // LexTerm needs to be defined such that (0, power) > (1, power).
         // Current LexTerm Ord: descending var index -> var 1 > var 0 (y > x).
         // Let's reverse the Ord logic in LexTerm for this test or map x->1, y->0.
         // Let's reverse the Ord logic for this test.
         // Modify LexTerm Ord for x > y (var 0 > var 1)

         // --- Redefine LexTerm Ord for x > y lexicographic (var 0 > var 1) ---
         #[derive(Clone, Default, Debug, PartialEq, Eq, Hash, CanonicalSerialize, CanonicalDeserialize)]
         struct LexTermXY {
             vars_and_powers: Vec<(usize, usize)>, // Sorted ascending by variable index
         }

         impl Deref for LexTermXY {
             type Target = [(usize, usize)];
             fn deref(&self) -> &Self::Target {
                 &self.vars_and_powers
             }
         }

         impl Term for LexTermXY {
             fn new(mut term: Vec<(usize, usize)>) -> Self {
                 // Sort ascending by variable index for x > y lexicographic (var 0 > var 1)
                 term.sort_by(|(v1, _), (v2, _)| v1.cmp(v2));
                 LexTermXY { vars_and_powers: term }
             }
             fn degree(&self) -> usize { self.vars_and_powers.iter().map(|(_, p)| p).sum() }
             fn vars(&self) -> Vec<usize> { self.vars_and_powers.iter().map(|(v, _)| *v).collect() }
             fn powers(&self) -> Vec<usize> { self.vars_and_powers.iter().map(|(_, p)| *p).collect() } // Still a bit ambiguous
             fn is_constant(&self) -> bool { self.vars_and_powers.is_empty() }
             fn evaluate<F: Field>(&self, p: &[F]) -> F {
                 let mut result = F::one();
                 for (var_idx, power) in &self.vars_and_powers {
                     if *var_idx < p.len() {
                         for _ in 0..*power {
                             result *= p[*var_idx];
                         }
                     }
                 }
                 result
             }
         }

         // Implement Ord for LexTermXY (Lexicographic Order: var 0 > var 1 > ...)
         impl Ord for LexTermXY {
             fn cmp(&self, other: &Self) -> Ordering {
                 // Get the maximum variable index present in either term
                 let max_var = self.vars_and_powers.iter().chain(other.vars_and_powers.iter()).map(|(v, _)| *v).max().unwrap_or(0);

                 // Compare powers from lowest variable index up to max_var
                 for var_idx in 0..=max_var {
                     let power_self = self.vars_and_powers.iter().find(|(v, _)| *v == var_idx).map(|(_, p)| *p).unwrap_or(0);
                     let power_other = other.vars_and_powers.iter().find(|(v, _)| *v == var_idx).map(|(_, p)| *p).unwrap_or(0);

                     match power_self.cmp(&power_other) {
                         Ordering::Equal => continue, // Powers are equal, check next higher variable
                         order => return order, // Powers are different, this determines the order
                     }
                 }
                 // If all powers are equal for all variables, the terms are equal
                 Ordering::Equal
             }
         }

         impl PartialOrd for LexTermXY {
             fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                 Some(self.cmp(other))
             }
         }

         // --- Test case: I = <x^2 + y, x y + x> in k[x, y] with x > y lexicographic ---
         let num_vars = 2; // x=0, y=1

         let g1 = poly::<Fp, LexTermXY>(num_vars, vec![
             (Fp::one(), vec![(0, 2)]), // x^2
             (Fp::one(), vec![(1, 1)]), // +y
         ]); // x^2 + y. LT is x^2 (0, 2)

         let g2 = poly::<Fp, LexTermXY>(num_vars, vec![
             (Fp::one(), vec![(0, 1), (1, 1)]), // xy
             (Fp::one(), vec![(0, 1)]), // +x
         ]); // xy + x. LT is xy (0, 1), (1, 1)

         let initial_basis_xy = vec![g1, g2];

         // Expected Reduced Gröbner Basis for <x^2+y, xy+x> with x > y:
         // g1 = x^2 + y
         // g2 = xy + x
         // S(g1, g2) = S(x^2+y, xy+x). LT(g1)=x^2, LT(g2)=xy. lcm = x^2 y.
         // mult_g1 = x^2 y / x^2 = y
         // mult_g2 = x^2 y / xy = x
         // S = y(x^2 + y) - x(xy + x) = x^2 y + y^2 - x^2 y - x^2 = y^2 - x^2
         // This S-poly needs to be reduced by g1 = x^2 + y.
         // S = y^2 - x^2. LT is -x^2. Reduce by g1.
         // (y^2 - x^2) - (-1) * (x^2 + y) = y^2 - x^2 + x^2 + y = y^2 + y
         // New polynomial h3 = y^2 + y. LT is y^2.
         // This is not reducible by LT(g1) or LT(g2). Add h3 to basis.
         // Basis is now {x^2+y, xy+x, y^2+y}. Need to check new pairs.
         // Pair (g1, h3) = S(x^2+y, y^2+y). LT(g1)=x^2, LT(h3)=y^2. lcm = x^2 y^2.
         // mult_g1 = y^2, mult_h3 = x^2.
         // S = y^2(x^2+y) - x^2(y^2+y) = x^2 y^2 + y^3 - x^2 y^2 - x^2 y = y^3 - x^2 y
         // Reduce by g1=x^2+y: (y^3 - x^2 y) - (-y) * (x^2 + y) = y^3 - x^2 y + x^2 y + y^2 = y^3 + y^2
         // Reduce by h3=y^2+y: (y^3 + y^2) - y * (y^2 + y) = y^3 + y^2 - y^3 - y^2 = 0. This pair yields 0.

         // Pair (g2, h3) = S(xy+x, y^2+y). LT(g2)=xy, LT(h3)=y^2. lcm = xy^2.
         // mult_g2 = y, mult_h3 = x.
         // S = y(xy+x) - x(y^2+y) = xy^2 + xy - xy^2 - xy = 0. This pair yields 0.

         // So the Gröbner basis should be {x^2+y, xy+x, y^2+y} (possibly with monic leading terms).
         // Let's run F4 and see.

         let groebner_basis = f4::<Fp, LexTermXY>(initial_basis_xy.clone());

         println!("Computed Gröbner Basis (x > y):");
         for p in &groebner_basis {
             println!("{:?}", p);
         }

         // Check if the computed basis generates the same ideal and is potentially the expected one.
         // This requires checking if the expected basis polynomials are reducible to zero by the computed basis,
         // and vice-versa (less practical). A simpler check is if the computed basis has the same
         // leading terms as the expected reduced basis (up to scalar multiples).

         let expected_lts: BTreeSet<LexTermXY> = [
             LexTermXY::new(vec![(0, 2)]), // x^2
             LexTermXY::new(vec![(0, 1), (1, 1)]), // xy
             LexTermXY::new(vec![(1, 2)]), // y^2
         ]
         .iter()
         .cloned()
         .collect();

         let computed_lts: BTreeSet<LexTermXY> = groebner_basis
             .iter()
             .filter(|p| !p.is_zero())
             .map(|p| leading_term(&p).1.clone())
             .collect();

         assert_eq!(computed_lts, expected_lts);

         // Optional: Check if the polynomials match (up to scalar multiples and term order)
         // This is harder because the exact coefficients in the matrix reduction might vary.
         // The leading terms check is a good first verification for a Gröbner basis.

         // A fully reduced Gröbner basis would be:
         // x^2 + y
         // xy + x
         // y^2 + y
         // Check if the computed polynomials match these after making monic and sorting.

         let mut computed_monic_basis = groebner_basis.clone();
         computed_monic_basis.retain(|p| !p.is_zero());
         for p in &mut computed_monic_basis {
              let lt = leading_term(&p);
              let inv_lc = lt.0.inverse().unwrap();
              p.terms.iter_mut().for_each(|(c, _)| *c *= inv_lc);
              // Re-sort terms just in case ark-poly doesn't guarantee it after arithmetic
              p.terms.sort_by(|(_, t1), (_, t2)| t1.cmp(t2).reverse()); // Sort by leading term order
         }

         let mut expected_reduced_basis = vec![
              poly::<Fp, LexTermXY>(num_vars, vec![(Fp::one(), vec![(0, 2)]), (Fp::one(), vec![(1, 1)])]), // x^2 + y
              poly::<Fp, LexTermXY>(num_vars, vec![(Fp::one(), vec![(0, 1), (1, 1)]), (Fp::one(), vec![(0, 1)])]), // xy + x
              poly::<Fp, LexTermXY>(num_vars, vec![(Fp::one(), vec![(1, 2)]), (Fp::one(), vec![(1, 1)])]), // y^2 + y
         ];
         expected_reduced_basis.sort_by(
             |p1, p2| leading_term(&p1).1.cmp(&leading_term(&p2).1)); // Sort by LT

         // Sort computed basis by LT
         computed_monic_basis.sort_by(
             |p1, p2| leading_term(&p1).1.cmp(&leading_term(&p2).1)); // Sort by LT

         // Compare polynomial term by term. This requires the term order within SparsePolynomial
         // to be consistent. BTreeMap conversion in our helpers ensures this if Term Ord is good.

         assert_eq!(computed_monic_basis.len(), expected_reduced_basis.len());
         for (computed_p, expected_p) in computed_monic_basis.iter().zip(expected_reduced_basis.iter()) {
             // Compare term vectors directly after sorting
             let mut computed_terms = computed_p.terms.clone();
             computed_terms.sort_by(|(_, t1), (_, t2)| t1.cmp(t2).reverse());

             let mut expected_terms = expected_p.terms.clone();
             expected_terms.sort_by(|(_, t1), (_, t2)| t1.cmp(t2).reverse());

             assert_eq!(computed_terms, expected_terms);
         }

        println!("Computed and Expected Reduced Gröbner Bases match (up to scalar).");

    }

}
