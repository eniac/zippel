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
    // Assume the first term is the leading term in the sorted order
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

/// Structure to hold data about each unique monomial in the matrix
#[derive(Debug, Clone)]
struct MonomialInfo {
    present: bool, // Is this monomial present in the current matrix build?
    column: usize, // The assigned column index in the matrix
}

// --- Matrix Reduction (Core of F4) ---
/// Represents the matrix used in F4 reduction.
struct F4Matrix<F: Field, T: Term> {
    sparse_matrix_rows: Vec<Vec<(F, usize)>>,
    column_terms: Vec<T>, // Sorted unique terms across all polynomials in the matrix
    num_vars: usize, // Number of variables in the polynomials
}


impl<F: Field, T: Term + Ord> F4Matrix<F, T> {
    /// Builds the data for an F4 matrix using the "chase terms" strategy
    /// adapted from the Faugere F4 paper's symbolic preprocessing phase.
    ///
    /// This function collects the polynomials that will form the rows
    /// and identifies/sorts all monomials that will form the columns.
    ///
    /// It starts with `initial_matrix_polys` (e.g., S-poly and initial reducers)
    /// and chases non-leading terms, adding necessary basis multiples.
    ///
    /// Returns: (sparse_matrix_rows, column_terms, row_origin_info)
    pub fn build(
        initial_matrix_polys: Vec<SparsePolynomial<F, T>>, // Start with these polys
        basis: &[SparsePolynomial<F, T>], // The full current basis
    ) -> Self {
        // Data structure to track all relevant monomials and their state
        let mut all_monomials: BTreeMap<T, MonomialInfo> = BTreeMap::new();

        // Set of polynomials currently selected to form matrix rows.
        // Initially populated with `initial_matrix_polys`.
        // New polynomials (basis multiples) are appended to this list during chasing.
        let mut selected_polys: Vec<SparsePolynomial<F, T>> = initial_matrix_polys;

        // Maximum variables
        let mut max_vars = 0;

        // Track the initial leading terms. We only chase terms that are *not*
        // one of these initial leading terms.
        let mut initial_leading_terms: BTreeSet<T> = BTreeSet::new();

        // Populate initial monomials and mark leading terms
        for poly in &selected_polys {
            if poly.is_zero() { continue; } // Skip zero polynomials
            let lt = leading_term(poly).1;
            initial_leading_terms.insert(lt.clone());
            max_vars = max_vars.max(poly.num_vars);

            // Mark the leading term as present and add to all_monomials if new
            if let Some(data) = all_monomials.get_mut(&lt) {
                 data.present = true;
            } else {
                 // Column index is a placeholder for now, assigned later
                 all_monomials.insert(lt.clone(), MonomialInfo { present: true, column: 0 });
            }

             // Add all terms of initial polynomials to all_monomials as present
             // This ensures all terms of starting polynomials become columns
            for (coef, term) in poly.terms.iter() { // Assumes terms_iter() exists
                if let Some(data) = all_monomials.get_mut(term) {
                     data.present = true;
                } else {
                    all_monomials.insert(term.clone(), MonomialInfo { present: true, column: 0 });
                };
                max_vars = max_vars.max(term.vars().into_iter().max().map_or(0, |v| v + 1));
            }
        }

        // --- Symbolic Preprocessing / Term Chasing ---
        // This loop structure is key from the reference: iterate over `selected_polys`
        // and append new polynomials found during the chase.
        let mut i = 0; // Index of the polynomial currently being processed
        while i < selected_polys.len() {
            let current_poly = &selected_polys[i];

            let mut new_polys: Vec<SparsePolynomial<F, T>> = vec![];

            // Iterate over *all* terms of the current polynomial
            for (coef, monom) in current_poly.terms.iter() { // Assumes terms_iter() exists
                // Mark this monomial as present in the matrix
                if let Some(data) = all_monomials.get_mut(monom) {
                    data.present = true;
                } else {
                    all_monomials.insert(monom.clone(), MonomialInfo { present: true, column: 0 });
                }
                max_vars = max_vars.max(monom.vars().into_iter().max().map_or(0, |v| v + 1));

                // --- Chase Term Logic ---
                // Only chase this term if it's NOT one of the original leading terms.
                // Leading terms are kept as pivots. Non-leading terms need reduction.
                if initial_leading_terms.contains(monom) {
                     continue; // This term is an initial leading term, don't chase it
                }

                // Find a basis polynomial whose LT divides 'monom'.
                // Use the reference's heuristic: pick the one with the smallest number of terms.
                let mut best_basis_info: Option<(usize, &SparsePolynomial<F, T>)> = None;

                for (k, basis_poly) in basis.iter().enumerate() {
                    if basis_poly.is_zero() { continue; }
                    let lt_basis = leading_term(basis_poly).1; // Only need the term here

                    if term_divides(monom, &lt_basis) {
                        // Found a potential reducer. Check if it's the "best" one.
                        if best_basis_info.is_none() || basis_poly.terms.len() < best_basis_info.unwrap().1.terms.len() {
                            best_basis_info = Some((k, basis_poly));
                        }
                    }
                }

                // If a suitable reducer was found
                if let Some((k, basis_poly)) = best_basis_info {
                     let lt_basis = leading_term(basis_poly).1;
                     // Calculate the multiplier term: monom / lt_basis
                     // term_div should succeed because term_divides was true
                     let multiplier_term = term_div(monom, &lt_basis).expect("Term division failed after check");

                     // Create the multiple: multiplier_term * basis_poly
                     // TODO: simplify here, or compute
                     // a pre-reduced form of the multiple. We are
                     // doing direct multiplication for simplicity.
                     let basis_poly_multiple = polynomial_mul_by_term_and_scalar(
                         basis_poly,
                         F::one(), // Coefficients handled in the matrix
                         &multiplier_term,
                     );
                     max_vars = max_vars.max(basis_poly_multiple.num_vars);

                     if !selected_polys.contains(&basis_poly_multiple) {
                         // Add this new polynomial (the multiple) to the list of polynomials to process and add to matrix
                         // Check if this exact polynomial is already in selected_polys to avoid duplicates?
                         // The reference's use of `simplify` might naturally handle redundancy better.
                         // For this adaptation, we'll just add it. Redundancy is typically handled
                         // by Gaussian elimination zeroing out dependent rows.
                         new_polys.push(basis_poly_multiple);
                     }
                }
            }

            // Append newly generated polynomials to the list being iterated
            selected_polys.append(&mut new_polys);


            // Move to the next polynomial in the potentially expanded list
            i += 1;

            // --- Add Safeguards Here If Needed (Similar to previous version) ---
            // Check total number of polynomials, total terms, max exponents
            // If limits hit, set incomplete flag and break outer while loop
            // e.g., if selected_polys.len() > MAX_POLY_LIMIT { ... break; }
            // e.g., if all_monomials.len() > MAX_TERM_LIMIT { ... break; }
            // e.g., if any term in all_monomials exceeds MAX_EXPONENT_LIMIT { ... break; }
        }
        // --- End Symbolic Preprocessing ---


        // --- Construct Sparse Matrix Data ---

        // Collect all monomials marked as present, sort them, and assign column indices
        let mut present_monomials: Vec<T> = all_monomials.iter()
            .filter(|(_, data)| data.present)
            .map(|(monomial, _)| monomial.clone())
            .collect();

        // Sort monomials according to the term ordering
        present_monomials.sort(); // BTreeSet/BTreeMap naturally keeps keys sorted, but collecting into vec needs sort

        // Assign column indices to the sorted present monomials
        let mut column_terms: Vec<T> = Vec::with_capacity(present_monomials.len());
        let mut term_to_col_map: BTreeMap<T, usize> = BTreeMap::new();

        for (col_idx, monom) in present_monomials.into_iter().enumerate() {
             // Update the column index in the main map (if needed later, maybe remove this step)
             // Or just use the separate term_to_col_map
             term_to_col_map.insert(monom.clone(), col_idx);
             column_terms.push(monom);
        }

        // Build the sparse matrix rows
        let mut sparse_matrix_rows: Vec<Vec<(F, usize)>> = Vec::with_capacity(selected_polys.len());

        for poly in selected_polys {
            let mut row: Vec<(F, usize)> = Vec::with_capacity(poly.terms.len());
            for (coeff, term) in &poly.terms {
                // Find the column index for this term
                if let Some(&col_idx) = term_to_col_map.get(term) {
                    row.push((*coeff, col_idx));
                } else {
                    // This should not happen if all terms in selected_polys were
                    // correctly marked as present and included in column_terms.
                    // It indicates a logic error in term collection/column assignment.
                    eprintln!("Error: Term {:?} not found in column map during matrix construction!", term);
                }
            }
            // Sort terms within the row by column index if needed for the echelonize function
            // row.sort_by_key(|(_, col_idx)| *col_idx); // Gaussian elimination often assumes this
            sparse_matrix_rows.push(row);
        }

        // Return the F4Matrix struct
        F4Matrix {
            sparse_matrix_rows,
            column_terms,
            num_vars: max_vars
        }
    }

    pub fn nrows(&self) -> usize {
        self.sparse_matrix_rows.len()
    }

    pub fn ncols(&self) -> usize {
        self.column_terms.len()
    }

    /// Performs Gaussian elimination on two sparse rows (vectors) and subtracts
    /// a scalar multiple of `row_pivot_scaled` from `row_target`.
    /// Assumes both input rows are sorted by column index.
    /// Returns the resulting sparse row, sorted by column index.
    /// Computes: `row_target - factor * row_pivot_scaled`
    fn sparse_row_subtract(
        row_target: &[(F, usize)],
        row_pivot_scaled: &[(F, usize)], // This row is assumed to have 1 at its pivot column after scaling
        factor: F, // The coefficient in row_target at the pivot column
    ) -> Vec<(F, usize)> {
        let mut result_row = Vec::new();
        result_row.reserve(row_target.len() + row_pivot_scaled.len()); // Reserve potential capacity

        let mut i = 0; // Pointer for row_target
        let mut j = 0; // Pointer for row_pivot_scaled

        while i < row_target.len() || j < row_pivot_scaled.len() {
            match (row_target.get(i), row_pivot_scaled.get(j)) {
                (Some((coeff_t, col_t)), Some((coeff_p_s, col_p_s))) => {
                    if col_t == col_p_s {
                        // Same column, perform subtraction: coeff_t - factor * coeff_p_s
                        let new_coeff = *coeff_t - factor * *coeff_p_s;
                        if !new_coeff.is_zero() {
                            result_row.push((new_coeff, *col_t));
                        }
                        i += 1;
                        j += 1;
                    } else if col_t < col_p_s {
                        // Entry only in target row, keep it
                        if !coeff_t.is_zero() { // Should already be non-zero, but good practice
                             result_row.push((*coeff_t, *col_t));
                        }
                        i += 1;
                    } else { // col_p_s < col_t
                        // Entry only in scaled pivot row, subtract its scaled value from zero
                        let new_coeff = F::zero() - factor * *coeff_p_s;
                         if !new_coeff.is_zero() {
                            result_row.push((new_coeff, *col_p_s));
                         }
                        j += 1;
                    }
                }
                (Some((coeff_t, col_t)), None) => {
                    // Remaining entries in target row
                    if !coeff_t.is_zero() {
                        result_row.push((*coeff_t, *col_t));
                    }
                    i += 1;
                }
                (None, Some((coeff_p_s, col_p_s))) => {
                    // Remaining entries in scaled pivot row, subtract its scaled value from zero
                     let new_coeff = F::zero() - factor * *coeff_p_s;
                     if !new_coeff.is_zero() {
                        result_row.push((new_coeff, *col_p_s));
                     }
                    j += 1;
                }
                (None, None) => break, // Both rows exhausted
            }
        }

        // The result_row is built in column order due to the merge logic, so it's sorted.
        result_row
    }

    /// Performs Gaussian elimination to bring the matrix to Row Echelon Form.
    /// Operates directly on the sparse matrix representation.
    /// Returns the non-zero rows as SparsePolynomials.
    fn reduce(mut self) -> Vec<SparsePolynomial<F, T>> {
        let num_cols = self.ncols();
        let num_rows = self.nrows();

        // Ownership transfer
        let mut rows = self.sparse_matrix_rows; // Take ownership of the rows

        if num_rows == 0 || num_cols == 0 {
            return vec![];
        }

        // Ensure rows are sorted by column index if not guaranteed by build
        // (The build function now explicitly sorts them, but keeping this for safety)
        for row in &mut rows {
             row.sort_by_key(|(_, col_idx)| *col_idx);
        }

        let mut pivot_row_idx = 0;
        let mut current_col = 0;

        // Iterate through columns to find pivots
        while pivot_row_idx < num_rows && current_col < num_cols {

            // Find a pivot: find the first row at or below pivot_row_idx with a non-zero entry in current_col
            let mut pivot_found_at_row: Option<usize> = None;
            let mut pivot_coeff: Option<F> = None;

            for r in pivot_row_idx..num_rows {
                // Search for the entry with column index `current_col` in row `r`
                // Since rows are sorted by col_idx, we can efficiently search.
                // Using a simple linear find for clarity, but binary_search_by_key could be faster.
                if let Some(entry) = rows[r].iter().find(|(_, col)| *col == current_col) {
                     if !entry.0.is_zero() {
                        pivot_found_at_row = Some(r);
                        pivot_coeff = Some(entry.0);
                        break; // Found a pivot
                    }
                }
            }

            if let Some(i) = pivot_found_at_row {
                // Found a pivot in row 'i' at column 'current_col'
                let pivot_value = pivot_coeff.expect("Pivot coefficient should be found if row is found");


                // Swap row `i` with `pivot_row_idx`
                rows.swap(pivot_row_idx, i);

                // Get a mutable reference to the pivot row (now at pivot_row_idx)
                let pivot_row = &mut rows[pivot_row_idx];

                // Make the pivot entry 1 by dividing the pivot row by the pivot value
                let inv_pivot = pivot_value.inverse().expect("Pivot should be non-zero");
                for (coeff, _) in pivot_row.iter_mut() {
                    *coeff = *coeff * inv_pivot;
                }
                // The entry at current_col in pivot_row should now be (F::one(), current_col)


                // Eliminate entries in other rows in the current column
                for i in 0..num_rows {
                    if i != pivot_row_idx {
                        // Find the factor for this row at the current_col
                        let factor = rows[i].iter()
                            .find(|(_, col)| *col == current_col)
                            .map(|(coeff, _)| *coeff)
                            .unwrap_or_else(F::zero); // Factor is 0 if no entry in this column

                        if !factor.is_zero() {
                            // Perform sparse row subtraction: rows[i] = rows[i] - factor * rows[pivot_row_idx]

                            // Get a reference to the scaled pivot row
                            let pivot_row_scaled_ref = &rows[pivot_row_idx];

                                // Use a temporary ownership transfer to avoid mutable borrow issues
                                // Or, more simply, clone the target row since sparse_row_subtract takes references.
                                let target_row_copy = rows[i].clone();

                            let new_target_row = Self::sparse_row_subtract(&target_row_copy, pivot_row_scaled_ref, factor);

                            // Replace the target row
                            rows[i] = new_target_row;
                        }
                    }
                }

                // Move to the next pivot row position and the next column
                pivot_row_idx += 1;
                current_col += 1; // Move to the next column to look for the next pivot

            } else {
                // No pivot found in this column at or below the current pivot row index,
                // move to the next column to search for a pivot.
                current_col += 1;
            }
        }

        // Convert non-zero rows back to polynomials
        let mut reduced_polynomials: Vec<SparsePolynomial<F, T>> = Vec::new();
        for row in rows.into_iter() {
             let mut terms: Vec<(F, T)> = Vec::new();
             terms.reserve(row.len());
             for (coeff, col_idx) in row {
                 if !coeff.is_zero() {
                     // Get the corresponding term for this column
                     // column_terms is sorted ascending by Term's Ord.
                     let term = self.column_terms[col_idx].clone();
                     terms.push((coeff, term));
                 }
             }
             // `terms` is currently sorted by column index, which corresponds to ascending
             // monomial order because `column_terms` is sorted ascendingly.
             // SparsePolynomial usually expects terms in descending monomial order.
             terms.reverse();


             let poly = SparsePolynomial {
                 num_vars: self.num_vars, // Use the stored num_vars
                 terms, // Pass the terms (now in descending order)
             };

            if !poly.is_zero() {
                 reduced_polynomials.push(poly);
            }
        }

        reduced_polynomials
    }
}

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
pub fn f4<F: Field, T: Term>(
    mut initial_basis: Vec<SparsePolynomial<F, T>>,
) -> Vec<SparsePolynomial<F, T>> {
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
        let mut initial_matrix_polys = vec![s_poly.clone()]; // Start with the S-polynomial
        // Add the basis polynomials whose leading term divides the S-polynomial leading term
        for (k, basis_poly) in basis.iter().enumerate() {
            if basis_poly.is_zero() { continue; }
            let lt_basis = leading_term(basis_poly).1.clone();
            if term_divides(&s_poly.terms[0].1, &lt_basis) {
                initial_matrix_polys.push(basis_poly.clone());
            }
        }
        // Build the matrix involving the S-polynomial and selected basis polynomials
        // based on term dependencies.
        let f4_matrix = F4Matrix::build(initial_matrix_polys, &basis);

        println!(" Matrix built with {} rows and {} columns.", f4_matrix.nrows(), f4_matrix.ncols());
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
    fn test_linear() {
        // Ideal
        let num_vars = 5;
        // s1 + r - a
        let f1 = poly::<Fp, LexTerm>(num_vars, vec![
            (-Fp::one(), vec![(1, 1)]), // -a
            (Fp::one(), vec![(2, 1)]), // s1
            (Fp::one(), vec![(0, 1)]), // -a
        ]);

        // s2 + r - b
        let f2 = poly::<Fp, LexTerm>(num_vars, vec![
            (-Fp::one(), vec![(3, 1)]), // -b
            (Fp::one(), vec![(4, 1)]), // s2
            (Fp::one(), vec![(0, 1)]), // r
        ]);

        let initial_basis = vec![f1, f2];
        let groebner_basis = f4::<Fp, LexTerm>(initial_basis.clone());

        println!("Ideal:");
        for p in &initial_basis {
            println!("{:?}", p);
        }

        println!("Computed Gröbner Basis:");
        for p in &groebner_basis {
            println!("{:?}", p);
        }
    }

}
