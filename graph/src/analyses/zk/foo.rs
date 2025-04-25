use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashSet};
use std::cmp::Ordering;
use std::fmt::Debug;

// Assume these traits and structs are defined elsewhere and are in scope:
// Field: A trait representing a field (supports +, -, *, /, inverse, is_zero, is_one)
// Term: A trait representing a monomial term (supports multiplication, division, lcm, degree, comparison/Ord, vars)
// SparsePolynomial: A struct representing a polynomial with non-zero terms

// Placeholder definitions for traits/structs assumed from your code structure:
// You would replace these with your actual implementations.
pub trait Field:
    Sized
    + Copy
    + std::ops::Add<Output = Self>
    + std::ops::Sub<Output = Self>
    + std::ops::Mul<Output = Self>
    + std::ops::Div<Output = Self>
    + std::ops::Neg<Output = Self>
    + PartialEq
    + Eq
    + From<u64>
    + Debug
{
    fn zero() -> Self;
    fn one() -> Self;
    fn inverse(&self) -> Option<Self>;
    fn is_zero(&self) -> bool { *self == Self::zero() }
    fn is_one(&self) -> bool { *self == Self::one() }
}

pub trait Term:
    Sized
    + Clone
    + PartialEq
    + Eq
    + Ord
    + std::hash::Hash
    + std::ops::Mul<Output = Self> // For term * term
    + std::ops::Div<Output = Option<Self>> // For term / term (returns Option as division may not be possible)
    + Debug
    + Default // Assuming a default term (e.g., 1 or identity)
    + Send + Sync // Required by your f4 function bounds
{
    // Should return the degree of the term
    fn degree(&self) -> usize;
    // Should return variable indices present in the term
    fn vars(&self) -> Vec<usize>;
}


#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SparsePolynomial<F: Field, T: Term> {
    pub num_vars: usize, // The number of variables this polynomial is over
    // Store terms as (coefficient, term), sorted by monomial order (descending)
    pub terms: Vec<(F, T)>,
}

impl<F: Field, T: Term + Ord> SparsePolynomial<F, T> {
     pub fn is_zero(&self) -> bool { self.terms.is_empty() }
     // Need a way to normalize/simplify the polynomial, e.g., combining like terms and removing zero coefficients.
     // This is crucial for correctness but omitted in your provided snippet.
     // For this example, we assume polynomials passed around are relatively clean.
     // A proper implementation would simplify polynomials after arithmetic operations.
}

// Assume these helper functions exist and are in scope:
fn leading_term<F: Field, T: Term + Ord>(poly: &SparsePolynomial<F, T>) -> (F, T) {
    // Should return the coefficient and term of the leading term.
    // Assumes terms are sorted descending.
    poly.terms.first().cloned().unwrap_or_else(|| (F::zero(), T::default()))
}

fn term_divides<T: Term>(t1: &T, t2: &T) -> bool {
    // Should check if term t2 divides term t1
    t1.clone() / t2.clone()).is_some()
}

fn term_div<T: Term>(t1: &T, t2: &T) -> Option<T> {
     // Should return t1 / t2 if t2 divides t1
     t1.clone() / t2.clone()
}

fn lcm_terms<T: Term>(t1: &T, t2: &T) -> T {
    // Should return the least common multiple of t1 and t2
    // Implementation depends on how Term stores variables and exponents.
    // Placeholder: assuming a function that computes LCM.
    // Example logic for Term = Vec<usize> (exponents for each variable):
    // lcm_terms([e1, e2], [f1, f2]) = [max(e1, f1), max(e2, f2)]
    unimplemented!("lcm_terms not implemented")
}

fn s_polynomial<F: Field, T: Term + Ord>(f: &SparsePolynomial<F, T>, g: &SparsePolynomial<F, T>) -> SparsePolynomial<F, T> {
    // Computes the S-polynomial of f and g.
    // This involves lcm(LT(f), LT(g)) and multiplying/subtracting.
    // Implementation omitted for brevity but assumed to exist.
    unimplemented!("s_polynomial not implemented")
}

fn polynomial_mul_by_term_and_scalar<F: Field, T: Term>(
    poly: &SparsePolynomial<F, T>,
    scalar: F,
    term: &T,
) -> SparsePolynomial<F, T> {
    // Multiplies a polynomial by a scalar and a term.
    // (scalar * term) * poly
    // Implementation omitted for brevity but assumed to exist.
     let new_terms = poly.terms.iter()
         .map(|(coeff, t)| (*coeff * scalar, t.clone() * term.clone()))
         .collect();
    // Note: A proper implementation should simplify/combine like terms here or afterwards.
    SparsePolynomial {
        num_vars: poly.num_vars, // Simple copy, may need update if term has new vars
        terms: new_terms,
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
    // Consider storing num_vars here if needed frequently
    num_vars: usize,
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
    /// Returns: F4Matrix instance
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

        // Track the maximum number of variables encountered
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
            for (coeff, term) in poly.terms.iter() { // Assumes terms_iter() exists (using terms directly)
                 if coeff.is_zero() { continue; } // Skip zero terms within a polynomial
                 if let Some(data) = all_monomials.get_mut(&term) {
                      data.present = true;
                 } else {
                      all_monomials.insert(term.clone(), MonomialInfo { present: true, column: 0 });
                 }
                max_vars = max_vars.max(term.vars().into_iter().max().map_or(0, |v| v + 1));
            }
        }

        // Also incorporate variables from the basis, just in case
        for poly in basis {
             max_vars = max_vars.max(poly.num_vars);
             for (_, term) in poly.terms.iter() {
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
            for (coeff, monom) in current_poly.terms.iter() { // Assumes terms_iter() exists (using terms directly)
                if coeff.is_zero() { continue; } // Skip zero terms
                // Mark this monomial as present in the matrix
                if let Some(data) = all_monomials.get_mut(&monom) {
                    data.present = true;
                } else {
                    all_monomials.insert(monom.clone(), MonomialInfo { present: true, column: 0 });
                }
                 max_vars = max_vars.max(monom.vars().into_iter().max().map_or(0, |v| v + 1));


                // --- Chase Term Logic ---
                // Only chase this term if it's NOT one of the original leading terms.
                // Leading terms are kept as pivots. Non-leading terms need reduction.
                if initial_leading_terms.contains(&monom) {
                     continue; // This term is an initial leading term, don't chase it
                }

                // Find a basis polynomial whose LT divides 'monom'.
                // Use the reference's heuristic: pick the one with the smallest number of terms.
                let mut best_basis_info: Option<(usize, &SparsePolynomial<F, T>)> = None;

                for (k, basis_poly) in basis.iter().enumerate() {
                    if basis_poly.is_zero() { continue; }
                    let lt_basis = leading_term(basis_poly).1; // Only need the term here

                    if term_divides(&monom, &lt_basis) {
                        // Found a potential reducer. Check if it's the "best" one.
                        if best_basis_info.is_none() || basis_poly.terms.len() < best_basis_info.unwrap().1.terms.len() {
                            best_basis_info = Some((k, basis_poly));
                        }
                    }
                }

                // If a suitable reducer was found
                if let Some((_k, basis_poly)) = best_basis_info {
                     let lt_basis = leading_term(basis_poly).1;
                     // Calculate the multiplier term: monom / lt_basis
                     // term_div should succeed because term_divides was true
                     let multiplier_term = term_div(&monom, &lt_basis).expect("Term division failed after check");

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


                     // Add this new polynomial (the multiple) to the list of polynomials to process and add to matrix
                     // Check if this exact polynomial is already in selected_polys to avoid duplicates?
                     // The reference's use of `simplify` might naturally handle redundancy better.
                     // For this adaptation, we'll just add it. Redundancy is typically handled
                     // by Gaussian elimination zeroing out dependent rows.
                     new_polys.push(basis_poly_multiple);
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

        // Sort monomials according to the term ordering (ascending)
        present_monomials.sort(); // BTreeSet/BTreeMap naturally keeps keys sorted, but collecting into vec needs sort

        // Assign column indices to the sorted present monomials
        let mut column_terms: Vec<T> = Vec::with_capacity(present_monomials.len());
        let mut term_to_col_map: BTreeMap<T, usize> = BTreeMap::new();

        for (col_idx, monom) in present_monomials.into_iter().enumerate() {
             term_to_col_map.insert(monom.clone(), col_idx);
             column_terms.push(monom);
        }

        // Build the sparse matrix rows
        let mut sparse_matrix_rows: Vec<Vec<(F, usize)>> = Vec::with_capacity(selected_polys.len());

        for poly in selected_polys {
            let mut row: Vec<(F, usize)> = Vec::new(); // Use new() and reserve capacity
             row.reserve(poly.terms.len());
            for (coeff, term) in &poly.terms {
                 if coeff.is_zero() { continue; } // Don't add zero entries to sparse row
                // Find the column index for this term
                if let Some(&col_idx) = term_to_col_map.get(term) {
                    row.push((*coeff, col_idx));
                } else {
                    eprintln!("Error: Term {:?} not found in column map during matrix construction! This should not happen.", term);
                }
            }
            // Sort terms within the row by column index - CRUCIAL for sparse Gaussian elimination
            row.sort_by_key(|(_, col_idx)| *col_idx);
            sparse_matrix_rows.push(row);
        }

        // Return the F4Matrix struct
        F4Matrix {
            sparse_matrix_rows,
            column_terms,
            num_vars: max_vars, // Store num_vars
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
        let mut rows = self.sparse_matrix_rows; // Take ownership of the rows

        let num_rows = rows.len();
        let num_cols = self.ncols();

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

// --- Pair Management (using a BinaryHeap for sugar strategy) ---
// ... (Your PairInfo and PairSetManager code remains the same) ...

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
    fn add_new_pairs<F: Field, T: Term + Ord>(&mut self, new_poly_idx: usize, basis: &[SparsePolynomial<F, T>]) {
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
    T: Term + Ord + Clone + Debug + Send + Sync + Default, // Term needs Clone, Debug, Send, Sync, Default
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
        let mut initial_matrix_polys = vec![s_poly.clone()]; // Start with the S-polynomial
        // Add the basis polynomials whose leading term divides the S-polynomial leading term
        // The F4 paper mentions adding polynomials whose LT divides any term in the S-poly or chased terms.
        // The `build` function implements the chasing, so we just need to provide the initial S-poly.
        // The `build` function will pull in necessary basis polynomials by chasing terms.

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
             if !lt_h_prime.0.is_one() && !lt_h_prime.0.is_zero() { // Add check for zero leading coeff
                 let inv_lc = lt_h_prime.0.inverse().expect("LC should be non-zero");
                 // Assuming polynomial_mul_by_term_and_scalar can handle scalar multiplication by using a default term (1)
                   // A dedicated `polynomial_mul_by_scalar` function would be cleaner.
                 h_prime = polynomial_mul_by_term_and_scalar(&h_prime, inv_lc, &T::default());
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
