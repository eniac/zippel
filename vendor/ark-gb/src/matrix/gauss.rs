//! Gaussian elimination over a sparse [`super::SparseRow`].
//!
//! Phase L2 surface — pivot strategy is *leading-column ascending*: the
//! row with the smallest non-empty leading column is selected as the
//! next pivot, normalised, and used to eliminate that column from every
//! other row. This ordering matches the F4 convention "monomial order
//! determines column order" so a future F4 caller gets a row-echelon
//! form that respects the chosen monomial order out of the box.

use ark_ff::Field;

use super::sparse::{Matrix, SparseRow};

/// Reduce `rows` to *row-echelon form* in place, returning the rank.
///
/// On exit:
/// * each non-zero row is unit-normalised at its pivot column,
/// * pivot columns are strictly ascending top-to-bottom,
/// * all-zero rows are sorted to the bottom.
///
/// Pivot strategy: at each step, pick the as-yet-unprocessed row with
/// the smallest leading column (ties broken by the original index).
pub fn row_echelon<F: Field>(rows: &mut [SparseRow<F>]) -> usize {
    let mut pivot_row = 0usize;
    let n = rows.len();

    while pivot_row < n {
        // Find the row in [pivot_row, n) with the smallest leading_col.
        let mut best: Option<(usize, usize)> = None;
        for (i, row) in rows.iter().enumerate().skip(pivot_row) {
            if let Some(lc) = row.leading_col() {
                match best {
                    None => best = Some((i, lc)),
                    Some((_, blc)) if lc < blc => best = Some((i, lc)),
                    _ => {}
                }
            }
        }
        let Some((src, pivot_col)) = best else {
            break; // remaining rows are all zero
        };
        rows.swap(pivot_row, src);

        // Normalise the pivot row.
        let pivot_val = rows[pivot_row]
            .as_pairs()
            .first()
            .expect("pivot row is non-zero")
            .0;
        let inv = pivot_val
            .inverse()
            .expect("non-zero field element has inverse");
        rows[pivot_row].scale(&inv);

        // Eliminate `pivot_col` from every other row that has it.
        // We split the vec to borrow `rows[pivot_row]` and the rest
        // disjointly.
        let (head, tail) = rows.split_at_mut(pivot_row + 1);
        let pivot = &head[pivot_row];
        for r in tail {
            let c = r.coeff(pivot_col);
            if !c.is_zero() {
                r.axpy_assign(&c, pivot);
            }
        }

        pivot_row += 1;
    }

    // Move zero rows to the bottom (they should already be there in
    // typical inputs because of the leading-col selection, but a row
    // may become zero mid-reduction — handle that).
    let mut write = 0usize;
    for read in 0..rows.len() {
        if !rows[read].is_zero() {
            if read != write {
                rows.swap(read, write);
            }
            write += 1;
        }
    }
    let rank = write;
    // Drop trailing zero rows? No — caller may rely on length stability.
    // Just leave them at the bottom.
    rank
}

/// Reduce `rows` to *reduced row-echelon form* in place, returning the rank.
///
/// Calls [`row_echelon`] then back-substitutes so each pivot column
/// has a single non-zero entry (the unit pivot).
pub fn rref<F: Field>(rows: &mut [SparseRow<F>]) -> usize {
    let rank = row_echelon(rows);
    if rank < 2 {
        return rank;
    }
    // Back-substitute from the last pivot upward.
    for i in (1..rank).rev() {
        let pivot_col = rows[i].leading_col().expect("row in [0, rank) is non-zero");
        let (head, tail) = rows.split_at_mut(i);
        let pivot = &tail[0];
        for r in head.iter_mut() {
            let c = r.coeff(pivot_col);
            if !c.is_zero() {
                r.axpy_assign(&c, pivot);
            }
        }
    }
    rank
}

/// Rank of the row space spanned by `rows`. Does not mutate the input.
pub fn rank<F: Field>(rows: &[SparseRow<F>]) -> usize {
    let mut clone: Vec<SparseRow<F>> = rows.to_vec();
    row_echelon(&mut clone)
}

// -----------------------------------------------------------------------
// Public adapters on `Matrix<F> = Vec<Vec<(F, usize)>>` (the snark shape)
// -----------------------------------------------------------------------

/// Reduce a snark-shaped [`Matrix`] to row-echelon form, returning the rank.
///
/// Convenience wrapper for callers that don't want to think in
/// [`SparseRow`].
pub fn row_echelon_matrix<F: Field>(matrix: &mut Matrix<F>) -> usize {
    let mut rows: Vec<SparseRow<F>> = matrix.drain(..).map(SparseRow::from).collect();
    let rank = row_echelon(&mut rows);
    matrix.extend(rows.into_iter().map(SparseRow::into_pairs));
    rank
}

/// Reduce a snark-shaped [`Matrix`] to reduced row-echelon form,
/// returning the rank.
pub fn rref_matrix<F: Field>(matrix: &mut Matrix<F>) -> usize {
    let mut rows: Vec<SparseRow<F>> = matrix.drain(..).map(SparseRow::from).collect();
    let rank = rref(&mut rows);
    matrix.extend(rows.into_iter().map(SparseRow::into_pairs));
    rank
}

#[cfg(test)]
mod tests {
    use super::super::sparse::SparseRow;
    use super::*;
    use ark_bls12_381::Fr;
    use ark_ff::{One, UniformRand, Zero};

    fn fr(x: u64) -> Fr {
        Fr::from(x)
    }

    fn rows_from_dense(rows: &[Vec<Fr>]) -> Vec<SparseRow<Fr>> {
        rows.iter().map(|r| SparseRow::from_dense(r)).collect()
    }

    fn rows_to_dense(rows: &[SparseRow<Fr>], cols: usize) -> Vec<Vec<Fr>> {
        rows.iter()
            .map(|r| {
                let mut d = vec![Fr::zero(); cols];
                for &(v, c) in r.as_pairs() {
                    d[c] = v;
                }
                d
            })
            .collect()
    }

    // --- hand-rolled cases ---------------------------------------------------

    #[test]
    fn echelon_of_identity_is_identity() {
        let mut rs = rows_from_dense(&[
            vec![fr(1), fr(0), fr(0)],
            vec![fr(0), fr(1), fr(0)],
            vec![fr(0), fr(0), fr(1)],
        ]);
        let r = row_echelon(&mut rs);
        assert_eq!(r, 3);
        assert_eq!(
            rows_to_dense(&rs, 3),
            vec![
                vec![fr(1), fr(0), fr(0)],
                vec![fr(0), fr(1), fr(0)],
                vec![fr(0), fr(0), fr(1)],
            ]
        );
    }

    #[test]
    fn echelon_swaps_to_get_pivot_order() {
        // Input rows in "wrong" leading-col order; result must be ascending.
        let mut rs = rows_from_dense(&[
            vec![fr(0), fr(0), fr(1)],
            vec![fr(0), fr(2), fr(0)],
            vec![fr(3), fr(0), fr(0)],
        ]);
        let r = row_echelon(&mut rs);
        assert_eq!(r, 3);
        // Unit-normalised, pivots ascending in columns 0, 1, 2.
        assert_eq!(
            rows_to_dense(&rs, 3),
            vec![
                vec![fr(1), fr(0), fr(0)],
                vec![fr(0), fr(1), fr(0)],
                vec![fr(0), fr(0), fr(1)],
            ]
        );
    }

    #[test]
    fn echelon_rank_deficient() {
        // Row 2 = 2 * Row 0, so rank = 2.
        let mut rs = rows_from_dense(&[
            vec![fr(1), fr(2), fr(3)],
            vec![fr(0), fr(1), fr(4)],
            vec![fr(2), fr(4), fr(6)],
        ]);
        let r = row_echelon(&mut rs);
        assert_eq!(r, 2);
        assert!(rs[2].is_zero());
    }

    #[test]
    fn rref_makes_pivot_columns_singletons() {
        // Same rank-2 input; RREF should give I_2 ⊕ extra column.
        let mut rs = rows_from_dense(&[
            vec![fr(1), fr(2), fr(3)],
            vec![fr(0), fr(1), fr(4)],
            vec![fr(2), fr(4), fr(6)],
        ]);
        let r = rref(&mut rs);
        assert_eq!(r, 2);
        // Row 0 should have no entry in pivot column of row 1 (col 1).
        assert_eq!(rs[0].coeff(0), Fr::one());
        assert_eq!(rs[0].coeff(1), Fr::zero());
        assert_eq!(rs[1].coeff(1), Fr::one());
    }

    #[test]
    fn rref_idempotent() {
        let mut rs = rows_from_dense(&[
            vec![fr(2), fr(4), fr(2)],
            vec![fr(1), fr(3), fr(1)],
            vec![fr(0), fr(1), fr(0)],
        ]);
        let r1 = rref(&mut rs);
        let snapshot = rs.clone();
        let r2 = rref(&mut rs);
        assert_eq!(r1, r2);
        assert_eq!(rs, snapshot);
    }

    #[test]
    fn rref_kernel_agreement_zero_input() {
        let mut rs: Vec<SparseRow<Fr>> = vec![SparseRow::new(); 4];
        let r = rref(&mut rs);
        assert_eq!(r, 0);
        assert!(rs.iter().all(|r| r.is_zero()));
    }

    #[test]
    fn rank_does_not_mutate() {
        let rs = rows_from_dense(&[vec![fr(1), fr(2)], vec![fr(2), fr(4)], vec![fr(0), fr(1)]]);
        let snapshot = rs.clone();
        let r = rank(&rs);
        assert_eq!(r, 2);
        assert_eq!(rs, snapshot);
    }

    #[test]
    fn permutation_preserves_rref() {
        let base = rows_from_dense(&[
            vec![fr(1), fr(2), fr(3)],
            vec![fr(0), fr(1), fr(4)],
            vec![fr(0), fr(0), fr(1)],
        ]);
        let mut a = base.clone();
        let mut b: Vec<_> = vec![base[2].clone(), base[0].clone(), base[1].clone()];
        let ra = rref(&mut a);
        let rb = rref(&mut b);
        assert_eq!(ra, rb);
        // Compare as sets of dense rows (zero rows are ignored).
        let mut da = rows_to_dense(&a, 3);
        let mut db = rows_to_dense(&b, 3);
        da.sort();
        db.sort();
        assert_eq!(da, db);
    }

    // --- snark-shape adapters -----------------------------------------------

    #[test]
    fn matrix_adapter_round_trip() {
        let mut m: Matrix<Fr> = vec![
            vec![(fr(2), 0), (fr(4), 1), (fr(2), 2)],
            vec![(fr(1), 0), (fr(3), 1), (fr(1), 2)],
            vec![(fr(1), 1)],
        ];
        let r = rref_matrix(&mut m);
        assert_eq!(r, 2);
        // After rref, every row is a sorted, unit-normalised SparseRow.
        for row in &m {
            // sorted ascending
            assert!(row.windows(2).all(|w| w[0].1 < w[1].1));
            // no zero entries
            assert!(row.iter().all(|&(v, _)| !v.is_zero()));
        }
    }

    // --- proptest-style: random sparse vs dense -----------------------------

    /// Naive O(rows*cols^2) dense reducer over the same field, used as
    /// an oracle for the sparse implementation. Returns the rank.
    #[allow(clippy::needless_range_loop)]
    fn dense_rank(matrix: &mut [Vec<Fr>]) -> usize {
        if matrix.is_empty() {
            return 0;
        }
        let cols = matrix[0].len();
        let rows = matrix.len();
        let mut pr = 0usize;
        let mut col = 0usize;
        while pr < rows && col < cols {
            // find pivot row in [pr, rows) with non-zero in col
            let mut sel = None;
            for i in pr..rows {
                if !matrix[i][col].is_zero() {
                    sel = Some(i);
                    break;
                }
            }
            let Some(i) = sel else {
                col += 1;
                continue;
            };
            matrix.swap(pr, i);
            let inv = matrix[pr][col].inverse().unwrap();
            for v in matrix[pr].iter_mut() {
                *v *= inv;
            }
            for r in 0..rows {
                if r == pr {
                    continue;
                }
                let c = matrix[r][col];
                if c.is_zero() {
                    continue;
                }
                for k in 0..cols {
                    let pk = matrix[pr][k];
                    matrix[r][k] -= c * pk;
                }
            }
            pr += 1;
            col += 1;
        }
        pr
    }

    #[test]
    fn random_sparse_rank_matches_dense_oracle() {
        use ark_std::rand::SeedableRng;
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(0xDEADBEEF);
        for trial in 0..64 {
            let rows = 3 + (trial % 4);
            let cols = 3 + ((trial / 2) % 5);
            let density_q = 3u8; // ~1/3 non-zero
            let dense: Vec<Vec<Fr>> = (0..rows)
                .map(|_| {
                    (0..cols)
                        .map(|_| {
                            if u8::rand(&mut rng) % density_q == 0 {
                                Fr::rand(&mut rng)
                            } else {
                                Fr::zero()
                            }
                        })
                        .collect()
                })
                .collect();
            let mut sparse: Vec<SparseRow<Fr>> =
                dense.iter().map(|d| SparseRow::from_dense(d)).collect();
            let dense_rk = dense_rank(&mut dense.clone());
            let sparse_rk = row_echelon(&mut sparse);
            assert_eq!(
                sparse_rk, dense_rk,
                "trial {} rows={} cols={}",
                trial, rows, cols
            );
        }
    }

    #[test]
    fn rref_kernel_zero_for_dependent_input() {
        // Row 2 is a Fr-linear combination of Row 0 and Row 1.
        let r0 = vec![fr(1), fr(2), fr(0), fr(3)];
        let r1 = vec![fr(0), fr(1), fr(4), fr(2)];
        // r2 = 2*r0 + 3*r1
        let r2: Vec<Fr> = r0
            .iter()
            .zip(&r1)
            .map(|(a, b)| fr(2) * a + fr(3) * b)
            .collect();
        let mut rs = rows_from_dense(&[r0, r1, r2]);
        let r = rref(&mut rs);
        assert_eq!(r, 2);
        assert!(rs[2].is_zero());
    }
}
