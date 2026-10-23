//! Multilinear extensions as evaluation tables over the boolean hypercube: dense (`2^n`
//! values) or sparse (`(index, value)` entries, an index listed twice taking the sum and an
//! unlisted one zero). Variable `i` is bit `i` of an index.
//!
//! Each operation reads the table alone. Sparse-input results are encoded by their actual
//! density, with dense scratch tables bounded by the number of stored input entries.

use crate::Field;
use lang::typ::CRange;
use rayon::prelude::*;
use std::collections::HashMap;

use super::{PolyVariant, fixed_index_for_var};

/// A multilinear extension by its values on the boolean hypercube: `2^num_vars` of them,
/// variable `i` being bit `i` of an index.
#[derive(Debug, Clone, Default, Hash, PartialEq, Eq)]
pub struct DenseMle<F> {
    num_vars: usize,
    evals: Vec<F>,
}

impl<F> DenseMle<F> {
    /// The MLE over `num_vars` variables with table `evals`.
    ///
    /// # Panics
    /// Panics unless `evals` has `2^num_vars` entries.
    pub fn new(num_vars: usize, evals: Vec<F>) -> Self {
        assert_eq!(
            Some(evals.len()),
            1usize.checked_shl(u32::try_from(num_vars).unwrap_or(u32::MAX)),
            "an MLE over {num_vars} variables has 2^{num_vars} values"
        );
        Self { num_vars, evals }
    }

    /// The number of variables.
    pub fn num_vars(&self) -> usize {
        self.num_vars
    }

    /// The `2^num_vars` values.
    pub fn evals(&self) -> &[F] {
        &self.evals
    }

    /// The `2^num_vars` values.
    pub fn into_evals(self) -> Vec<F> {
        self.evals
    }
}

/// A multilinear extension's table, by encoding.
#[derive(Clone, Copy)]
pub(super) enum Table<'a, F> {
    /// All `2^n` values.
    Dense(&'a [F]),
    /// The non-zero `(index, value)` entries.
    Sparse(&'a [(usize, F)]),
}

/// A sparse result is kept while its non-zero entries fill at most `1 / SPARSE_MAX_FILL` of
/// its `2^num_vars` indices; a fuller table is cheaper dense, as a sparse entry stores an
/// index beside its value and is read through a lookup.
const SPARSE_MAX_FILL: usize = 4;

/// Blocks above this many entries evaluate their halves in parallel.
const PARALLEL_BLOCK: usize = 1 << 10;

/// The MLE over `num_vars` variables with the given entries (an index listed twice takes the
/// sum), encoded by density: a `SparseMle`, sorted and without zeros, while it is sparse
/// enough (see [`SPARSE_MAX_FILL`]), else a `DenseMle`.
fn from_entries<F: Field>(
    num_vars: usize,
    entries: impl IntoIterator<Item = (usize, F)>,
) -> PolyVariant<F> {
    let mut sums: HashMap<usize, F> = HashMap::new();
    for (i, v) in entries {
        *sums.entry(i).or_insert_with(F::zero) += v;
    }
    sums.retain(|_, v| !v.is_zero());
    match 1usize.checked_shl(num_vars as u32) {
        Some(len) if sums.len().saturating_mul(SPARSE_MAX_FILL) > len => {
            let mut dense = vec![F::zero(); len];
            for (i, v) in sums {
                dense[i] = v;
            }
            dense_mle(num_vars, dense)
        }
        _ => {
            let mut evals: Vec<(usize, F)> = sums.into_iter().collect();
            evals.sort_unstable_by_key(|&(i, _)| i);
            PolyVariant::SparseMle { num_vars, evals }
        }
    }
}

/// The `DenseMle` with table `values` over `num_vars` variables.
pub(super) fn dense_mle<F: Field>(num_vars: usize, values: Vec<F>) -> PolyVariant<F> {
    PolyVariant::DenseMle(DenseMle::new(num_vars, values))
}

/// The dense table of the sparse entries `evals` over `num_vars` variables.
pub(super) fn to_dense<F: Field>(num_vars: usize, evals: &[(usize, F)]) -> Vec<F> {
    let len = 1usize << num_vars;
    let mut dense = vec![F::zero(); len];
    for &(i, v) in evals {
        debug_assert!(i < len, "SparseMle index out of range");
        dense[i] += v;
    }
    dense
}

/// The sum of two tables over the same variables: sparse while both are and it stays sparse
/// ([`from_entries`]), else dense.
pub(super) fn add<F: Field>(num_vars: usize, a: Table<'_, F>, b: Table<'_, F>) -> PolyVariant<F> {
    match (a, b) {
        (Table::Sparse(a), Table::Sparse(b)) => from_entries(num_vars, a.iter().chain(b).copied()),
        (Table::Dense(a), Table::Dense(b)) => {
            dense_mle(num_vars, a.iter().zip(b).map(|(x, y)| *x + y).collect())
        }
        (Table::Dense(d), Table::Sparse(s)) | (Table::Sparse(s), Table::Dense(d)) => {
            let mut sum = d.to_vec();
            for &(i, v) in s {
                sum[i] += v;
            }
            dense_mle(num_vars, sum)
        }
    }
}

/// The extension at `point`, which fixes every variable.
pub(super) fn evaluate<F: Field>(table: Table<'_, F>, point: &[F]) -> F {
    match table {
        Table::Dense(values) => evaluate_block(values, point),
        Table::Sparse(evals) => {
            let one_minus: Vec<F> = point.iter().map(|r| F::one() - r).collect();
            evals
                .par_iter()
                .map(|&(i, v)| v * eq_weight(i, point, &one_minus))
                .sum()
        }
    }
}

/// The extension over `num_vars` variables with its low `point.len()` variables (fewer than
/// all) fixed to `point`, the rest renumbered from 0.
///
/// A dense table is folded block by block: entry `j` of the result is the block
/// `values[j·2^k..(j+1)·2^k]` evaluated at the `k`-coordinate `point`, and only the
/// `2^(n-k)`-entry result is allocated (arkworks' `fix_variables` first copies the whole
/// table, and folds it single-threaded). A sparse table weighs each entry by
/// `eq(point, low bits)` and adds it to the entry of its high bits, in `O(|evals| · k)`.
pub(super) fn fix_low<F: Field>(
    num_vars: usize,
    table: Table<'_, F>,
    point: &[F],
) -> PolyVariant<F> {
    let k = point.len();
    match table {
        Table::Dense(values) => dense_mle(
            num_vars - k,
            values
                .par_chunks(1 << k)
                .map(|block| evaluate_block(block, point))
                .collect(),
        ),
        Table::Sparse(evals) => {
            let remaining = num_vars - k;
            if let Some(len) = 1usize.checked_shl(u32::try_from(remaining).unwrap_or(u32::MAX))
                && len <= evals.len().saturating_mul(SPARSE_MAX_FILL)
            {
                let values = fix_sparse_into_dense(evals, point, len);
                let nonzero = values.iter().filter(|v| !v.is_zero()).count();
                return if nonzero.saturating_mul(SPARSE_MAX_FILL) > len {
                    dense_mle(remaining, values)
                } else {
                    PolyVariant::SparseMle {
                        num_vars: remaining,
                        evals: values
                            .into_iter()
                            .enumerate()
                            .filter(|(_, v)| !v.is_zero())
                            .collect(),
                    }
                };
            }
            let one_minus: Vec<F> = point.iter().map(|r| F::one() - r).collect();
            from_entries(
                num_vars - k,
                evals
                    .iter()
                    .map(|&(i, v)| (i >> k, v * eq_weight(i, point, &one_minus))),
            )
        }
    }
}

/// Accumulate directly when the output table is bounded by the stored input size.
/// Keep the arithmetic loop separate from representation selection: inlining it into
/// the dispatch regresses the sparse matrix partial evaluations used by Spartan.
#[inline(never)]
fn fix_sparse_into_dense<F: Field>(evals: &[(usize, F)], point: &[F], len: usize) -> Vec<F> {
    let k = point.len();
    let one_minus: Vec<F> = point.iter().map(|r| F::one() - r).collect();
    let mut out = vec![F::zero(); len];
    for &(i, v) in evals {
        let weighted = (0..k).fold(v, |acc, j| {
            acc * if (i >> j) & 1 == 1 {
                point[j]
            } else {
                one_minus[j]
            }
        });
        out[i >> k] += weighted;
    }
    out
}

/// The extension over `input_num_vars` variables with every variable outside `free_range`
/// fixed to the next value of `fixed` (see [`fixed_index_for_var`]), the free ones kept in
/// order. Each entry is weighted by `eq(fixed, its fixed bits)` and added to the entry of its
/// free bits; a dense table fixed only to 0s and 1s is read off directly.
pub(super) fn restrict<F: Field>(
    input_num_vars: usize,
    table: Table<'_, F>,
    free_range: &CRange,
    fixed: &[F],
) -> PolyVariant<F> {
    let free_len = free_range.len();
    match table {
        Table::Dense(values) => {
            if let Some(bits) = boolean(fixed) {
                return dense_mle(
                    free_len,
                    restrict_to_bits(input_num_vars, values, free_range, &bits),
                );
            }
            let mut out = vec![F::zero(); 1 << free_len];
            let entries = values.iter().copied().enumerate();
            for (i, v) in restricted_entries(input_num_vars, entries, free_range, fixed) {
                out[i] += v;
            }
            dense_mle(free_len, out)
        }
        Table::Sparse(evals) => from_entries(
            free_len,
            restricted_entries(input_num_vars, evals.iter().copied(), free_range, fixed),
        ),
    }
}

/// The table at the free variables' bits when every fixed variable is 0 or 1 (`bits`): each
/// output entry is one input entry.
fn restrict_to_bits<F: Field>(
    input_num_vars: usize,
    values: &[F],
    free_range: &CRange,
    bits: &[bool],
) -> Vec<F> {
    let entry = |free_idx: usize| {
        let mut idx = 0usize;
        for var in 0..input_num_vars {
            let bit = match fixed_index_for_var(free_range, var) {
                None => (free_idx >> (var - free_range.start())) & 1 == 1,
                Some(i) => bits[i],
            };
            idx |= usize::from(bit) << var;
        }
        values[idx]
    };
    let len = 1usize << free_range.len();
    if len <= 1024 {
        (0..len).map(entry).collect()
    } else {
        (0..len).into_par_iter().map(entry).collect()
    }
}

/// Each entry weighted by the fixed variables' values and moved to its index among the free
/// variables; entries landing on the same index are to be summed.
fn restricted_entries<'a, F: Field>(
    input_num_vars: usize,
    entries: impl Iterator<Item = (usize, F)> + 'a,
    free_range: &'a CRange,
    fixed: &'a [F],
) -> impl Iterator<Item = (usize, F)> + 'a {
    entries.map(move |(idx, value)| {
        let mut free_idx = 0usize;
        let mut factor = value;
        for var in 0..input_num_vars {
            let bit = (idx >> var) & 1 == 1;
            match fixed_index_for_var(free_range, var) {
                None => free_idx |= usize::from(bit) << (var - free_range.start()),
                Some(i) => factor *= if bit { fixed[i] } else { F::one() - fixed[i] },
            }
        }
        (free_idx, factor)
    })
}

/// `values` as bits when each is 0 or 1.
fn boolean<F: Field>(values: &[F]) -> Option<Vec<bool>> {
    values
        .iter()
        .map(|v| {
            if v.is_zero() {
                Some(false)
            } else if v.is_one() {
                Some(true)
            } else {
                None
            }
        })
        .collect()
}

/// The extension of `block` (`2^point.len()` values) at `point`: the halves on the last
/// variable, combined.
fn evaluate_block<F: Field>(block: &[F], point: &[F]) -> F {
    let Some((&r, rest)) = point.split_last() else {
        return block[0];
    };
    let (lo, hi) = block.split_at(block.len() / 2);
    let (a, b) = if block.len() > PARALLEL_BLOCK {
        rayon::join(|| evaluate_block(lo, rest), || evaluate_block(hi, rest))
    } else {
        (evaluate_block(lo, rest), evaluate_block(hi, rest))
    };
    a + r * (b - a)
}

/// `eq(point, low bits of idx)`, with `one_minus[j] = 1 - point[j]`.
fn eq_weight<F: Field>(idx: usize, point: &[F], one_minus: &[F]) -> F {
    point
        .iter()
        .zip(one_minus)
        .enumerate()
        .map(|(j, (r, s))| if (idx >> j) & 1 == 1 { *r } else { *s })
        .product()
}
