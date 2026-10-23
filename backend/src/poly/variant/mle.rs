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

/// Temporary dense tables use at most this many field elements per stored input entry.
/// This allocation budget is independent of the result's density threshold.
const DENSE_SCRATCH_FACTOR: usize = 4;

/// Blocks above this many entries evaluate their halves in parallel.
const PARALLEL_BLOCK: usize = 1 << 10;

/// The MLE over `num_vars` variables with the given entries (an index listed twice takes the
/// sum), encoded by density: a `SparseMle`, sorted and without zeros, while it is sparse
/// enough (see [`SPARSE_MAX_FILL`]), else a `DenseMle`.
/// Dense scratch storage is bounded by the iterator's known entry count. Its choice
/// does not determine the result encoding, which depends only on actual nonzeros.
fn from_entries<F: Field>(
    num_vars: usize,
    entries: impl IntoIterator<Item = (usize, F)>,
) -> PolyVariant<F> {
    enum Accumulated<F> {
        Dense(Vec<F>),
        Sparse(HashMap<usize, F>),
    }

    let entries = entries.into_iter();
    let len = 1usize.checked_shl(u32::try_from(num_vars).unwrap_or(u32::MAX));
    let mut sums = match len {
        Some(len) if len <= entries.size_hint().0.saturating_mul(DENSE_SCRATCH_FACTOR) => {
            Accumulated::Dense(accumulate_dense(len, entries))
        }
        _ => {
            let mut sums: HashMap<usize, F> = HashMap::new();
            for (i, v) in entries {
                *sums.entry(i).or_insert_with(F::zero) += v;
            }
            Accumulated::Sparse(sums)
        }
    };
    let nonzero = match &mut sums {
        Accumulated::Dense(values) => values.iter().filter(|v| !v.is_zero()).count(),
        Accumulated::Sparse(entries) => {
            entries.retain(|_, v| !v.is_zero());
            entries.len()
        }
    };
    if let Some(len) = len
        && nonzero.saturating_mul(SPARSE_MAX_FILL) > len
    {
        let values = match sums {
            Accumulated::Dense(values) => values,
            Accumulated::Sparse(entries) => accumulate_dense(len, entries),
        };
        return dense_mle(num_vars, values);
    }
    let evals = match sums {
        Accumulated::Dense(values) => values
            .into_iter()
            .enumerate()
            .filter(|(_, v)| !v.is_zero())
            .collect(),
        Accumulated::Sparse(entries) => {
            let mut evals: Vec<_> = entries.into_iter().collect();
            evals.sort_unstable_by_key(|&(i, _)| i);
            evals
        }
    };
    PolyVariant::SparseMle { num_vars, evals }
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

/// `Σ c·f` over the tables `terms`, all over `num_vars` variables: dense when any table is,
/// else encoded by density ([`from_entries`]).
pub(super) fn linear_combination<F: Field>(
    num_vars: usize,
    terms: &[(F, Table<'_, F>)],
) -> PolyVariant<F> {
    if terms.iter().all(|(_, t)| matches!(t, Table::Sparse(_))) {
        return from_entries(
            num_vars,
            terms.iter().flat_map(|&(c, table)| {
                let evals: &[(usize, F)] = match table {
                    Table::Sparse(evals) => evals,
                    Table::Dense(_) => &[],
                };
                evals.iter().map(move |&(i, v)| (i, c * v))
            }),
        );
    }
    let mut out = vec![F::zero(); 1 << num_vars];
    for &(c, table) in terms {
        match table {
            Table::Dense(values) => out
                .par_iter_mut()
                .zip(values)
                .with_min_len(PARALLEL_BLOCK)
                .for_each(|(o, &v)| *o += c * v),
            Table::Sparse(evals) => {
                for &(i, v) in evals {
                    out[i] += c * v;
                }
            }
        }
    }
    dense_mle(num_vars, out)
}

/// The extension at `point`, which fixes every variable.
pub(super) fn evaluate<F: Field>(table: Table<'_, F>, point: &[F]) -> F {
    match table {
        Table::Dense(values) => evaluate_block(values, point),
        Table::Sparse(evals) => {
            let weights = EqualityWeights::new(point, evals.len());
            evals.par_iter().map(|&(i, v)| weights.apply(i, v)).sum()
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
/// `eq(point, low bits)` and adds it to the entry of its high bits. A bounded equality
/// table shares weights; otherwise each entry computes its `k` factors directly.
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
            let weights = EqualityWeights::new(point, evals.len());
            from_entries(
                num_vars - k,
                evals.iter().map(|&(i, v)| (i >> k, weights.apply(i, v))),
            )
        }
    }
}

/// Keep accumulation separate from representation selection, preserving the outlined
/// arithmetic loop used by sparse matrix partial evaluations.
#[inline(never)]
fn accumulate_dense<F: Field>(len: usize, entries: impl IntoIterator<Item = (usize, F)>) -> Vec<F> {
    let mut out = vec![F::zero(); len];
    for (i, v) in entries {
        out[i] += v;
    }
    out
}

enum EqualityWeights<'a, F> {
    Table(Vec<F>),
    Factors { point: &'a [F], one_minus: Vec<F> },
}

impl<'a, F: Field> EqualityWeights<'a, F> {
    fn new(point: &'a [F], entries: usize) -> Self {
        Self::table(point, entries).map_or_else(
            || Self::Factors {
                point,
                one_minus: point.iter().map(|r| F::one() - r).collect(),
            },
            Self::Table,
        )
    }

    fn apply(&self, index: usize, value: F) -> F {
        match self {
            Self::Table(weights) => value * weights[index & (weights.len() - 1)],
            Self::Factors { point, one_minus } => (0..point.len()).fold(value, |acc, j| {
                acc * if (index >> j) & 1 == 1 {
                    point[j]
                } else {
                    one_minus[j]
                }
            }),
        }
    }

    /// `eq(point, i)` for every low-bit index, when both storage and multiplication count
    /// are bounded by the direct per-entry calculation. Build each pair with one multiply.
    fn table(point: &[F], entries: usize) -> Option<Vec<F>> {
        let len = 1usize.checked_shl(u32::try_from(point.len()).ok()?)?;
        if len > entries.saturating_mul(DENSE_SCRATCH_FACTOR)
            || len > entries.saturating_mul(point.len().saturating_sub(1))
        {
            return None;
        }
        let mut weights = Vec::with_capacity(len);
        weights.push(F::one());
        for &r in point {
            let half = weights.len();
            weights.resize(half * 2, F::zero());
            for i in 0..half {
                let right = weights[i] * r;
                weights[half + i] = right;
                weights[i] -= right;
            }
        }
        Some(weights)
    }
}

/// The extension over `input_num_vars` variables with every variable outside `free_range`
/// fixed to the next value of `fixed` (see [`fixed_index_for_var`]), the free ones kept in
/// order. Each entry is weighted by `eq(fixed, its fixed bits)` and added to the entry of its
/// free bits; a dense table fixed only to 0s and 1s is read off directly, and one whose free
/// variables are the low ones folds its high variables away ([`fix_high`]).
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
            if free_range.start() == 0 {
                return dense_mle(free_len, fix_high(values, fixed));
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

/// The table with its high `point.len()` variables fixed to `point`, the low ones kept in
/// order: the highest variable at a time, each fold combining the table's halves as
/// `lo + r·(hi - lo)`. Scratch is at most half the input.
fn fix_high<F: Field>(values: &[F], point: &[F]) -> Vec<F> {
    let Some((&r, rest)) = point.split_last() else {
        return values.to_vec();
    };
    let (lo, hi) = values.split_at(values.len() / 2);
    let mut out: Vec<F> = lo
        .par_iter()
        .zip(hi)
        .with_min_len(PARALLEL_BLOCK)
        .map(|(&a, &b)| a + r * (b - a))
        .collect();
    for &r in rest.iter().rev() {
        let half = out.len() / 2;
        let (lo, hi) = out.split_at_mut(half);
        lo.par_iter_mut()
            .zip(&*hi)
            .with_min_len(PARALLEL_BLOCK)
            .for_each(|(a, &b)| *a += r * (b - *a));
        out.truncate(half);
    }
    out.shrink_to_fit();
    out
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
