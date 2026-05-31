//! `BSet` — transient per-survivor pair set.
//!
//! Design reference: `~/project/docs/rust-bba-port-plan.md` §7.4.
//!
//! The bba driver builds a `BSet` per newly-reduced survivor `h`:
//! one candidate pair per live basis element (filtered by the
//! product criterion). The chain criterion then dedups within the
//! set and the survivors merge into the main [`LSet`](crate::lset::LSet).
//!
//! `BSet` is unsorted (append-only `Vec<Pair>`) because the driver
//! walks it linearly and the hash index is enough for
//! remove-by-indices. No priority queue here.

use std::collections::HashMap;

use crate::pair::Pair;

/// Transient pair set built during `enterpairs`.
///
/// `Send + Sync` — just plain data. The driver owns it for the
/// duration of a single `enterpairs` call and drops it afterward.
#[derive(Debug, Default)]
pub struct BSet<const W: usize = 4> {
    pairs: Vec<Pair<W>>,
    /// Parallel array of `pair.lcm_sev` values. Maintained in
    /// lockstep with `pairs` (push appends to both; swap_remove
    /// swap-removes from both at the same index). Used by the
    /// SIMD-batched chain-criterion sweep introduced in ADR-009;
    /// see `~/ark_gb/docs/design-decisions.md` ADR-009 for the
    /// rationale (Singular's `sev_flat` flat-parallel-array
    /// pattern, applied to the BSet's pairs).
    lcm_sevs: Vec<u64>,
    /// (i, j) → index into `pairs`. Never holds a stale mapping: on
    /// removal the last element is swapped in and the hash for the
    /// swapped-in pair is updated.
    by_indices: HashMap<(u32, u32), usize>,
}

impl<const W: usize> BSet<W> {
    /// Empty B set.
    pub fn new() -> Self {
        Self {
            pairs: Vec::new(),
            lcm_sevs: Vec::new(),
            by_indices: HashMap::new(),
        }
    }

    /// Number of pairs.
    #[inline]
    pub fn len(&self) -> usize {
        self.pairs.len()
    }

    /// Whether the set is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.pairs.is_empty()
    }

    /// Push a pair. Panics in debug builds if `(i, j)` is already
    /// present — the caller is expected to build B without
    /// duplicates (the chain criterion handles chain-implied pairs,
    /// not literal duplicates).
    pub fn push(&mut self, pair: Pair<W>) {
        let idx = self.pairs.len();
        let key = (pair.i, pair.j);
        debug_assert!(
            !self.by_indices.contains_key(&key),
            "BSet duplicate push of {:?}",
            key
        );
        self.by_indices.insert(key, idx);
        self.lcm_sevs.push(pair.lcm_sev);
        self.pairs.push(pair);
    }

    /// Borrow the raw pair slice.
    #[inline]
    pub fn pairs(&self) -> &[Pair<W>] {
        &self.pairs
    }

    /// Borrow the parallel `lcm_sev` array. `lcm_sevs()[i]` equals
    /// `pairs()[i].lcm_sev` for every valid `i`. Used by the
    /// ADR-009 SIMD-batched chain-criterion sweep.
    #[inline]
    pub fn lcm_sevs(&self) -> &[u64] {
        &self.lcm_sevs
    }

    /// Remove the pair at `at` (swap-remove). Returns the removed
    /// pair. Keeps `by_indices` consistent.
    pub fn swap_remove(&mut self, at: usize) -> Pair<W> {
        let removed = self.pairs.swap_remove(at);
        self.lcm_sevs.swap_remove(at);
        self.by_indices.remove(&(removed.i, removed.j));
        if at < self.pairs.len() {
            // The element previously at the end now lives at `at`.
            let moved = &self.pairs[at];
            self.by_indices.insert((moved.i, moved.j), at);
        }
        removed
    }

    /// Drain the entire set, consuming it into its constituent pairs.
    pub fn into_pairs(self) -> Vec<Pair<W>> {
        self.pairs
    }

    /// Debug-only invariant check.
    pub fn assert_canonical<F: ark_ff::Field + Copy + Send + Sync>(
        &self,
        ring: &crate::ring::Ring<F, W>,
    ) {
        assert_eq!(self.pairs.len(), self.by_indices.len(), "index size");
        assert_eq!(
            self.pairs.len(),
            self.lcm_sevs.len(),
            "pairs / lcm_sevs length mismatch"
        );
        for (idx, pair) in self.pairs.iter().enumerate() {
            pair.assert_canonical(ring);
            let got = self.by_indices.get(&(pair.i, pair.j));
            assert_eq!(got, Some(&idx), "by_indices mismatch for {idx}");
            assert_eq!(
                self.lcm_sevs[idx], pair.lcm_sev,
                "lcm_sevs[{idx}] out of sync with pair.lcm_sev"
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::monomial::MonoTerm;
    use crate::ring::Ring;
    use ark_bls12_381::Fr;

    fn mk_ring(nvars: u32) -> Ring<Fr> {
        Ring::<Fr>::new(nvars).unwrap()
    }

    fn mk_pair(r: &Ring<Fr>, i: u32, j: u32, sugar: u32, arrival: u64) -> Pair {
        let lcm = MonoTerm::from_exponents(r, &vec![1u32; r.nvars() as usize]).unwrap();
        Pair::new(i, j, lcm, sugar, arrival)
    }

    #[test]
    fn push_and_swap_remove_maintain_index() {
        let r = mk_ring(3);
        let mut b = BSet::new();
        b.push(mk_pair(&r, 0, 1, 3, 0));
        b.push(mk_pair(&r, 0, 2, 4, 1));
        b.push(mk_pair(&r, 0, 3, 5, 2));
        b.assert_canonical(&r);
        let removed = b.swap_remove(1);
        assert_eq!((removed.i, removed.j), (0, 2));
        b.assert_canonical(&r);
        assert_eq!(b.len(), 2);
    }
}
