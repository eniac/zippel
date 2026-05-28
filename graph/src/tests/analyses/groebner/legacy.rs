//! Test-only legacy in-tree Buchberger implementation.
//!
//! Production Groebner entry points dispatch through ark-gb. This module keeps
//! the original implementation available only in test builds so regression
//! tests and the speedup bench can compare ark-gb against the reference path.

use std::collections::{HashSet, VecDeque};

use ark_ff::Field;
use log::debug;
use rayon::prelude::*;

use crate::analyses::groebner::{GroebnerBasis, Monomial, SparsePolynomial};

impl<F: Field, T: Monomial> GroebnerBasis<F, T> {
    /// Group-parallel pair selection used by [`Self::legacy_buchberger`].
    fn pairs_select(&self, pairs: &mut VecDeque<(usize, usize)>) -> Vec<(usize, usize)> {
        let num_threads = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1)
            .saturating_sub(1)
            .max(2);

        let mut selected = Vec::new();
        for _ in 0..num_threads {
            if let Some((i, j)) = pairs.pop_front() {
                if i < self.len() && j < self.len() {
                    selected.push((i, j));
                }
            } else {
                break;
            }
        }
        selected
    }

    /// In-tree Buchberger implementation retained as a test-only reference.
    pub(crate) fn legacy_buchberger(&self) -> Self {
        if self.basis.is_empty() {
            return Self::empty(self.num_vars);
        }

        let basis_nonzero = self
            .basis
            .iter()
            .filter(|p| !p.is_zero())
            .cloned()
            .collect();

        let mut g: Self = Self::new(self.num_vars, basis_nonzero);
        let mut pairs: VecDeque<(usize, usize)> = VecDeque::new();
        let mut seen = HashSet::new();

        for i in 0..g.len() {
            for j in (i + 1)..g.len() {
                pairs.push_back((i, j));
            }
        }

        while !pairs.is_empty() {
            let ps = g.pairs_select(&mut pairs);
            seen.extend(ps.iter().map(|(i, j)| (*i, *j)));

            let reduced_ps: Vec<SparsePolynomial<F, T>> = ps
                .par_iter()
                .filter_map(|&(i, j)| {
                    if i >= g.len() || j >= g.len() {
                        return None;
                    }

                    let g_i = &g[i];
                    let g_j = &g[j];

                    debug!("Processing pair ({}, {})", i, j);
                    let s_poly = g_i.s_poly(g_j);

                    if s_poly.is_zero() {
                        debug!("  S(G[{}], G[{}]) = 0", i, j);
                        return None;
                    }

                    let s_reduced = g.reduce(s_poly);

                    if !s_reduced.is_zero() {
                        debug!("  S(G[{}], G[{}]) reduces to non-zero polynomial.", i, j);
                        Some(s_reduced)
                    } else {
                        debug!("  S(G[{}], G[{}]) reduces to 0", i, j);
                        None
                    }
                })
                .collect();

            for s_reduced in reduced_ps {
                let k = g.len();
                g.push(s_reduced);

                for l in 0..k {
                    if !Self::skip_pair(l, k, &g, &seen) {
                        pairs.push_back((l, k));
                    }
                }
            }
        }

        g
    }

    /// Buchberger's criteria.
    ///
    /// See <https://www.andrew.cmu.edu/course/15-355/lectures/lecture11.pdf>.
    fn skip_pair(
        l: usize,
        k: usize,
        g: &GroebnerBasis<F, T>,
        seen: &HashSet<(usize, usize)>,
    ) -> bool {
        let lt_l = g[l].leading_term().map(|(_, m)| m);
        let lt_k = g[k].leading_term().map(|(_, m)| m);
        if let (Some(ml), Some(mk)) = (lt_l, lt_k) {
            if ml.is_coprime(&mk) {
                return true;
            }

            return (0..g.len()).into_par_iter().any(|i| {
                if let Some(lt_i) = g[i].leading_term().map(|(_, m)| m)
                    && ml.lcm(&mk).is_divided(&lt_i)
                    && seen.contains(&(l, i))
                    && seen.contains(&(i, k))
                {
                    return true;
                }
                false
            });
        }
        false
    }

    /// Reduces a computed Groebner basis to a minimal, reduced Groebner basis.
    pub(crate) fn legacy_reduce_groebner_basis(&mut self) {
        let num_vars = self.num_vars;

        let mut g_monic = GroebnerBasis::empty(num_vars);
        for p in self.iter() {
            if p.is_zero() {
                continue;
            }

            if let Some((lc, _)) = p.leading_term() {
                let lc_inv = lc
                    .inverse()
                    .expect("Leading coefficient must be invertible in a Field for non-zero poly");

                let mut monic_p = SparsePolynomial::zero();
                for (term, coeff) in p.terms.iter() {
                    monic_p.terms.insert(term, &(*coeff * lc_inv));
                }

                if !monic_p.is_zero() {
                    g_monic.push(monic_p);
                }
            }
        }
        *self = g_monic;

        self.basis.sort_unstable_by(|p1, p2| {
            let lt1 = p1.leading_term().map(|(_, t)| t);
            let lt2 = p2.leading_term().map(|(_, t)| t);
            lt1.cmp(&lt2)
        });

        let mut g_minimal = GroebnerBasis::empty(num_vars);
        let mut discarded = vec![false; self.len()];

        for i in 0..self.len() {
            if discarded[i] {
                continue;
            }
            let lt_i = self[i].leading_term().unwrap().1;

            for j in (i + 1)..self.len() {
                if discarded[j] {
                    continue;
                }
                let lt_j = self[j].leading_term().unwrap().1;

                if lt_j.is_divided(&lt_i) {
                    discarded[j] = true;
                }
            }
        }

        for i in 0..self.len() {
            if !discarded[i] {
                g_minimal.push(self[i].clone());
            }
        }
        *self = g_minimal;

        let mut g_reduced = GroebnerBasis::new(num_vars, Vec::with_capacity(self.len()));
        for i in 0..self.len() {
            let current_g = self[i].clone();

            let mut reduction_basis = GroebnerBasis::empty(num_vars);
            for j in 0..self.len() {
                if i != j {
                    reduction_basis.push(self[j].clone());
                }
            }

            let reduced_g = reduction_basis.reduce(current_g);

            if !reduced_g.is_zero() {
                g_reduced.push(reduced_g);
            }
        }

        g_reduced.basis.sort_unstable_by(|p1, p2| {
            let lt1 = p1.leading_term().map(|(_, t)| t);
            let lt2 = p2.leading_term().map(|(_, t)| t);
            lt1.cmp(&lt2)
        });

        *self = g_reduced;
    }
}

pub(crate) fn legacy_compute_reduced_gb<F: Field, T: Monomial>(
    num_vars: usize,
    basis: Vec<SparsePolynomial<F, T>>,
) -> Vec<SparsePolynomial<F, T>> {
    let mut g = GroebnerBasis::new(num_vars, basis).legacy_buchberger();
    g.legacy_reduce_groebner_basis();
    g.basis
}
