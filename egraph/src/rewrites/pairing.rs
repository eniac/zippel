//! Pairing rewrite (i).
//!
//! `(assert (pair ?a ?b) (pair ?c ?d))` →
//! `(assert (dot (vec ?a ?c) (vec ?b (neg ?d))) (constant "gt_zero"))`.
//!
//! Generalizes to N pairings: collects all Pair nodes under Assert,
//! builds `Dot(Vec(all_g1s), Vec(all_g2s_with_negs))`.
//! `Dot` of `Vec(G1,N) × Vec(G2,N)` = sum of pairings → GT.
//!
//! The RHS constant is `Value::GT(PairingOutput::zero())`.

use std::marker::PhantomData;

use crate::lang::{ZAnalysis, ZIR};
use backend::{ATyp, ArkConfig, Value};
use egg::{Applier, EGraph, Id, PatternAst, Rewrite, SearchMatches, Subst, Symbol, Var};

/// Custom Searcher for the pairing rewrite.
/// Walks e-classes looking for `Assert(Pair(a,b), Pair(c,d))` patterns
/// where both children of Assert are Pair nodes.
pub struct PairingSearcher<C: ArkConfig>(PhantomData<C>);

impl<C: ArkConfig + std::fmt::Debug> egg::Searcher<ZIR<C>, ZAnalysis<C>> for PairingSearcher<C> {
    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph<ZIR<C>, ZAnalysis<C>>,
        eclass: Id,
        limit: usize,
    ) -> Option<SearchMatches<'_, ZIR<C>>> {
        let mut substs = vec![];
        for node in &egraph[eclass].nodes {
            if let ZIR::Assert([lhs, rhs]) = node {
                let lhs_class = egraph.find(*lhs);
                let rhs_class = egraph.find(*rhs);
                // Both children must be Pair nodes
                let lhs_is_pair = egraph[lhs_class]
                    .nodes
                    .iter()
                    .any(|n| matches!(n, ZIR::Pair(_)));
                let rhs_is_pair = egraph[rhs_class]
                    .nodes
                    .iter()
                    .any(|n| matches!(n, ZIR::Pair(_)));
                if lhs_is_pair && rhs_is_pair {
                    substs.push(Subst::default());
                    if substs.len() >= limit {
                        break;
                    }
                }
            }
        }
        if substs.is_empty() {
            None
        } else {
            Some(SearchMatches {
                eclass,
                substs,
                ast: None,
            })
        }
    }

    fn vars(&self) -> Vec<Var> {
        vec![]
    }
}

/// Custom Applier for the pairing rewrite.
/// Collects all Pair nodes from both Assert children, builds
/// `Assert(Dot(Vec(g1s), Vec(g2s_with_neg)), Constant(GT_zero))`.
pub struct PairingApplier<C: ArkConfig>(PhantomData<C>);

impl<C: ArkConfig + std::fmt::Debug> Applier<ZIR<C>, ZAnalysis<C>> for PairingApplier<C> {
    fn apply_one(
        &self,
        egraph: &mut EGraph<ZIR<C>, ZAnalysis<C>>,
        eclass: Id,
        _subst: &Subst,
        _searcher_ast: Option<&PatternAst<ZIR<C>>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        // Find Assert nodes in this e-class
        let assert_nodes: Vec<[Id; 2]> = egraph[eclass]
            .nodes
            .iter()
            .filter_map(|n| {
                if let ZIR::Assert(ids) = n {
                    Some(*ids)
                } else {
                    None
                }
            })
            .collect();

        let mut added = vec![];
        for [lhs, rhs] in assert_nodes {
            // Collect Pair children from both sides
            let mut g1s: Vec<Id> = vec![];
            let mut g2s: Vec<Id> = vec![];

            // Extract Pair(a, b) from lhs e-class
            let lhs_class = egraph.find(lhs);
            for node in &egraph[lhs_class].nodes {
                if let ZIR::Pair([a, b]) = node {
                    g1s.push(egraph.find(*a));
                    g2s.push(egraph.find(*b));
                }
            }

            // Extract Pair(c, d) from rhs e-class
            let rhs_class = egraph.find(rhs);
            for node in &egraph[rhs_class].nodes {
                if let ZIR::Pair([c, d]) = node {
                    g1s.push(egraph.find(*c));
                    g2s.push(egraph.find(*d));
                }
            }

            if g1s.len() < 2 || g1s.len() != g2s.len() {
                continue;
            }

            // Negate all g2s: Neg(g2) for each
            let neg_g2s: Vec<Id> = g2s.iter().map(|&id| egraph.add(ZIR::Neg([id]))).collect();

            // Build Vec(g1s) and Vec(neg_g2s)
            let vec_g1 = egraph.add(ZIR::Vec(g1s.into_boxed_slice()));
            let vec_g2 = egraph.add(ZIR::Vec(neg_g2s.into_boxed_slice()));

            // Build Dot(vec_g1, vec_g2)
            let dot = egraph.add(ZIR::Dot([vec_g1, vec_g2]));

            // Create GT zero constant
            let gt_zero = egraph.add(ZIR::Constant(Value::zero(&ATyp::gt())));

            // Build Assert(dot, gt_zero)
            let new_assert = egraph.add(ZIR::Assert([dot, gt_zero]));

            // Union with the matched e-class
            if egraph.union(eclass, new_assert) {
                added.push(new_assert);
            }
        }
        added
    }
}

pub fn rewrites<C: ArkConfig + std::fmt::Debug + Clone + 'static>()
-> Vec<Rewrite<ZIR<C>, ZAnalysis<C>>> {
    vec![
        Rewrite::new(
            "pairing",
            PairingSearcher::<C>(PhantomData),
            PairingApplier::<C>(PhantomData),
        )
        .unwrap(),
    ]
}
