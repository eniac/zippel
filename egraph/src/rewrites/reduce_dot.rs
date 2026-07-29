//! Reduce→dot rewrite (v).
//!
//! `Reduce(Add, Map(?tag, [?dom, Mul(?a, ?b)]))` → `Dot(?a, ?b)`
//! when ?a and ?b are vector-typed.
//!
//! Uses a custom Searcher because `Map(Symbol, _)` can't bind the
//! binder tag as a pattern variable (egg matches Symbol data exactly).

use std::marker::PhantomData;

use crate::lang::{ZAnalysis, ZIR};
use backend::{ATyp, ArkConfig};
use egg::{Applier, EGraph, Id, PatternAst, Rewrite, SearchMatches, Subst, Symbol, Var};
use lang::ast::BinOp;

/// Custom Searcher for reduce→dot.
/// Walks e-classes looking for `Reduce(Add, [Map(tag, [dom, Mul([a, b])])])`
/// where a and b are vector-typed.
pub struct ReduceDotSearcher<C: ArkConfig>(PhantomData<C>);

impl<C: ArkConfig + std::fmt::Debug> egg::Searcher<ZIR<C>, ZAnalysis<C>> for ReduceDotSearcher<C> {
    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph<ZIR<C>, ZAnalysis<C>>,
        eclass: Id,
        limit: usize,
    ) -> Option<SearchMatches<'_, ZIR<C>>> {
        let mut substs = vec![];
        for node in &egraph[eclass].nodes {
            // Look for Reduce(BinOp::Add, [map_id])
            if let ZIR::Reduce(BinOp::Add, [map_id]) = node {
                let map_class = egraph.find(*map_id);
                // Find a Map(tag, [dom, body]) in the map's e-class
                for map_node in &egraph[map_class].nodes {
                    if let ZIR::Map(_tag, [_dom_id, body_id]) = map_node {
                        let body_class = egraph.find(*body_id);
                        // Find a Mul([a, b]) in the body's e-class
                        for body_node in &egraph[body_class].nodes {
                            if let ZIR::Mul([a, b]) = body_node {
                                let a_id = egraph.find(*a);
                                let b_id = egraph.find(*b);
                                // Type guard: both a and b must be vector-typed
                                let a_typ = &egraph[a_id].data.typ;
                                let b_typ = &egraph[b_id].data.typ;
                                if matches!(a_typ, ATyp::Vec(_, _))
                                    && matches!(b_typ, ATyp::Vec(_, _))
                                {
                                    substs.push(Subst::default());
                                    if substs.len() >= limit {
                                        break;
                                    }
                                }
                            }
                        }
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

/// Custom Applier for reduce→dot.
/// Reconstructs the Mul children from the matched Reduce/Map/Mul structure
/// and creates `Dot(a, b)`, unioning with the matched e-class.
pub struct ReduceDotApplier<C: ArkConfig>(PhantomData<C>);

impl<C: ArkConfig + std::fmt::Debug> Applier<ZIR<C>, ZAnalysis<C>> for ReduceDotApplier<C> {
    fn apply_one(
        &self,
        egraph: &mut EGraph<ZIR<C>, ZAnalysis<C>>,
        eclass: Id,
        _subst: &Subst,
        _searcher_ast: Option<&PatternAst<ZIR<C>>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        // Find all Reduce(Add, [map_id]) nodes in this e-class
        let reduce_nodes: Vec<Id> = egraph[eclass]
            .nodes
            .iter()
            .filter_map(|n| {
                if let ZIR::Reduce(BinOp::Add, [map_id]) = n {
                    Some(*map_id)
                } else {
                    None
                }
            })
            .collect();

        let mut added = vec![];
        for map_id in reduce_nodes {
            let map_class = egraph.find(map_id);
            // Find Map(tag, [dom, body]) in the map's e-class
            let map_nodes: Vec<(Symbol, Id, Id)> = egraph[map_class]
                .nodes
                .iter()
                .filter_map(|n| {
                    if let ZIR::Map(tag, [dom_id, body_id]) = n {
                        Some((*tag, *dom_id, *body_id))
                    } else {
                        None
                    }
                })
                .collect();

            for (_tag, _dom_id, body_id) in map_nodes {
                let body_class = egraph.find(body_id);
                // Find Mul([a, b]) in the body's e-class
                let mul_nodes: Vec<[Id; 2]> = egraph[body_class]
                    .nodes
                    .iter()
                    .filter_map(|n| {
                        if let ZIR::Mul(ids) = n {
                            Some(*ids)
                        } else {
                            None
                        }
                    })
                    .collect();

                for [a, b] in mul_nodes {
                    let a_id = egraph.find(a);
                    let b_id = egraph.find(b);
                    // Type guard: both must be vector-typed
                    let a_typ = &egraph[a_id].data.typ;
                    let b_typ = &egraph[b_id].data.typ;
                    if !matches!(a_typ, ATyp::Vec(_, _)) || !matches!(b_typ, ATyp::Vec(_, _)) {
                        continue;
                    }
                    // Create Dot(a, b) and union with the matched e-class
                    let dot = egraph.add(ZIR::Dot([a_id, b_id]));
                    if egraph.union(eclass, dot) {
                        added.push(dot);
                    }
                }
            }
        }
        added
    }
}

pub fn rewrites<C: ArkConfig + std::fmt::Debug + Clone + 'static>()
-> Vec<Rewrite<ZIR<C>, ZAnalysis<C>>> {
    vec![
        Rewrite::new(
            "reduce-dot",
            ReduceDotSearcher::<C>(PhantomData),
            ReduceDotApplier::<C>(PhantomData),
        )
        .unwrap(),
    ]
}
