//! Reduce→dot rewrite (v).
//!
//! `Reduce(Add, Map(?tag, [?dom, Mul(?a, ?b)]))` → `Dot(?a, ?b)`
//! when ?a and ?b are vector-typed.
//!
//! Uses a custom Searcher because `Map(Symbol, _)` can't bind the
//! binder tag as a pattern variable (egg matches Symbol data exactly).

use std::marker::PhantomData;

use super::v;
use crate::lang::{ZAnalysis, ZIR};
use backend::{ATyp, ArkConfig};
use egg::{Applier, EGraph, Id, PatternAst, Rewrite, SearchMatches, Subst, Symbol, Var};
use lang::ast::BinOp;

/// Custom Searcher for reduce→dot.
/// Walks e-classes looking for `Reduce(Add, [Map(tag, [dom, Mul([a, b])])])`
/// where a and b are vector-typed.
/// Binds `?a` and `?b` to the Mul's two child e-class Ids.
pub struct ReduceDotSearcher<C: ArkConfig>(PhantomData<C>);

impl<C: ArkConfig + std::fmt::Debug> egg::Searcher<ZIR<C>, ZAnalysis<C>> for ReduceDotSearcher<C> {
    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph<ZIR<C>, ZAnalysis<C>>,
        eclass: Id,
        limit: usize,
    ) -> Option<SearchMatches<'_, ZIR<C>>> {
        if limit == 0 {
            return None;
        }
        let a_var = v("?a");
        let b_var = v("?b");
        let mut substs = vec![];
        'outer: for node in &egraph[eclass].nodes {
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
                                    let mut subst = Subst::default();
                                    subst.insert(a_var, a_id);
                                    subst.insert(b_var, b_id);
                                    substs.push(subst);
                                    if substs.len() >= limit {
                                        break 'outer;
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
        vec![v("?a"), v("?b")]
    }
}

/// Custom Applier for reduce→dot.
/// Uses `?a` and `?b` from the Subst to find the specific Mul node,
/// creates `Dot(a, b)`, unions with the matched e-class.
pub struct ReduceDotApplier<C: ArkConfig>(PhantomData<C>);

impl<C: ArkConfig + std::fmt::Debug> Applier<ZIR<C>, ZAnalysis<C>> for ReduceDotApplier<C> {
    fn apply_one(
        &self,
        egraph: &mut EGraph<ZIR<C>, ZAnalysis<C>>,
        eclass: Id,
        subst: &Subst,
        _searcher_ast: Option<&PatternAst<ZIR<C>>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        let a_class = egraph.find(subst[v("?a")]);
        let b_class = egraph.find(subst[v("?b")]);

        // Find the specific Reduce(Add, [Map(tag, [dom, Mul([a, b])])])
        // in this e-class that references our bound a and b
        for node in &egraph[eclass].nodes {
            if let ZIR::Reduce(BinOp::Add, [map_id]) = node {
                let map_class = egraph.find(*map_id);
                for map_node in &egraph[map_class].nodes {
                    if let ZIR::Map(_tag, [_dom_id, body_id]) = map_node {
                        let body_class = egraph.find(*body_id);
                        for body_node in &egraph[body_class].nodes {
                            if let ZIR::Mul([a, b]) = body_node
                                && egraph.find(*a) == a_class && egraph.find(*b) == b_class {
                                    // Create Dot(a, b) and union
                                    let dot = egraph.add(ZIR::Dot([a_class, b_class]));
                                    if egraph.union(eclass, dot) {
                                        return vec![dot];
                                    }
                                    return vec![];
                                }
                        }
                    }
                }
            }
        }
        vec![]
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
