//! Record projection resolution rewrite (x).
//!
//! `(proj ?f (record ?names ?values))` → `?values[i]` where
//! `?names[i] == ?f`.
//!
//! Guarded by `!has_visible_side_effect` on the Record's e-class.
//! Dead record elimination is automatic via extraction (no rewrite needed).

use std::marker::PhantomData;

use crate::lang::{ZAnalysis, ZIR};
use backend::ArkConfig;
use egg::{Applier, EGraph, Id, PatternAst, Rewrite, SearchMatches, Subst, Symbol, Var};

/// A Record's field names and value e-class IDs.
type RecordData = (Box<[Symbol]>, Box<[Id]>);

/// Custom Applier for projection resolution.
/// Looks at the matched e-class's Proj nodes, finds matching Record children,
/// and unions the Proj's e-class with the corresponding value's e-class.
pub struct ProjApplier<C: ArkConfig>(PhantomData<C>);

impl<C: ArkConfig + std::fmt::Debug> Applier<ZIR<C>, ZAnalysis<C>> for ProjApplier<C> {
    fn apply_one(
        &self,
        egraph: &mut EGraph<ZIR<C>, ZAnalysis<C>>,
        eclass: Id,
        _subst: &Subst,
        _searcher_ast: Option<&PatternAst<ZIR<C>>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        // Collect all Proj e-nodes in this e-class
        let proj_nodes: Vec<(Symbol, Id)> = egraph[eclass]
            .nodes
            .iter()
            .filter_map(|n| {
                if let ZIR::Proj(field, [rec_id]) = n {
                    Some((*field, *rec_id))
                } else {
                    None
                }
            })
            .collect();

        let mut added = vec![];
        for (field, rec_id) in proj_nodes {
            let rec_class = egraph.find(rec_id);
            // Guard: no visible side effect on the record's e-class
            if egraph[rec_class].data.has_visible_side_effect {
                continue;
            }

            // Find a Record e-node in the record's e-class with matching field
            let rec_nodes: Vec<RecordData> = egraph[rec_class]
                .nodes
                .iter()
                .filter_map(|n| {
                    if let ZIR::Record(names, values) = n {
                        Some((names.clone(), values.clone()))
                    } else {
                        None
                    }
                })
                .collect();

            for (names, values) in rec_nodes {
                if let Some(idx) = names.iter().position(|n| *n == field)
                    && idx < values.len()
                {
                    let val_id = egraph.find(values[idx]);
                    if egraph.union(eclass, val_id) {
                        added.push(val_id);
                    }
                }
            }
        }
        added
    }
}

/// Custom Searcher for projection resolution.
/// Walks e-classes looking for `Proj(field, [Record(...)])` patterns.
pub struct ProjSearcher<C: ArkConfig>(PhantomData<C>);

impl<C: ArkConfig + std::fmt::Debug> egg::Searcher<ZIR<C>, ZAnalysis<C>> for ProjSearcher<C> {
    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph<ZIR<C>, ZAnalysis<C>>,
        eclass: Id,
        limit: usize,
    ) -> Option<SearchMatches<'_, ZIR<C>>> {
        let mut substs = vec![];
        for node in &egraph[eclass].nodes {
            if let ZIR::Proj(field, [rec_id]) = node {
                let rec_class = egraph.find(*rec_id);
                // Guard: no visible side effect
                if egraph[rec_class].data.has_visible_side_effect {
                    continue;
                }
                // Check if the record's e-class has a Record e-node
                // with a matching field name
                let has_match = egraph[rec_class].nodes.iter().any(|n| {
                    if let ZIR::Record(names, _) = n {
                        names.contains(field)
                    } else {
                        false
                    }
                });
                if has_match {
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

pub fn rewrites<C: ArkConfig + std::fmt::Debug + Clone + 'static>()
-> Vec<Rewrite<ZIR<C>, ZAnalysis<C>>> {
    vec![
        Rewrite::new(
            "proj-record",
            ProjSearcher::<C>(PhantomData),
            ProjApplier::<C>(PhantomData),
        )
        .unwrap(),
    ]
}
