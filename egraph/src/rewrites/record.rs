//! Record projection resolution rewrite (x).
//!
//! `(proj ?f (record ?names ?values))` → `?values[i]` where
//! `?names[i] == ?f`.
//!
//! Guarded by `!has_visible_side_effect` on the Record's e-class.
//! Dead record elimination is automatic via extraction (no rewrite needed).

use std::marker::PhantomData;

use super::v;
use crate::lang::{ZAnalysis, ZIR};
use backend::ArkConfig;
use egg::{Applier, EGraph, Id, PatternAst, Rewrite, SearchMatches, Subst, Symbol, Var};

/// Custom Searcher for projection resolution.
/// Walks e-classes looking for `Proj(field, [Record(...)])` patterns.
/// Binds `?rec` to the Record child's e-class Id for each match.
pub struct ProjSearcher<C: ArkConfig>(PhantomData<C>);

impl<C: ArkConfig + std::fmt::Debug> egg::Searcher<ZIR<C>, ZAnalysis<C>> for ProjSearcher<C> {
    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph<ZIR<C>, ZAnalysis<C>>,
        eclass: Id,
        limit: usize,
    ) -> Option<SearchMatches<'_, ZIR<C>>> {
        if limit == 0 {
            return None;
        }
        let rec_var = v("?rec");
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
                    let mut subst = Subst::default();
                    subst.insert(rec_var, rec_class);
                    substs.push(subst);
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
        vec![v("?rec")]
    }
}

/// Custom Applier for projection resolution.
/// Uses `?rec` from the Subst to find the specific Proj(field, [?rec]) node,
/// extracts the field name, finds the matching value in the Record, and
/// unions the Proj's e-class with the value's e-class.
pub struct ProjApplier<C: ArkConfig>(PhantomData<C>);

impl<C: ArkConfig + std::fmt::Debug> Applier<ZIR<C>, ZAnalysis<C>> for ProjApplier<C> {
    fn apply_one(
        &self,
        egraph: &mut EGraph<ZIR<C>, ZAnalysis<C>>,
        eclass: Id,
        subst: &Subst,
        _searcher_ast: Option<&PatternAst<ZIR<C>>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        let rec_class = egraph.find(subst[v("?rec")]);

        // Find the specific Proj(field, [rec]) in this e-class
        // that references our bound record e-class
        for node in &egraph[eclass].nodes {
            if let ZIR::Proj(field, [rec_id]) = node {
                if egraph.find(*rec_id) != rec_class {
                    continue;
                }
                // Find the matching Record in rec's e-class
                for rec_node in &egraph[rec_class].nodes {
                    if let ZIR::Record(names, values) = rec_node
                        && let Some(idx) = names.iter().position(|n| *n == *field)
                        && idx < values.len()
                    {
                        let val_id = egraph.find(values[idx]);
                        if egraph.union(eclass, val_id) {
                            return vec![val_id];
                        }
                        return vec![];
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
            "proj-record",
            ProjSearcher::<C>(PhantomData),
            ProjApplier::<C>(PhantomData),
        )
        .unwrap(),
    ]
}

#[cfg(test)]
mod tests {
    use backend::{ArkBls12_381, Value};
    use egg::{EGraph, Id, Symbol};

    use super::super::test_utils::{ZEgraph, saturate};
    use crate::lang::ZIR;

    #[test]
    fn test_proj_record_resolution() {
        let mut eg: ZEgraph = EGraph::default();
        let x = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(1),
        )));
        let y = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(2),
        )));
        let names: Box<[Symbol]> = vec![Symbol::from("a"), Symbol::from("b")].into_boxed_slice();
        let values: Box<[Id]> = vec![x, y].into_boxed_slice();
        let record = eg.add(ZIR::Record(names, values));
        let proj_a = eg.add(ZIR::Proj(Symbol::from("a"), [record]));

        saturate(&mut eg);

        assert_eq!(
            eg.find(proj_a),
            eg.find(x),
            "proj-record should unify Proj(\"a\", record) with x"
        );
    }

    #[test]
    fn test_proj_record_resolution_second_field() {
        let mut eg: ZEgraph = EGraph::default();
        let x = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(1),
        )));
        let y = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(2),
        )));
        let names: Box<[Symbol]> = vec![Symbol::from("a"), Symbol::from("b")].into_boxed_slice();
        let values: Box<[Id]> = vec![x, y].into_boxed_slice();
        let record = eg.add(ZIR::Record(names, values));
        let proj_b = eg.add(ZIR::Proj(Symbol::from("b"), [record]));

        saturate(&mut eg);

        assert_eq!(
            eg.find(proj_b),
            eg.find(y),
            "proj-record should unify Proj(\"b\", record) with y"
        );
    }

    #[test]
    fn test_proj_record_blocked_by_side_effect() {
        let mut eg: ZEgraph = EGraph::default();
        let challenge = eg.add(ZIR::Challenge(Symbol::from("c1"), false));
        let y = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(2),
        )));
        let names: Box<[Symbol]> = vec![Symbol::from("a"), Symbol::from("b")].into_boxed_slice();
        let values: Box<[Id]> = vec![challenge, y].into_boxed_slice();
        let record = eg.add(ZIR::Record(names, values));
        let proj_a = eg.add(ZIR::Proj(Symbol::from("a"), [record]));

        saturate(&mut eg);

        assert_ne!(
            eg.find(proj_a),
            eg.find(challenge),
            "proj-record should NOT resolve when record has visible side effect"
        );
    }
}
