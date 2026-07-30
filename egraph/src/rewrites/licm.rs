//! Loop-invariant code motion (LICM, rewrite xi).
//!
//! `Map(?tag, [?dom, op(?e, ?rest)])` →
//! `op(?e, Map(?tag, [?dom, ?rest]))`.
//!
//! Checks **both** operands of the binary op: whichever is loop-invariant
//! (free_vars doesn't contain `?tag`) and side-effect-free gets lifted.
//! The other operand stays inside the Map.
//!
//! Conditions: (1) lifted operand's free_vars doesn't contain `?tag`
//! (loop-invariant), (2) lifted operand's `has_side_effect == false`
//! (includes Random — lifting Random changes N draws to 1),
//! (3) op is broadcasting-permitting: Add/Sub/Mul/Div/Rem/Pow/Pair.
//!
//! Broadcast (iii) is a sub-case: when `?e` is a scalar `?m` and `?rest`
//! is `?vec`, LICM produces `Mul(?m, Map(?tag, [?dom, ?vec]))`, which is
//! the broadcast result. No separate broadcast rewrite needed.

use std::marker::PhantomData;

use super::v;
use crate::lang::{ZAnalysis, ZIR};
use backend::ArkConfig;
use egg::{Applier, EGraph, Id, PatternAst, Rewrite, SearchMatches, Subst, Symbol, Var};

/// Extract (op_name, [a_id, b_id]) from a broadcasting-permitting binary op
/// node (Add/Sub/Mul/Div/Rem/Pow/Pair).
fn extract_binop(node: &ZIR<impl ArkConfig>) -> Option<(&'static str, [Id; 2])> {
    match node {
        ZIR::Add(ids) => Some(("Add", *ids)),
        ZIR::Sub(ids) => Some(("Sub", *ids)),
        ZIR::Mul(ids) => Some(("Mul", *ids)),
        ZIR::Div(ids) => Some(("Div", *ids)),
        ZIR::Rem(ids) => Some(("Rem", *ids)),
        ZIR::Pow(ids) => Some(("Pow", *ids)),
        ZIR::Pair(ids) => Some(("Pair", *ids)),
        _ => None,
    }
}

/// Reconstruct a binary op ZIR node from its variant name and children.
fn make_binop<C: ArkConfig>(op: &str, children: [Id; 2]) -> ZIR<C> {
    match op {
        "Add" => ZIR::Add(children),
        "Sub" => ZIR::Sub(children),
        "Mul" => ZIR::Mul(children),
        "Div" => ZIR::Div(children),
        "Rem" => ZIR::Rem(children),
        "Pow" => ZIR::Pow(children),
        "Pair" => ZIR::Pair(children),
        _ => unreachable!("invalid binop in LICM"),
    }
}

/// Check if an e-class is loop-invariant and side-effect-free.
fn is_liftable<C: ArkConfig + std::fmt::Debug>(
    egraph: &EGraph<ZIR<C>, ZAnalysis<C>>,
    e_class: Id,
    tag: &Symbol,
) -> bool {
    let data = &egraph[e_class].data;
    !data.free_vars.contains(tag) && !data.has_side_effect
}

/// Custom Searcher for LICM.
/// Walks e-classes looking for `Map(tag, [dom, op([a, b])])` where:
/// - op is Add/Sub/Mul/Div/Rem/Pow/Pair
/// - at least one operand is loop-invariant (free_vars doesn't contain tag)
///   and side-effect-free
///
/// Binds `?dom`, `?invariant` (the lifted operand), `?rest` (the remaining
/// operand), and `?which` (0 or 1 — which operand is the invariant one).
pub struct LicmSearcher<C: ArkConfig>(PhantomData<C>);

impl<C: ArkConfig + std::fmt::Debug> egg::Searcher<ZIR<C>, ZAnalysis<C>> for LicmSearcher<C> {
    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph<ZIR<C>, ZAnalysis<C>>,
        eclass: Id,
        limit: usize,
    ) -> Option<SearchMatches<'_, ZIR<C>>> {
        if limit == 0 {
            return None;
        }
        let dom_var = v("?dom");
        let inv_var = v("?invariant");
        let rest_var = v("?rest");
        let which_var = v("?which");
        let mut substs = vec![];
        'outer: for node in &egraph[eclass].nodes {
            if let ZIR::Map(tag, [dom_id, body_id]) = node {
                let dom_class = egraph.find(*dom_id);
                let body_class = egraph.find(*body_id);

                for body_node in &egraph[body_class].nodes {
                    if let Some((_, [a_id, b_id])) = extract_binop(body_node) {
                        let a_class = egraph.find(a_id);
                        let b_class = egraph.find(b_id);

                        // Check which operand is liftable
                        let a_liftable = is_liftable(egraph, a_class, tag);
                        let b_liftable = is_liftable(egraph, b_class, tag);
                        if !a_liftable && !b_liftable {
                            continue;
                        }

                        // Prefer lifting the first operand if both are liftable.
                        let (inv_class, rest_class, which) = if a_liftable {
                            (a_class, b_class, 0usize)
                        } else {
                            (b_class, a_class, 1usize)
                        };

                        let mut subst = Subst::default();
                        subst.insert(dom_var, dom_class);
                        subst.insert(inv_var, inv_class);
                        subst.insert(rest_var, rest_class);
                        subst.insert(which_var, Id::from(which));
                        substs.push(subst);
                        if substs.len() >= limit {
                            break 'outer;
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
        vec![v("?dom"), v("?invariant"), v("?rest"), v("?which")]
    }
}

/// Custom Applier for LICM.
/// Uses `?dom`, `?invariant`, `?rest`, `?which` from the Subst to find the
/// specific `Map(tag, [dom, op([a, b])])` node, creates
/// `op(invariant, Map(tag, [dom, rest]))`, unions with the matched e-class.
pub struct LicmApplier<C: ArkConfig>(PhantomData<C>);

impl<C: ArkConfig + std::fmt::Debug> Applier<ZIR<C>, ZAnalysis<C>> for LicmApplier<C> {
    fn apply_one(
        &self,
        egraph: &mut EGraph<ZIR<C>, ZAnalysis<C>>,
        eclass: Id,
        subst: &Subst,
        _searcher_ast: Option<&PatternAst<ZIR<C>>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        let dom_class = egraph.find(subst[v("?dom")]);
        let inv_class = egraph.find(subst[v("?invariant")]);
        let rest_class = egraph.find(subst[v("?rest")]);
        let which: usize = subst[v("?which")].into();

        // Find the specific Map(tag, [dom, body]) in this e-class
        // where body has op([a, b]) matching our bindings
        for node in &egraph[eclass].nodes {
            if let ZIR::Map(tag, [dom_id, body_id]) = node {
                if egraph.find(*dom_id) != dom_class {
                    continue;
                }
                let body_class = egraph.find(*body_id);
                for body_node in &egraph[body_class].nodes {
                    if let Some((op_name, [a_id, b_id])) = extract_binop(body_node) {
                        let a = egraph.find(a_id);
                        let b = egraph.find(b_id);
                        // Match based on which operand is the invariant
                        let (inv_match, rest_match) = if which == 0 {
                            (a == inv_class, b == rest_class)
                        } else {
                            (b == inv_class, a == rest_class)
                        };
                        if inv_match && rest_match {
                            // Build Map(tag, [dom, rest])
                            let new_map = egraph.add(ZIR::Map(*tag, [dom_class, rest_class]));
                            // Build op(invariant, new_map) — preserving operand order
                            let new_op = if which == 0 {
                                egraph.add(make_binop::<C>(op_name, [inv_class, new_map]))
                            } else {
                                egraph.add(make_binop::<C>(op_name, [new_map, inv_class]))
                            };

                            if egraph.union(eclass, new_op) {
                                return vec![new_op];
                            }
                            return vec![];
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
            "licm",
            LicmSearcher::<C>(PhantomData),
            LicmApplier::<C>(PhantomData),
        )
        .unwrap(),
    ]
}

#[cfg(test)]
mod tests {
    use ark_ff::Zero;
    use backend::{ArkBls12_381, Value};
    use egg::{EGraph, Symbol};

    use super::super::test_utils::{ZEgraph, saturate};
    use crate::lang::ZIR;

    #[test]
    fn test_licm_lifts_scalar_from_map() {
        let mut eg: ZEgraph = EGraph::default();

        let m = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(42),
        )));
        let dom = eg.add(ZIR::Constant(Value::VecScalar(vec![
            <ArkBls12_381 as backend::ArkConfig>::F::from(0),
            <ArkBls12_381 as backend::ArkConfig>::F::from(1),
            <ArkBls12_381 as backend::ArkConfig>::F::from(2),
        ])));
        let tag = Symbol::from("i");
        let var_i = eg.add(ZIR::Var(tag));
        let body = eg.add(ZIR::Add([m, var_i]));
        let map = eg.add(ZIR::Map(tag, [dom, body]));

        saturate(&mut eg);

        let map_class = &eg[eg.find(map)];
        let has_lifted_add = map_class.nodes.iter().any(|n| {
            if let ZIR::Add([a, b]) = n {
                let a_class = &eg[eg.find(*a)];
                let a_is_scalar = a_class.nodes.iter().any(|an| {
                    matches!(an, ZIR::Constant(Value::Scalar(v))
                        if v == &<ArkBls12_381 as backend::ArkConfig>::F::from(42))
                });
                let b_class = &eg[eg.find(*b)];
                let b_is_map = b_class.nodes.iter().any(|bn| matches!(bn, ZIR::Map(_, _)));
                a_is_scalar && b_is_map
            } else {
                false
            }
        });
        assert!(
            has_lifted_add,
            "LICM should produce Add(m, Map(tag, [dom, Var(tag)])) in the map e-class"
        );
    }

    #[test]
    fn test_licm_blocked_by_random() {
        let mut eg: ZEgraph = EGraph::default();

        let r = eg.add(ZIR::Random(Symbol::from("r1"), false));
        let dom = eg.add(ZIR::Constant(Value::VecScalar(vec![
            <ArkBls12_381 as backend::ArkConfig>::F::from(0),
            <ArkBls12_381 as backend::ArkConfig>::F::from(1),
        ])));
        let tag = Symbol::from("i");
        let var_i = eg.add(ZIR::Var(tag));
        let body = eg.add(ZIR::Add([r, var_i]));
        let map = eg.add(ZIR::Map(tag, [dom, body]));

        saturate(&mut eg);

        let map_class = &eg[eg.find(map)];
        let has_lifted = map_class.nodes.iter().any(|n| {
            if let ZIR::Add([a, b]) = n {
                let a_class = &eg[eg.find(*a)];
                let a_is_random = a_class
                    .nodes
                    .iter()
                    .any(|an| matches!(an, ZIR::Random(_, _)));
                let b_class = &eg[eg.find(*b)];
                let b_is_map = b_class.nodes.iter().any(|bn| matches!(bn, ZIR::Map(_, _)));
                a_is_random && b_is_map
            } else {
                false
            }
        });
        assert!(
            !has_lifted,
            "LICM should NOT lift Random out of Map (has_side_effect blocks it)"
        );
    }

    #[test]
    fn test_licm_blocked_by_loop_variant() {
        let mut eg: ZEgraph = EGraph::default();

        let tag = Symbol::from("i");
        let var_i = eg.add(ZIR::Var(tag));
        let dom = eg.add(ZIR::Constant(Value::VecScalar(vec![
            <ArkBls12_381 as backend::ArkConfig>::F::from(0),
            <ArkBls12_381 as backend::ArkConfig>::F::from(1),
        ])));
        let body = eg.add(ZIR::Add([var_i, var_i]));
        let map = eg.add(ZIR::Map(tag, [dom, body]));

        saturate(&mut eg);

        let map_class = &eg[eg.find(map)];
        let has_lifted = map_class.nodes.iter().any(|n| {
            if let ZIR::Add([a, b]) = n {
                let b_class = &eg[eg.find(*b)];
                let b_is_map = b_class.nodes.iter().any(|bn| matches!(bn, ZIR::Map(_, _)));
                let a_class = &eg[eg.find(*a)];
                let a_is_var = a_class.nodes.iter().any(|an| matches!(an, ZIR::Var(_)));
                a_is_var && b_is_map
            } else {
                false
            }
        });
        assert!(
            !has_lifted,
            "LICM should NOT lift Var(tag) out of Map (not loop-invariant)"
        );
    }

    #[test]
    fn test_licm_lifts_second_operand() {
        let mut eg: ZEgraph = EGraph::default();

        let m = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(42),
        )));
        let dom = eg.add(ZIR::Constant(Value::VecScalar(vec![
            <ArkBls12_381 as backend::ArkConfig>::F::from(0),
            <ArkBls12_381 as backend::ArkConfig>::F::from(1),
        ])));
        let tag = Symbol::from("i");
        let var_i = eg.add(ZIR::Var(tag));
        let body = eg.add(ZIR::Sub([var_i, m]));
        let map = eg.add(ZIR::Map(tag, [dom, body]));

        saturate(&mut eg);

        let map_class = &eg[eg.find(map)];
        let has_lifted = map_class.nodes.iter().any(|n| {
            if let ZIR::Sub([a, b]) = n {
                let a_class = &eg[eg.find(*a)];
                let a_is_map = a_class.nodes.iter().any(|bn| matches!(bn, ZIR::Map(_, _)));
                let b_class = &eg[eg.find(*b)];
                let b_is_scalar = b_class.nodes.iter().any(|bn| {
                    matches!(bn, ZIR::Constant(Value::Scalar(v))
                        if v == &<ArkBls12_381 as backend::ArkConfig>::F::from(42))
                });
                a_is_map && b_is_scalar
            } else {
                false
            }
        });
        assert!(
            has_lifted,
            "LICM should lift second operand: Sub(Map(tag, [dom, Var(tag)]), m)"
        );
    }

    #[test]
    fn test_licm_rem() {
        let mut eg: ZEgraph = EGraph::default();

        let m = eg.add(ZIR::Constant(Value::Index(7)));
        let dom = eg.add(ZIR::Constant(Value::VecIndex(vec![0, 1, 2, 3])));
        let tag = Symbol::from("i");
        let var_i = eg.add(ZIR::Var(tag));
        let body = eg.add(ZIR::Rem([var_i, m]));
        let map = eg.add(ZIR::Map(tag, [dom, body]));

        saturate(&mut eg);

        let map_class = &eg[eg.find(map)];
        let has_lifted = map_class.nodes.iter().any(|n| {
            if let ZIR::Rem([a, b]) = n {
                let a_class = &eg[eg.find(*a)];
                let a_is_map = a_class.nodes.iter().any(|bn| matches!(bn, ZIR::Map(_, _)));
                let b_class = &eg[eg.find(*b)];
                let b_is_const = b_class
                    .nodes
                    .iter()
                    .any(|bn| matches!(bn, ZIR::Constant(Value::Index(7))));
                a_is_map && b_is_const
            } else {
                false
            }
        });
        assert!(has_lifted, "LICM should lift Rem's invariant operand");
    }

    #[test]
    fn test_licm_pow() {
        let mut eg: ZEgraph = EGraph::default();

        let exp = eg.add(ZIR::Constant(Value::Index(3)));
        let dom = eg.add(ZIR::Constant(Value::VecIndex(vec![0, 1, 2])));
        let tag = Symbol::from("i");
        let var_i = eg.add(ZIR::Var(tag));
        let body = eg.add(ZIR::Pow([var_i, exp]));
        let map = eg.add(ZIR::Map(tag, [dom, body]));

        saturate(&mut eg);

        let map_class = &eg[eg.find(map)];
        let has_lifted = map_class.nodes.iter().any(|n| {
            if let ZIR::Pow([a, b]) = n {
                let a_class = &eg[eg.find(*a)];
                let a_is_map = a_class.nodes.iter().any(|bn| matches!(bn, ZIR::Map(_, _)));
                let b_class = &eg[eg.find(*b)];
                let b_is_const = b_class
                    .nodes
                    .iter()
                    .any(|bn| matches!(bn, ZIR::Constant(Value::Index(3))));
                a_is_map && b_is_const
            } else {
                false
            }
        });
        assert!(has_lifted, "LICM should lift Pow's invariant operand");
    }

    #[test]
    fn test_licm_pow_lifts_base() {
        let mut eg: ZEgraph = EGraph::default();

        let base = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(2),
        )));
        let dom = eg.add(ZIR::Constant(Value::VecIndex(vec![0, 1, 2])));
        let tag = Symbol::from("i");
        let var_i = eg.add(ZIR::Var(tag));
        let body = eg.add(ZIR::Pow([base, var_i]));
        let map = eg.add(ZIR::Map(tag, [dom, body]));

        saturate(&mut eg);

        let map_class = &eg[eg.find(map)];
        let has_lifted = map_class.nodes.iter().any(|n| {
            if let ZIR::Pow([a, b]) = n {
                let a_class = &eg[eg.find(*a)];
                let a_is_scalar = a_class.nodes.iter().any(|an| {
                    matches!(an, ZIR::Constant(Value::Scalar(v))
                        if v == &<ArkBls12_381 as backend::ArkConfig>::F::from(2))
                });
                let b_class = &eg[eg.find(*b)];
                let b_is_map = b_class.nodes.iter().any(|bn| matches!(bn, ZIR::Map(_, _)));
                a_is_scalar && b_is_map
            } else {
                false
            }
        });
        assert!(
            has_lifted,
            "LICM should lift Pow's base: Pow(scalar, Map(...)) is now valid"
        );
    }

    #[test]
    fn test_licm_pair() {
        let mut eg: ZEgraph = EGraph::default();

        let g1 = eg.add(ZIR::Constant(Value::G1(
            <ArkBls12_381 as backend::ArkConfig>::G1::zero(),
        )));
        let dom = eg.add(ZIR::Constant(Value::VecScalar(vec![
            <ArkBls12_381 as backend::ArkConfig>::F::from(0),
            <ArkBls12_381 as backend::ArkConfig>::F::from(1),
        ])));
        let tag = Symbol::from("i");
        let var_i = eg.add(ZIR::Var(tag));
        let body = eg.add(ZIR::Pair([g1, var_i]));
        let map = eg.add(ZIR::Map(tag, [dom, body]));

        saturate(&mut eg);

        let map_class = &eg[eg.find(map)];
        let has_lifted = map_class.nodes.iter().any(|n| {
            if let ZIR::Pair([a, b]) = n {
                let a_class = &eg[eg.find(*a)];
                let a_is_g1 = a_class
                    .nodes
                    .iter()
                    .any(|an| matches!(an, ZIR::Constant(Value::G1(_))));
                let b_class = &eg[eg.find(*b)];
                let b_is_map = b_class.nodes.iter().any(|bn| matches!(bn, ZIR::Map(_, _)));
                a_is_g1 && b_is_map
            } else {
                false
            }
        });
        assert!(has_lifted, "LICM should lift Pair's invariant G1 operand");
    }
}
