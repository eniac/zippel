//! Constant propagation (vii).
//!
//! `(+ ?c1 ?c2)` → `?c3` (computed), `(* ?c1 ?c2)` → `?c3`, etc.
//!
//! Custom `Applier`: read `Value<C>` from both `Constant` operands,
//! compute result, create new `Constant(result_value)`. Guarded by
//! `Condition` that both children are `Constant` nodes.

use std::marker::PhantomData;

use super::v;
use crate::lang::{ZAnalysis, ZIR};
use backend::ArkConfig;
use egg::{Applier, EGraph, Id, PatternAst, Rewrite, SearchMatches, Subst, Symbol, Var};
use lang::ast::BinOp;

/// Check if a node is a binary op with both children being Constant.
/// Returns the BinOp and child e-class Ids if so.
fn extract_binop_with_consts<C: ArkConfig + std::fmt::Debug>(
    egraph: &EGraph<ZIR<C>, ZAnalysis<C>>,
    node: &ZIR<C>,
) -> Option<(BinOp, Id, Id)> {
    let (op, [a, b]) = match node {
        ZIR::Add(ids) => (BinOp::Add, *ids),
        ZIR::Sub(ids) => (BinOp::Sub, *ids),
        ZIR::Mul(ids) => (BinOp::Mul, *ids),
        ZIR::Div(ids) => (BinOp::Div, *ids),
        ZIR::Rem(ids) => (BinOp::Rem, *ids),
        ZIR::Pow(ids) => (BinOp::Pow, *ids),
        _ => return None,
    };

    let a_class = egraph.find(a);
    let b_class = egraph.find(b);

    // Both children must have a Constant node in their e-class
    let a_is_const = egraph[a_class]
        .nodes
        .iter()
        .any(|n| matches!(n, ZIR::Constant(_)));
    let b_is_const = egraph[b_class]
        .nodes
        .iter()
        .any(|n| matches!(n, ZIR::Constant(_)));

    if a_is_const && b_is_const {
        Some((op, a_class, b_class))
    } else {
        None
    }
}

/// Custom Searcher for constant propagation.
/// Walks e-classes looking for binary op nodes where both children
/// are `Constant` nodes.
/// Binds `?a` and `?b` to the two operand e-class Ids.
pub struct ConstPropSearcher<C: ArkConfig>(PhantomData<C>);

impl<C: ArkConfig + std::fmt::Debug> egg::Searcher<ZIR<C>, ZAnalysis<C>> for ConstPropSearcher<C> {
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
        for node in &egraph[eclass].nodes {
            if let Some((_, a_class, b_class)) = extract_binop_with_consts(egraph, node) {
                let mut subst = Subst::default();
                subst.insert(a_var, a_class);
                subst.insert(b_var, b_class);
                substs.push(subst);
                if substs.len() >= limit {
                    break;
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

/// Custom Applier for constant propagation.
/// Uses `?a` and `?b` from the Subst to find the specific binary op node,
/// reads `Value<C>` from both `Constant` operands, computes the result,
/// creates a new `Constant(result_value)`, unions with the matched e-class.
pub struct ConstPropApplier<C: ArkConfig>(PhantomData<C>);

impl<C: ArkConfig + std::fmt::Debug> Applier<ZIR<C>, ZAnalysis<C>> for ConstPropApplier<C> {
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

        // Find the specific op([a, b]) in this e-class matching our bindings
        for node in &egraph[eclass].nodes {
            let (op, [a, b]) = match node {
                ZIR::Add(ids) => (BinOp::Add, *ids),
                ZIR::Sub(ids) => (BinOp::Sub, *ids),
                ZIR::Mul(ids) => (BinOp::Mul, *ids),
                ZIR::Div(ids) => (BinOp::Div, *ids),
                ZIR::Rem(ids) => (BinOp::Rem, *ids),
                ZIR::Pow(ids) => (BinOp::Pow, *ids),
                _ => continue,
            };
            if egraph.find(a) != a_class || egraph.find(b) != b_class {
                continue;
            }

            // Extract Values from the Constant nodes
            let a_val = egraph[a_class].nodes.iter().find_map(|n| {
                if let ZIR::Constant(v) = n {
                    Some(v.clone())
                } else {
                    None
                }
            });
            let b_val = egraph[b_class].nodes.iter().find_map(|n| {
                if let ZIR::Constant(v) = n {
                    Some(v.clone())
                } else {
                    None
                }
            });

            let (Some(a_val), Some(b_val)) = (a_val, b_val) else {
                continue;
            };

            // Compute the result
            let result = match op {
                BinOp::Add => a_val + b_val,
                BinOp::Sub => a_val - b_val,
                BinOp::Mul => a_val * b_val,
                BinOp::Div => a_val / b_val,
                BinOp::Rem => a_val % b_val,
                BinOp::Pow => {
                    let mut result = b_val.clone();
                    a_val.value_pow(&mut result);
                    result
                }
                BinOp::Dot | BinOp::Concat => continue,
            };

            let const_id = egraph.add(ZIR::Constant(result));
            if egraph.union(eclass, const_id) {
                return vec![const_id];
            }
            return vec![];
        }
        vec![]
    }
}

pub fn rewrites<C: ArkConfig + std::fmt::Debug + Clone + 'static>()
-> Vec<Rewrite<ZIR<C>, ZAnalysis<C>>> {
    vec![
        Rewrite::new(
            "const-prop",
            ConstPropSearcher::<C>(PhantomData),
            ConstPropApplier::<C>(PhantomData),
        )
        .unwrap(),
    ]
}

#[cfg(test)]
mod tests {
    use backend::{ArkBls12_381, Value};
    use egg::{EGraph, Symbol};

    use super::super::test_utils::{ZEgraph, saturate};
    use crate::lang::ZIR;

    #[test]
    fn test_const_prop_add() {
        let mut eg: ZEgraph = EGraph::default();
        let a = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(3),
        )));
        let b = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(4),
        )));
        let add = eg.add(ZIR::Add([a, b]));

        saturate(&mut eg);

        let add_class = &eg[eg.find(add)];
        let has_seven = add_class.nodes.iter().any(|n| {
            matches!(n, ZIR::Constant(Value::Scalar(v))
                if v == &<ArkBls12_381 as backend::ArkConfig>::F::from(7))
        });
        assert!(has_seven, "const-prop should fold Add(3, 4) to Constant(7)");
    }

    #[test]
    fn test_const_prop_mul() {
        let mut eg: ZEgraph = EGraph::default();
        let a = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(5),
        )));
        let b = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(6),
        )));
        let mul = eg.add(ZIR::Mul([a, b]));

        saturate(&mut eg);

        let mul_class = &eg[eg.find(mul)];
        let has_thirty = mul_class.nodes.iter().any(|n| {
            matches!(n, ZIR::Constant(Value::Scalar(v))
                if v == &<ArkBls12_381 as backend::ArkConfig>::F::from(30))
        });
        assert!(
            has_thirty,
            "const-prop should fold Mul(5, 6) to Constant(30)"
        );
    }

    #[test]
    fn test_const_prop_sub() {
        let mut eg: ZEgraph = EGraph::default();
        let a = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(10),
        )));
        let b = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(3),
        )));
        let sub = eg.add(ZIR::Sub([a, b]));

        saturate(&mut eg);

        let sub_class = &eg[eg.find(sub)];
        let has_seven = sub_class.nodes.iter().any(|n| {
            matches!(n, ZIR::Constant(Value::Scalar(v))
                if v == &<ArkBls12_381 as backend::ArkConfig>::F::from(7))
        });
        assert!(
            has_seven,
            "const-prop should fold Sub(10, 3) to Constant(7)"
        );
    }

    #[test]
    fn test_const_prop_does_not_fire_on_non_constant() {
        let mut eg: ZEgraph = EGraph::default();
        let a = eg.add(ZIR::Constant(Value::Scalar(
            <ArkBls12_381 as backend::ArkConfig>::F::from(3),
        )));
        let var = eg.add(ZIR::Var(Symbol::from("x")));
        let add = eg.add(ZIR::Add([a, var]));

        saturate(&mut eg);

        let add_class = &eg[eg.find(add)];
        let has_constant = add_class
            .nodes
            .iter()
            .any(|n| matches!(n, ZIR::Constant(_)));
        assert!(
            !has_constant,
            "const-prop should NOT fire when one operand is not Constant"
        );
    }
}
