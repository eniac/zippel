//! Pairing rewrite (i).
//!
//! `(assert (pair ?a ?b) (pair ?c ?d))` →
//! `(assert (dot (vec ?a (neg ?c)) (vec ?b ?d)) (constant "gt_zero"))`.
//!
//! Generalizes to N pairings: lhs and rhs can be single Pair nodes or
//! Add-chained Pair sums. Collects all pairs from both sides.
//!
//! The pairing product equation:
//! `e(a1,b1)*e(a2,b2) = e(c1,d1)*e(c2,d2)`
//! Two equivalent Dot forms are unioned (negating G1s, which is cheaper
//! than negating G2s since G1 points are over a smaller field):
//! - `dot([lhs_g1s ++ neg(rhs_g1s)], [lhs_g2s ++ rhs_g2s])` — negate RHS G1s
//! - `dot([neg(lhs_g1s) ++ rhs_g1s], [lhs_g2s ++ rhs_g2s])` — negate LHS G1s
//!
//! Both are valid because `e(-x, y) = e(x, -y) = -e(x, y)`.
//!
//! Works for both `Assert` (prover) and `Verify` (verifier).

use std::marker::PhantomData;

use super::v;
use crate::lang::{ZAnalysis, ZIR};
use backend::{ATyp, ArkConfig, Value};
use egg::{Applier, EGraph, Id, PatternAst, Rewrite, SearchMatches, Subst, Symbol, Var};

/// Collect ALL valid pair collections from a single e-node.
/// Each inner `Vec<[Id; 2]>` is one valid decomposition into pairs.
///
/// - `Pair([a, b])` → one collection: `[[a, b]]`
/// - `Add([a, b])` → cartesian product of collections from both children
/// - anything else → no collections (empty)
fn collect_pairs<C: ArkConfig + std::fmt::Debug>(
    egraph: &EGraph<ZIR<C>, ZAnalysis<C>>,
    node: &ZIR<C>,
) -> Vec<Vec<[Id; 2]>> {
    match node {
        ZIR::Pair([a, b]) => vec![vec![[*a, *b]]],
        ZIR::Add([a, b]) => {
            let a_cols = all_pairs_from_class(egraph, *a);
            let b_cols = all_pairs_from_class(egraph, *b);
            // Cartesian product: each a_col ++ each b_col
            a_cols
                .iter()
                .flat_map(|a_col| {
                    b_cols.iter().map(move |b_col| {
                        let mut combined = a_col.clone();
                        combined.extend(b_col.iter().copied());
                        combined
                    })
                })
                .collect()
        }
        _ => vec![],
    }
}

/// Drive `collect_pairs` over all e-nodes in an e-class.
/// Returns all valid pair collections from every interpretation.
fn all_pairs_from_class<C: ArkConfig + std::fmt::Debug>(
    egraph: &EGraph<ZIR<C>, ZAnalysis<C>>,
    class_id: Id,
) -> Vec<Vec<[Id; 2]>> {
    let class_id = egraph.find(class_id);
    egraph[class_id]
        .nodes
        .iter()
        .flat_map(|node| collect_pairs(egraph, node))
        .collect()
}

/// Custom Searcher for the pairing rewrite.
/// Walks e-classes looking for `Assert(lhs, rhs)` or `Verify(lhs, rhs)`
/// where both lhs and rhs are pair sums (single Pair or Add-chained Pairs).
/// Binds `?lhs` and `?rhs` to the Assert/Verify's two child e-class Ids.
pub struct PairingSearcher<C: ArkConfig>(PhantomData<C>);

impl<C: ArkConfig + std::fmt::Debug> egg::Searcher<ZIR<C>, ZAnalysis<C>> for PairingSearcher<C> {
    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph<ZIR<C>, ZAnalysis<C>>,
        eclass: Id,
        limit: usize,
    ) -> Option<SearchMatches<'_, ZIR<C>>> {
        if limit == 0 {
            return None;
        }
        let lhs_var = v("?lhs");
        let rhs_var = v("?rhs");
        let mut substs = vec![];
        for node in &egraph[eclass].nodes {
            if let ZIR::Assert([lhs, rhs]) | ZIR::Verify([lhs, rhs]) = node {
                let lhs_class = egraph.find(*lhs);
                let rhs_class = egraph.find(*rhs);
                // Both sides must have at least one valid pair collection
                if !all_pairs_from_class(egraph, lhs_class).is_empty()
                    && !all_pairs_from_class(egraph, rhs_class).is_empty()
                {
                    let mut subst = Subst::default();
                    subst.insert(lhs_var, lhs_class);
                    subst.insert(rhs_var, rhs_class);
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
        vec![v("?lhs"), v("?rhs")]
    }
}

/// Custom Applier for the pairing rewrite.
/// Collects all pair collections from both sides, builds the two Dot
/// forms (negate RHS G1s, negate LHS G1s) for each collection, and
/// unions all with the matched e-class.
pub struct PairingApplier<C: ArkConfig>(PhantomData<C>);

impl<C: ArkConfig + std::fmt::Debug> Applier<ZIR<C>, ZAnalysis<C>> for PairingApplier<C> {
    fn apply_one(
        &self,
        egraph: &mut EGraph<ZIR<C>, ZAnalysis<C>>,
        eclass: Id,
        subst: &Subst,
        _searcher_ast: Option<&PatternAst<ZIR<C>>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        let lhs_class = egraph.find(subst[v("?lhs")]);
        let rhs_class = egraph.find(subst[v("?rhs")]);

        // Determine whether this is Assert or Verify
        let is_assert = egraph[eclass].nodes.iter().any(|n| {
            if let ZIR::Assert([a, b]) = n {
                egraph.find(*a) == lhs_class && egraph.find(*b) == rhs_class
            } else {
                false
            }
        });
        let is_verify = egraph[eclass].nodes.iter().any(|n| {
            if let ZIR::Verify([a, b]) = n {
                egraph.find(*a) == lhs_class && egraph.find(*b) == rhs_class
            } else {
                false
            }
        });
        if !is_assert && !is_verify {
            return vec![];
        }

        // Collect all pair collections from both sides
        let lhs_collections = all_pairs_from_class(egraph, lhs_class);
        let rhs_collections = all_pairs_from_class(egraph, rhs_class);
        if lhs_collections.is_empty() || rhs_collections.is_empty() {
            return vec![];
        }

        // GT zero constant (shared across all forms)
        let gt_zero = egraph.add(ZIR::Constant(Value::zero(&ATyp::gt())));

        let mut added = vec![];

        // For each (lhs_col, rhs_col) combination, build both Dot forms
        for lhs_pairs in &lhs_collections {
            for rhs_pairs in &rhs_collections {
                // All G2s: lhs_g2s ++ rhs_g2s (same for both forms)
                let mut all_g2s: Vec<Id> = lhs_pairs.iter().map(|p| egraph.find(p[1])).collect();
                all_g2s.extend(rhs_pairs.iter().map(|p| egraph.find(p[1])));
                let vec_g2 = egraph.add(ZIR::Vec(all_g2s.into_boxed_slice()));

                // Form 1: negate RHS G1s
                // dot([lhs_g1s ++ neg(rhs_g1s)], [all_g2s])
                let lhs_g1s: Vec<Id> = lhs_pairs.iter().map(|p| egraph.find(p[0])).collect();
                let neg_rhs_g1s: Vec<Id> = rhs_pairs
                    .iter()
                    .map(|p| egraph.add(ZIR::Neg([egraph.find(p[0])])))
                    .collect();
                let mut form1_g1s = lhs_g1s;
                form1_g1s.extend(neg_rhs_g1s);
                let vec_g1_f1 = egraph.add(ZIR::Vec(form1_g1s.into_boxed_slice()));
                let dot_f1 = egraph.add(ZIR::Dot([vec_g1_f1, vec_g2]));

                // Form 2: negate LHS G1s
                // dot([neg(lhs_g1s) ++ rhs_g1s], [all_g2s])
                let neg_lhs_g1s: Vec<Id> = lhs_pairs
                    .iter()
                    .map(|p| egraph.add(ZIR::Neg([egraph.find(p[0])])))
                    .collect();
                let rhs_g1s: Vec<Id> = rhs_pairs.iter().map(|p| egraph.find(p[0])).collect();
                let mut form2_g1s = neg_lhs_g1s;
                form2_g1s.extend(rhs_g1s);
                let vec_g1_f2 = egraph.add(ZIR::Vec(form2_g1s.into_boxed_slice()));
                let dot_f2 = egraph.add(ZIR::Dot([vec_g1_f2, vec_g2]));

                // Build Assert or Verify for both forms
                let make_node = |dot: Id| -> ZIR<C> {
                    if is_assert {
                        ZIR::Assert([dot, gt_zero])
                    } else {
                        ZIR::Verify([dot, gt_zero])
                    }
                };
                let node_f1 = egraph.add(make_node(dot_f1));
                let node_f2 = egraph.add(make_node(dot_f2));

                if egraph.union(eclass, node_f1) {
                    added.push(node_f1);
                }
                if egraph.union(eclass, node_f2) {
                    added.push(node_f2);
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
            "pairing",
            PairingSearcher::<C>(PhantomData),
            PairingApplier::<C>(PhantomData),
        )
        .unwrap(),
    ]
}

#[cfg(test)]
mod tests {
    use ark_ff::Zero;
    use backend::{ArkBls12_381, Value};
    use egg::EGraph;

    use super::super::test_utils::{ZEgraph, saturate};
    use crate::lang::ZIR;

    #[test]
    fn test_pairing_rewrite() {
        let mut eg: ZEgraph = EGraph::default();

        let g1_a = eg.add(ZIR::Constant(Value::G1(
            <ArkBls12_381 as backend::ArkConfig>::G1::zero(),
        )));
        let g2_b = eg.add(ZIR::Constant(Value::G2(
            <ArkBls12_381 as backend::ArkConfig>::G2::zero(),
        )));
        let g1_c = eg.add(ZIR::Constant(Value::G1(
            <ArkBls12_381 as backend::ArkConfig>::G1::zero(),
        )));
        let g2_d = eg.add(ZIR::Constant(Value::G2(
            <ArkBls12_381 as backend::ArkConfig>::G2::zero(),
        )));

        let pair1 = eg.add(ZIR::Pair([g1_a, g2_b]));
        let pair2 = eg.add(ZIR::Pair([g1_c, g2_d]));
        let assert = eg.add(ZIR::Assert([pair1, pair2]));

        saturate(&mut eg);

        let assert_class = &eg[eg.find(assert)];
        let has_dot_assert = assert_class.nodes.iter().any(|n| {
            if let ZIR::Assert([dot, _gt_zero]) = n {
                let dot_class = &eg[eg.find(*dot)];
                dot_class.nodes.iter().any(|dn| matches!(dn, ZIR::Dot(_)))
            } else {
                false
            }
        });
        assert!(
            has_dot_assert,
            "pairing rewrite should produce Assert(Dot(...), Constant(GT_zero))"
        );

        let has_dot_with_vecs = assert_class.nodes.iter().any(|n| {
            if let ZIR::Assert([dot, _]) = n {
                let dot_class = &eg[eg.find(*dot)];
                dot_class.nodes.iter().any(|dn| {
                    if let ZIR::Dot([a, b]) = dn {
                        let a_class = &eg[eg.find(*a)];
                        let b_class = &eg[eg.find(*b)];
                        a_class.nodes.iter().any(|vn| matches!(vn, ZIR::Vec(_)))
                            && b_class.nodes.iter().any(|vn| matches!(vn, ZIR::Vec(_)))
                    } else {
                        false
                    }
                })
            } else {
                false
            }
        });
        assert!(
            has_dot_with_vecs,
            "pairing rewrite Dot should have Vec children"
        );
    }

    #[test]
    fn test_pairing_rewrite_verify() {
        let mut eg: ZEgraph = EGraph::default();

        let g1_a = eg.add(ZIR::Constant(Value::G1(
            <ArkBls12_381 as backend::ArkConfig>::G1::zero(),
        )));
        let g2_b = eg.add(ZIR::Constant(Value::G2(
            <ArkBls12_381 as backend::ArkConfig>::G2::zero(),
        )));
        let g1_c = eg.add(ZIR::Constant(Value::G1(
            <ArkBls12_381 as backend::ArkConfig>::G1::zero(),
        )));
        let g2_d = eg.add(ZIR::Constant(Value::G2(
            <ArkBls12_381 as backend::ArkConfig>::G2::zero(),
        )));

        let pair1 = eg.add(ZIR::Pair([g1_a, g2_b]));
        let pair2 = eg.add(ZIR::Pair([g1_c, g2_d]));
        let verify = eg.add(ZIR::Verify([pair1, pair2]));

        saturate(&mut eg);

        let verify_class = &eg[eg.find(verify)];
        let has_dot_verify = verify_class.nodes.iter().any(|n| {
            if let ZIR::Verify([dot, _gt_zero]) = n {
                let dot_class = &eg[eg.find(*dot)];
                dot_class.nodes.iter().any(|dn| matches!(dn, ZIR::Dot(_)))
            } else {
                false
            }
        });
        assert!(
            has_dot_verify,
            "pairing rewrite should work for Verify: Verify(Dot(...), Constant(GT_zero))"
        );
    }

    #[test]
    fn test_pairing_rewrite_n_pairs() {
        let mut eg: ZEgraph = EGraph::default();

        let g1_a = eg.add(ZIR::Constant(Value::G1(
            <ArkBls12_381 as backend::ArkConfig>::G1::zero(),
        )));
        let g2_b = eg.add(ZIR::Constant(Value::G2(
            <ArkBls12_381 as backend::ArkConfig>::G2::zero(),
        )));
        let g1_c = eg.add(ZIR::Constant(Value::G1(
            <ArkBls12_381 as backend::ArkConfig>::G1::zero(),
        )));
        let g2_d = eg.add(ZIR::Constant(Value::G2(
            <ArkBls12_381 as backend::ArkConfig>::G2::zero(),
        )));
        let g1_e = eg.add(ZIR::Neg([g1_a]));
        let g2_f = eg.add(ZIR::Constant(Value::G2(
            <ArkBls12_381 as backend::ArkConfig>::G2::zero(),
        )));
        let g1_g = eg.add(ZIR::Neg([g1_c]));
        let g2_h = eg.add(ZIR::Constant(Value::G2(
            <ArkBls12_381 as backend::ArkConfig>::G2::zero(),
        )));

        let pair1 = eg.add(ZIR::Pair([g1_a, g2_b]));
        let pair2 = eg.add(ZIR::Pair([g1_e, g2_f]));
        let lhs = eg.add(ZIR::Add([pair1, pair2]));

        let pair3 = eg.add(ZIR::Pair([g1_c, g2_d]));
        let pair4 = eg.add(ZIR::Pair([g1_g, g2_h]));
        let rhs = eg.add(ZIR::Add([pair3, pair4]));

        let assert = eg.add(ZIR::Assert([lhs, rhs]));

        saturate(&mut eg);

        let assert_class = &eg[eg.find(assert)];
        let has_dot = assert_class.nodes.iter().any(|n| {
            if let ZIR::Assert([dot, _]) = n {
                let dot_class = &eg[eg.find(*dot)];
                dot_class.nodes.iter().any(|dn| {
                    if let ZIR::Dot([a, b]) = dn {
                        let a_class = &eg[eg.find(*a)];
                        let b_class = &eg[eg.find(*b)];
                        a_class.nodes.iter().any(|vn| {
                            if let ZIR::Vec(ids) = vn {
                                ids.len() == 4
                            } else {
                                false
                            }
                        }) && b_class.nodes.iter().any(|vn| {
                            if let ZIR::Vec(ids) = vn {
                                ids.len() == 4
                            } else {
                                false
                            }
                        })
                    } else {
                        false
                    }
                })
            } else {
                false
            }
        });
        assert!(has_dot, "pairing rewrite should fire for Add-chained pairs");
    }

    #[test]
    fn test_pairing_rewrite_negates_g1s_both_forms() {
        let mut eg: ZEgraph = EGraph::default();

        let g1_a = eg.add(ZIR::Constant(Value::G1(
            <ArkBls12_381 as backend::ArkConfig>::G1::zero(),
        )));
        let g2_b = eg.add(ZIR::Constant(Value::G2(
            <ArkBls12_381 as backend::ArkConfig>::G2::zero(),
        )));
        let g1_c = eg.add(ZIR::Constant(Value::G1(
            <ArkBls12_381 as backend::ArkConfig>::G1::zero(),
        )));
        let g2_d = eg.add(ZIR::Constant(Value::G2(
            <ArkBls12_381 as backend::ArkConfig>::G2::zero(),
        )));

        let pair1 = eg.add(ZIR::Pair([g1_a, g2_b]));
        let pair2 = eg.add(ZIR::Pair([g1_c, g2_d]));
        let assert = eg.add(ZIR::Assert([pair1, pair2]));

        saturate(&mut eg);

        let assert_class = &eg[eg.find(assert)];

        let g1_has_neg = assert_class.nodes.iter().any(|n| {
            if let ZIR::Assert([dot, _]) = n {
                let dot_class = &eg[eg.find(*dot)];
                dot_class.nodes.iter().any(|dn| {
                    if let ZIR::Dot([g1_vec, _]) = dn {
                        let g1_class = &eg[eg.find(*g1_vec)];
                        g1_class.nodes.iter().any(|vn| {
                            if let ZIR::Vec(ids) = vn {
                                ids.iter().any(|id| {
                                    eg[eg.find(*id)]
                                        .nodes
                                        .iter()
                                        .any(|n| matches!(n, ZIR::Neg(_)))
                                })
                            } else {
                                false
                            }
                        })
                    } else {
                        false
                    }
                })
            } else {
                false
            }
        });
        assert!(
            g1_has_neg,
            "pairing rewrite should negate G1s (cheaper than G2s)"
        );

        let g2_has_no_neg = assert_class.nodes.iter().any(|n| {
            if let ZIR::Assert([dot, _]) = n {
                let dot_class = &eg[eg.find(*dot)];
                dot_class.nodes.iter().any(|dn| {
                    if let ZIR::Dot([_, g2_vec]) = dn {
                        let g2_class = &eg[eg.find(*g2_vec)];
                        g2_class.nodes.iter().any(|vn| {
                            if let ZIR::Vec(ids) = vn {
                                !ids.iter().any(|id| {
                                    eg[eg.find(*id)]
                                        .nodes
                                        .iter()
                                        .any(|n| matches!(n, ZIR::Neg(_)))
                                })
                            } else {
                                false
                            }
                        })
                    } else {
                        false
                    }
                })
            } else {
                false
            }
        });
        assert!(g2_has_no_neg, "pairing rewrite should NOT negate any G2s");
    }
}
