//! Loop fusion rewrite.
//!
//! `Map(tag2, [Map(tag1, [dom, body1]), body2])` →
//! `Map(tag1, [dom, substitute(body2, tag2, body1)])`
//!
//! Fuses nested maps: `[g(y) for y in [f(x) for x in 0..N]]` →
//! `[g(f(x)) for x in 0..N]`.
//!
//! Conditions: (1) both bodies have `has_side_effect == false` (pure),
//! (2) body2 references `tag2` (otherwise fusion is pointless),
//! (3) body1's free_vars doesn't contain `tag2` (no capture — guaranteed
//! by fresh tags, but checked for safety).
//!
//! Substitution is done by manually rebuilding body2 with `Var(tag2)`
//! replaced by `body1`. All e-nodes in each e-class are processed to
//! avoid losing interpretations. The `free_vars` analysis is used to
//! short-circuit recursion into subtrees that don't reference `tag2`.

use std::marker::PhantomData;

use super::v;
use crate::lang::{ZAnalysis, ZIR};
use backend::ArkConfig;
use egg::{Applier, EGraph, Id, Language, PatternAst, Rewrite, SearchMatches, Subst, Symbol, Var};

/// Substitute `Var(tag)` with `replacement` in every interpretation of
/// an e-class. Returns one canonical e-class Id.
///
/// All e-nodes in the e-class are processed: each is rebuilt with
/// substituted children, then all rebuilt ids are unioned together.
/// Since they're all equivalent (their originals were equivalent and
/// we applied the same substitution), unioning makes them one e-class.
/// Returning one representative suffices — the e-graph's congruence
/// closure ensures any parent using this e-class gets the right result.
///
/// The `free_vars` analysis short-circuits recursion into subtrees
/// that don't reference `tag`.
fn substitute_var<C: ArkConfig + std::fmt::Debug>(
    egraph: &mut EGraph<ZIR<C>, ZAnalysis<C>>,
    class_id: Id,
    tag: Symbol,
    replacement: Id,
) -> Id {
    let class_id = egraph.find(class_id);
    let replacement = egraph.find(replacement);

    // Short-circuit: if tag not in free_vars, no substitution needed
    if !egraph[class_id].data.free_vars.contains(&tag) {
        return class_id;
    }

    // Clone nodes to avoid borrowing egraph while adding
    let nodes: Vec<ZIR<C>> = egraph[class_id].nodes.to_vec();
    let mut result_ids = vec![];

    for node in &nodes {
        match node {
            ZIR::Var(t) if *t == tag => {
                // This is the variable being substituted
                result_ids.push(replacement);
            }
            ZIR::Var(_) | ZIR::Constant(_) => {
                // Other leaves: add as-is
                result_ids.push(egraph.add(node.clone()));
            }
            // Non-leaf nodes: recursively substitute each child
            // (each child returns one canonical id after unioning its
            // own results), then rebuild this node with those ids.
            _ => {
                let children: &[Id] = node.children();
                let new_children: Vec<Id> = children
                    .iter()
                    .map(|&c| substitute_var(egraph, c, tag, replacement))
                    .collect();
                let new_node = rebuild_node(node, &new_children);
                result_ids.push(egraph.add(new_node));
            }
        }
    }

    // Union all rebuilt ids — they're all equivalent substitutions
    let canonical = result_ids[0];
    for &id in &result_ids[1..] {
        egraph.union(canonical, id);
    }
    egraph.find(canonical)
}

/// Rebuild a ZIR node with new children. Only handles variants that have
/// children (Var and Constant are leaves handled separately in
/// `substitute_var`).
fn rebuild_node<C: ArkConfig>(node: &ZIR<C>, children: &[Id]) -> ZIR<C> {
    match node {
        ZIR::Var(_) | ZIR::Constant(_) => node.clone(),
        ZIR::Add(_) => ZIR::Add([children[0], children[1]]),
        ZIR::Sub(_) => ZIR::Sub([children[0], children[1]]),
        ZIR::Mul(_) => ZIR::Mul([children[0], children[1]]),
        ZIR::Div(_) => ZIR::Div([children[0], children[1]]),
        ZIR::Rem(_) => ZIR::Rem([children[0], children[1]]),
        ZIR::Pow(_) => ZIR::Pow([children[0], children[1]]),
        ZIR::Dot(_) => ZIR::Dot([children[0], children[1]]),
        ZIR::Concat(_) => ZIR::Concat([children[0], children[1]]),
        ZIR::Neg(_) => ZIR::Neg([children[0]]),
        ZIR::Pair(_) => ZIR::Pair([children[0], children[1]]),
        ZIR::Poly(_) => ZIR::Poly([children[0]]),
        ZIR::Coef(_) => ZIR::Coef([children[0]]),
        ZIR::Mle(_) => ZIR::Mle([children[0]]),
        ZIR::Fft(_) => ZIR::Fft([children[0]]),
        ZIR::Ifft(_) => ZIR::Ifft([children[0]]),
        ZIR::Interpolate(_) => ZIR::Interpolate([children[0], children[1]]),
        ZIR::Evaluate(_) => ZIR::Evaluate([children[0], children[1]]),
        ZIR::EvaluateGrid(_) => ZIR::EvaluateGrid([children[0]]),
        ZIR::EvaluateSelected(_) => ZIR::EvaluateSelected([children[0], children[1], children[2]]),
        ZIR::Reduce(op, _) => ZIR::Reduce(*op, [children[0]]),
        ZIR::Map(tag, _) => ZIR::Map(*tag, [children[0], children[1]]),
        ZIR::Proj(field, _) => ZIR::Proj(*field, [children[0]]),
        ZIR::Record(names, _) => ZIR::Record(names.clone(), children.to_vec().into_boxed_slice()),
        ZIR::Vec(_) => ZIR::Vec(children.to_vec().into_boxed_slice()),
        ZIR::Ram(_) => ZIR::Ram([children[0], children[1]]),
        ZIR::Random(name, na) => ZIR::Random(*name, *na),
        ZIR::Challenge(name, na) => ZIR::Challenge(*name, *na),
        ZIR::Log(name, _) => ZIR::Log(*name, [children[0]]),
        ZIR::Seq(_) => ZIR::Seq([children[0], children[1]]),
        ZIR::Assert(_) => ZIR::Assert([children[0], children[1]]),
        ZIR::Verify(_) => ZIR::Verify([children[0], children[1]]),
    }
}

/// Custom Searcher for loop fusion.
/// Walks e-classes looking for `Map(tag2, [Map(tag1, [dom, body1]), body2])`
/// where both bodies are pure and body2 references tag2.
///
/// Binds `?dom`, `?body1`, `?body2`, `?tag1`, `?tag2`.
/// Since Subst can only store Ids (not Symbols), we store tag1 and tag2
/// as Ids of their Var nodes.
pub struct MapFusionSearcher<C: ArkConfig>(PhantomData<C>);

impl<C: ArkConfig + std::fmt::Debug> egg::Searcher<ZIR<C>, ZAnalysis<C>> for MapFusionSearcher<C> {
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
        let body1_var = v("?body1");
        let body2_var = v("?body2");
        let tag1_var = v("?tag1");
        let tag2_var = v("?tag2");
        let mut substs = vec![];
        'outer: for node in &egraph[eclass].nodes {
            if let ZIR::Map(tag2, [inner_map_id, body2_id]) = node {
                let inner_map_class = egraph.find(*inner_map_id);
                let body2_class = egraph.find(*body2_id);

                // Condition 1: body2 must be pure
                if egraph[body2_class].data.has_side_effect {
                    continue;
                }
                // Condition 2: body2 must reference tag2
                if !egraph[body2_class].data.free_vars.contains(tag2) {
                    continue;
                }

                // Find Map(tag1, [dom, body1]) in the inner map's e-class
                for inner_node in &egraph[inner_map_class].nodes {
                    if let ZIR::Map(_tag1, [dom_id, body1_id]) = inner_node {
                        let dom_class = egraph.find(*dom_id);
                        let body1_class = egraph.find(*body1_id);

                        // Condition 1: body1 must be pure
                        if egraph[body1_class].data.has_side_effect {
                            continue;
                        }
                        // Condition 3: body1's free_vars must not contain tag2 (no capture)
                        if egraph[body1_class].data.free_vars.contains(tag2) {
                            continue;
                        }

                        let mut subst = Subst::default();
                        subst.insert(dom_var, dom_class);
                        subst.insert(body1_var, body1_class);
                        subst.insert(body2_var, body2_class);
                        // Store the inner map e-class and outer e-class to re-extract tags
                        subst.insert(tag1_var, inner_map_class);
                        subst.insert(tag2_var, eclass);
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
        vec![v("?dom"), v("?body1"), v("?body2"), v("?tag1"), v("?tag2")]
    }
}

/// Custom Applier for loop fusion.
/// Uses the Subst to find the specific nested Map structure, extracts tags,
/// substitutes `Var(tag2)` with `body1` in body2 (rebuilding all
/// interpretations), unions the results, creates `Map(tag1, [dom, body])`,
/// unions with the matched e-class.
pub struct MapFusionApplier<C: ArkConfig>(PhantomData<C>);

impl<C: ArkConfig + std::fmt::Debug> Applier<ZIR<C>, ZAnalysis<C>> for MapFusionApplier<C> {
    fn apply_one(
        &self,
        egraph: &mut EGraph<ZIR<C>, ZAnalysis<C>>,
        eclass: Id,
        subst: &Subst,
        _searcher_ast: Option<&PatternAst<ZIR<C>>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        let dom_class = egraph.find(subst[v("?dom")]);
        let body1_class = egraph.find(subst[v("?body1")]);
        let body2_class = egraph.find(subst[v("?body2")]);
        let inner_map_class = egraph.find(subst[v("?tag1")]);
        let outer_class = egraph.find(subst[v("?tag2")]);

        // Re-extract tag1 from the inner Map node
        let tag1 = {
            let mut found = None;
            for node in &egraph[inner_map_class].nodes {
                if let ZIR::Map(t, [d, b]) = node
                    && egraph.find(*d) == dom_class && egraph.find(*b) == body1_class {
                        found = Some(*t);
                        break;
                    }
            }
            match found {
                Some(t) => t,
                None => return vec![],
            }
        };

        // Re-extract tag2 from the outer Map node
        let tag2 = {
            let mut found = None;
            for node in &egraph[outer_class].nodes {
                if let ZIR::Map(t, [im, b2]) = node
                    && egraph.find(*im) == inner_map_class && egraph.find(*b2) == body2_class {
                        found = Some(*t);
                        break;
                    }
            }
            match found {
                Some(t) => t,
                None => return vec![],
            }
        };

        // Substitute Var(tag2) with body1 in body2, rebuilding all
        // interpretations and unioning them into one e-class.
        let canonical_body = substitute_var(egraph, body2_class, tag2, body1_class);

        // Build Map(tag1, [dom, canonical_body])
        let new_map = egraph.add(ZIR::Map(tag1, [dom_class, canonical_body]));

        if egraph.union(eclass, new_map) {
            vec![new_map]
        } else {
            vec![]
        }
    }
}

pub fn rewrites<C: ArkConfig + std::fmt::Debug + Clone + 'static>()
-> Vec<Rewrite<ZIR<C>, ZAnalysis<C>>> {
    vec![
        Rewrite::new(
            "map-fusion",
            MapFusionSearcher::<C>(PhantomData),
            MapFusionApplier::<C>(PhantomData),
        )
        .unwrap(),
    ]
}
