use crate::Var;
use backend::ArkConfig;
use backend::op::HasOpFactory;
use graph::{DQDag, GOp, Node, Op, Ref, mk};
use petgraph::graph::NodeIndex;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

fn named_var(
    dag: &DQDag<impl ArkConfig>,
    r: Ref,
    typ: backend::ATyp,
    qualifier: lang::typ::Qualifier,
    distribution: lang::typ::Distribution,
) -> Var {
    let name = dag.find_var(r.node());
    Var {
        reference: r,
        index: Vec::new(),
        typ,
        qualifier,
        distribution,
        name: name
            .map(|v| v.0)
            .unwrap_or_else(|| format!("__zippel::node::{}", r.node().index())),
    }
}

fn collect_reachable_forward<C: ArkConfig>(dag: &DQDag<C>, start: NodeIndex) -> HashSet<NodeIndex> {
    let mut done: HashSet<NodeIndex> = HashSet::new();
    let mut worklist = vec![start];

    while let Some(node) = worklist.pop() {
        if !done.insert(node) {
            continue;
        }
        for neighbor in dag.nodes_from(node) {
            if !done.contains(&neighbor) {
                worklist.push(neighbor);
            }
        }
    }

    done.into_iter().filter(|&n| dag[n].is_op()).collect()
}

fn collect_reachable_backward<C: ArkConfig>(
    dag: &DQDag<C>,
    starts: &[NodeIndex],
    stop_set: Option<&HashSet<NodeIndex>>,
) -> HashSet<NodeIndex> {
    let mut done: HashSet<NodeIndex> = HashSet::new();
    let mut worklist: Vec<NodeIndex> = starts.to_vec();

    while let Some(node) = worklist.pop() {
        if !done.insert(node) {
            continue;
        }
        if stop_set.map_or_else(|| false, |s| s.contains(&node)) {
            continue;
        }
        for neighbor in dag.nodes_to(node) {
            if !done.contains(&neighbor) {
                worklist.push(neighbor);
            }
        }
    }

    done.into_iter().filter(|&n| dag[n].is_op()).collect()
}

fn topo_sort_nodes<C: ArkConfig>(dag: &DQDag<C>, nodes: &HashSet<NodeIndex>) -> Vec<NodeIndex> {
    let mut in_degree: HashMap<NodeIndex, usize> = HashMap::with_capacity(nodes.len());
    for &node in nodes {
        let deg = dag.nodes_to(node).filter(|dep| nodes.contains(dep)).count();
        in_degree.insert(node, deg);
    }

    let mut queue: VecDeque<NodeIndex> = in_degree
        .iter()
        .filter(|&(_, &deg)| deg == 0)
        .map(|(&node, _)| node)
        .collect();

    let mut result = Vec::with_capacity(nodes.len());
    while let Some(node) = queue.pop_front() {
        result.push(node);
        for dependent in dag.nodes_from(node) {
            if let Some(deg) = in_degree.get_mut(&dependent) {
                *deg -= 1;
                if *deg == 0 {
                    queue.push_back(dependent);
                }
            }
        }
    }

    assert_eq!(
        result.len(),
        nodes.len(),
        "topo_sort_nodes: cycle detected or nodes missing"
    );
    result
}

/// Transitive closure on a DAG.
///
/// Flattens a `DQDag` into a linear list of `(Var, GOp)` pairs.
/// For each node, `trans_clos_op` recursively normalizes the stored op:
/// - `Op::Check(inner)` is unwrapped to `inner` (the verifier assertion is
///   stripped, leaving the asserted expression).
/// - `Op::Ref` children are resolved so that their targets are added to
///   `clos`. After resolution, compound ops are reconstructed via `mk()`
///   wrapping, but no algebraic simplification fires on `Ref` children.
///
/// `vars` holds the protocol-parameter Vars.
///
/// # Invariants
///
/// - **`vars`** contains exactly the leaf/source nodes — variables that are
///   opaque inputs to the computation (e.g. protocol arguments, transcript
///   challenges/randomness). These are never the result of an operation.
///
/// - **`clos`** contains exactly the result nodes — Vars that are the output
///   of some operation (`GOp`). Every entry `(var, op)` satisfies: `var` is the
///   result of applying `op` to its operands.
///
/// - **Disjointness**: `vars` and `clos` are disjoint. A Var that is a leaf
///   (source/input) appears only in `vars`; a Var that is a computation
///   result appears only in `clos`. This invariant is maintained by the
///   internal `seen` map — leaf nodes are inserted into `seen` before the
///   traversal, so `trans_clos_ref` skips them when encountered later.
///
/// Constructors pre-populate the internal `seen` map to establish canonical
/// mappings before traversal:
/// - `relation()` maps both input-arg and relation-arg nodes to the same
///   input-arg Var, ensuring a single namespace.
/// - `verifier()` pre-populates transcript-source nodes so `trans_clos_op`
///   doesn't recurse past the transcript boundary.
#[derive(Clone)]
pub struct TransClos<C: ArkConfig> {
    pub clos: Vec<(Var, GOp<C>)>,
    pub vars: Vec<Var>,
}

impl<C: ArkConfig + HasOpFactory> TransClos<C> {
    // ----------------------------------------------------------------
    // Public constructors
    // ----------------------------------------------------------------

    /// Transitive closure from the `Rel` (relation) marker of the full DAG.
    ///
    /// Pre-populates the index with identity entries for each input arg
    /// (so they get canonical Vars), then maps each relation-arg node to
    /// the same index entry by name. This ensures the resulting closure
    /// uses a single namespace — the input namespace — throughout.
    ///
    /// Panics if the DAG has no relation node (i.e. it's a function, not a protocol).
    pub fn relation(dag: &DQDag<C>) -> Self {
        let start = dag.relation_node().unwrap();
        let rel_vars = Self::vars_from_marker(dag, start);
        let input_vars = Self::vars_from_marker(dag, dag.input_node());

        let mut tc = Self {
            clos: Vec::new(),
            vars: Vec::new(),
        };
        let mut seen: HashMap<NodeIndex, Var> = HashMap::new();

        // Insert input args as canonical entries in seen (not clos — they're
        // leaf/source nodes, not results of ops), then alias relation args.
        for input_var in &input_vars {
            seen.insert(input_var.node(), input_var.clone());
        }
        for rel_var in &rel_vars {
            let input_var = input_vars
                .iter()
                .find(|ip| ip.name() == rel_var.name())
                .expect("relation arg must also exist in input arg");
            seen.insert(rel_var.node(), input_var.clone());
        }

        tc.vars = input_vars;

        let reachable = collect_reachable_forward(dag, start);
        let topo = topo_sort_nodes(dag, &reachable);
        for node in topo {
            if !seen.contains_key(&node) {
                tc.trans_clos_ref(dag, dag.find_ref(node), &mut seen);
            }
        }
        tc
    }

    /// Transitive closure of the prover view.
    ///
    /// Walks backward from transcript nodes to input args and processes
    /// every node encountered. Prefs are all input args (both public and
    /// private).
    pub fn prover(dag: &DQDag<C>) -> Self {
        let vars = Self::vars_from_marker(dag, dag.input_node());
        let transcripts_vec = dag.transcript_nodes();

        let mut tc = Self {
            clos: Vec::new(),
            vars,
        };

        let reachable = collect_reachable_backward(dag, &transcripts_vec, None);
        let topo = topo_sort_nodes(dag, &reachable);

        let mut seen: HashMap<NodeIndex, Var> = HashMap::new();

        for node in topo {
            tc.trans_clos_ref(dag, dag.find_ref(node), &mut seen);
        }
        tc
    }

    /// Transitive closure of the verifier view.
    ///
    /// Walks backwards from verifier assertion (`Check`) nodes, stopping at
    /// transcript source nodes (Challenge/Random) which are opaque inputs
    /// to the verifier. Prefs include public input args and transcript sources.
    ///
    /// Transcript source nodes are pre-populated in the index so that
    /// `trans_clos_op` does not recurse past them into prover-only nodes.
    pub fn verifier(dag: &DQDag<C>) -> Self {
        let input_vars: Vec<Var> = dag
            .input_args()
            .into_iter()
            .filter_map(|n| match &dag[n] {
                Node::Arg(name, typ, qual, dist, _kind) => {
                    if qual.is_public() {
                        let var = Var::new_named(Ref(n), name.0.clone(), typ.clone(), *qual, *dist);
                        Some(var)
                    } else {
                        None
                    }
                }
                _ => None,
            })
            .collect();

        let checks = dag.find_check();
        let transcripts_vec = dag.transcript_nodes();
        let transcripts_set: HashSet<NodeIndex> = transcripts_vec.iter().copied().collect();

        let mut tc = Self {
            clos: Vec::new(),
            vars: input_vars,
        };

        let mut seen: HashMap<NodeIndex, Var> = HashMap::new();

        // Pre-populate seen with transcript source nodes so trans_clos_ref
        // doesn't recurse past them into prover-only nodes. Also add
        // transcript source Vars to vars — they are opaque inputs to
        // the verifier, analogous to public args. These are leaf nodes
        // and are NOT added to clos.
        for &n in &transcripts_vec {
            match &dag[n] {
                Node::Op(op, (qualifier, distribution))
                | Node::Transcr(op, (qualifier, distribution)) => {
                    let inner = op.get();
                    let var = named_var(dag, Ref::new(n), inner.typ(), *qualifier, *distribution);
                    tc.vars.push(var.clone());
                    seen.insert(n, var);
                }
                _ => {}
            }
        }

        let reachable = collect_reachable_backward(dag, &checks, Some(&transcripts_set));
        let topo = topo_sort_nodes(dag, &reachable);
        for node in topo {
            if !seen.contains_key(&node) {
                tc.trans_clos_ref(dag, dag.find_ref(node), &mut seen);
            }
        }
        tc
    }

    /// Remap every Var (both vars and clos entries) through `f`.
    ///
    /// `f` must not change the `reference` (node identity) of a Var, only its
    /// metadata. Changing the reference would leave `Op::Ref` children in
    /// `clos` pointing at stale node identities.
    pub fn remap(&mut self, f: &impl Fn(&Var) -> Var) {
        self.vars = self.vars.iter().map(f).collect();
        self.clos = self.clos.drain(..).map(|(var, op)| (f(&var), op)).collect();
    }

    // ----------------------------------------------------------------
    // Internal
    // ----------------------------------------------------------------

    fn vars_from_marker<A>(dag: &graph::Dag<C, A>, node: NodeIndex) -> Vec<Var> {
        let mut args: Vec<NodeIndex> = dag.nodes_from(node).filter(|n| dag[*n].is_arg()).collect();
        args.sort();
        args.into_iter()
            .filter_map(|n| match &dag[n] {
                Node::Arg(name, typ, qual, dist, _kind) => {
                    let var = Var::new_named(Ref(n), name.0.clone(), typ.clone(), *qual, *dist);
                    Some(var)
                }
                _ => None,
            })
            .collect()
    }

    fn trans_clos_op(
        &mut self,
        dag: &DQDag<C>,
        op: GOp<C>,
        seen: &mut HashMap<NodeIndex, Var>,
    ) -> GOp<C> {
        match op {
            Op::Ref(r, _) => self.trans_clos_ref(dag, r, seen),
            Op::Bin(op, a, b, typ) => {
                let oa = self.trans_clos_op(dag, a.get().clone(), seen);
                let ob = self.trans_clos_op(dag, b.get().clone(), seen);
                Op::bin(op, oa, ob, typ.clone())
            }
            Op::Ram(a, b) => {
                let oa = self.trans_clos_op(dag, a.get().clone(), seen);
                let ob = self.trans_clos_op(dag, b.get().clone(), seen);
                Op::Ram(mk::<C>(oa), mk::<C>(ob))
            }
            Op::Value(v) => Op::Value(v),
            Op::Vec(vs) => Op::Vec(
                vs.into_iter()
                    .map(|v| mk::<C>(self.trans_clos_op(dag, v.get().clone(), seen)))
                    .collect::<Vec<_>>(),
            ),
            Op::Check(op) => self.trans_clos_op(dag, op.get().clone(), seen),
            Op::Interpolate(points, evals) => Op::Interpolate(
                mk::<C>(self.trans_clos_op(dag, points.get().clone(), seen)),
                mk::<C>(self.trans_clos_op(dag, evals.get().clone(), seen)),
            ),
            Op::Ifft(v) => Op::Ifft(mk::<C>(self.trans_clos_op(dag, v.get().clone(), seen))),
            Op::Fft(v) => Op::Fft(mk::<C>(self.trans_clos_op(dag, v.get().clone(), seen))),
            Op::Reduce(op, v) => {
                Op::Reduce(op, mk::<C>(self.trans_clos_op(dag, v.get().clone(), seen)))
            }
            Op::Evaluate(p, range, xs) => Op::Evaluate(
                mk::<C>(self.trans_clos_op(dag, p.get().clone(), seen)),
                range,
                xs.map(|xs| mk::<C>(self.trans_clos_op(dag, xs.get().clone(), seen))),
            ),
            Op::LoopParam(i, t) => Op::LoopParam(i, t),
            Op::Map(d, b) => Op::Map(
                mk::<C>(self.trans_clos_op(dag, d.get().clone(), seen)),
                mk::<C>(self.trans_clos_op(dag, b.get().clone(), seen)),
            ),
            Op::ReduceMap(op, d, b) => Op::ReduceMap(
                op,
                mk::<C>(self.trans_clos_op(dag, d.get().clone(), seen)),
                mk::<C>(self.trans_clos_op(dag, b.get().clone(), seen)),
            ),
            Op::Poly(v) => Op::Poly(mk::<C>(self.trans_clos_op(dag, v.get().clone(), seen))),
            Op::Mle(v) => Op::Mle(mk::<C>(self.trans_clos_op(dag, v.get().clone(), seen))),
            Op::Coef(v) => Op::Coef(mk::<C>(self.trans_clos_op(dag, v.get().clone(), seen))),
            Op::Record(fields) => Op::Record(
                fields
                    .into_iter()
                    .map(|(k, v)| {
                        (
                            k.clone(),
                            mk::<C>(self.trans_clos_op(dag, v.get().clone(), seen)),
                        )
                    })
                    .collect(),
            ),
            Op::Pair(a, b, t) => {
                let oa = self.trans_clos_op(dag, a.get().clone(), seen);
                let ob = self.trans_clos_op(dag, b.get().clone(), seen);
                Op::Pair(mk::<C>(oa), mk::<C>(ob), t)
            }
            Op::Random(t, b) => Op::Random(t, b),
            Op::Challenge(t, b) => Op::Challenge(t, b),

            Op::Proj(op, field, typ) => Op::Proj(
                mk::<C>(self.trans_clos_op(dag, op.get().clone(), seen)),
                field.clone(),
                typ.clone(),
            ),
        }
    }

    fn find<'a>(seen: &'a HashMap<NodeIndex, Var>, r: &Ref) -> Option<&'a Var> {
        seen.get(&r.node())
    }

    fn insert(&mut self, r: Var, op: GOp<C>, seen: &mut HashMap<NodeIndex, Var>) -> GOp<C> {
        if let Some(canonical) = seen.get(&r.node()) {
            Op::Ref(canonical.reference, op.typ())
        } else {
            let typ = op.typ();
            let node = r.node();
            let reference = r.reference;
            self.clos.push((r.clone(), op));
            seen.insert(node, r);
            Op::Ref(reference, typ)
        }
    }

    fn trans_clos_ref(
        &mut self,
        dag: &DQDag<C>,
        r: Ref,
        seen: &mut HashMap<NodeIndex, Var>,
    ) -> GOp<C> {
        if let Some(canonical) = Self::find(seen, &r) {
            return Op::Ref(canonical.reference, canonical.typ.clone());
        }
        match &dag[r.node()] {
            Node::Op(op, (qualifier, distribution))
            | Node::Transcr(op, (qualifier, distribution))
                if matches!(op.get(), Op::Challenge(_, _) | Op::Random(_, _)) =>
            {
                let inner = op.get();
                let var = named_var(dag, r, inner.typ(), *qualifier, *distribution);
                self.insert(var, inner.clone(), seen)
            }
            Node::Op(op, (qualifier, distribution))
            | Node::Transcr(op, (qualifier, distribution)) => {
                let obin = self.trans_clos_op(dag, op.get().clone(), seen);
                self.insert(
                    named_var(dag, r, obin.typ(), *qualifier, *distribution),
                    obin,
                    seen,
                )
            }
            Node::Arg(_, t, _, _, _) => Op::Ref(r, t.clone()),
            Node::Inp(_) | Node::Rel(_) => {
                unreachable!("Input/relation marker should not be referenced directly")
            }
        }
    }
}

impl<C: ArkConfig> fmt::Display for TransClos<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(
            f,
            "Pref: {}",
            self.vars
                .iter()
                .map(|n| n.verbose())
                .collect::<Vec<_>>()
                .join(", ")
        )?;
        write!(f, "\nTC: \n")?;
        self.clos
            .iter()
            .try_for_each(|(n, op)| writeln!(f, "\t{}   |   {} ", n.verbose(), op))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{QualifierPropagation, UniformityPropagation};
    use backend::ArkBls12_381;
    use graph::{DQDag, UDags};
    use lang::ast::UModule;
    use share::{Ctx, unwrap};
    use std::collections::HashSet;

    fn make_qualified_dag(ex: &str) -> DQDag<ArkBls12_381> {
        let m = UModule::from_str(ex)
            .unwrap()
            .concretize(&Ctx::new())
            .unwrap();
        let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));
        let g = QualifierPropagation::from_dag(&gs[0]);
        UniformityPropagation::from_dag(&g).annotate_dag(&g)
    }

    #[test]
    fn trans_clos_prover_not_empty() {
        let g = make_qualified_dag(
            r#"
            proto foo<F: Field>(private s: [F; 10], private s': F, public i: Fin<5>) where s == s {
                let r = random<F>;
                a <- r * s[i + 2];
                b <- r * s';
                verify(a == b)
            }"#,
        );

        let tc = TransClos::prover(&g);

        assert!(!tc.vars.is_empty(), "vars should not be empty");
        assert!(
            tc.vars.iter().any(|p| p.is_private()),
            "prover should include private args"
        );
        assert!(
            tc.vars.iter().any(|p| p.is_public()),
            "prover should include public args"
        );
        assert!(!tc.clos.is_empty(), "clos should not be empty");

        for (_, op) in tc.clos.iter() {
            assert!(
                !matches!(op, Op::Bin(_, a, _, _) if matches!(a.get(), Op::Bin(_, _, _, _))),
                "found nested Bin in left child"
            );
            assert!(
                !matches!(op, Op::Bin(_, _, b, _) if matches!(b.get(), Op::Bin(_, _, _, _))),
                "found nested Bin in right child"
            );
        }
    }

    #[test]
    fn trans_clos_relation_uses_input_namespace() {
        let g = make_qualified_dag(
            r#"
            proto foo<F: Field>(private s: [F; 10], private s': F, public i: Fin<5>) where s == s {
                let r = random<F>;
                a <- r * s[i + 2];
                b <- r * s';
                verify(a == b)
            }"#,
        );

        let tc_prover = TransClos::prover(&g);
        let tc_rel = TransClos::relation(&g);

        // Relation vars should use input namespace (same NodeIndex)
        for rel_var in &tc_rel.vars {
            let matching_prover = tc_prover.vars.iter().find(|ip| ip.name() == rel_var.name());
            assert!(
                matching_prover.is_some(),
                "relation arg {:?} should have a matching prover arg",
                rel_var.name()
            );
            assert_eq!(
                rel_var.node(),
                matching_prover.unwrap().node(),
                "relation arg {:?} should map to same node as prover arg",
                rel_var.name()
            );
        }

        // Relation clos entries for arg nodes should also use input namespace
        for (var, _) in tc_rel.clos.iter() {
            if let Some(prover_var) = tc_prover.vars.iter().find(|ip| ip.name() == var.name()) {
                assert_eq!(
                    var.node(),
                    prover_var.node(),
                    "relation clos entry {:?} should use input namespace",
                    var.name()
                );
            }
        }
    }

    #[test]
    fn trans_clos_parametric() {
        let g = make_qualified_dag(
            r#"
            proto foo<F: Field, N: 2..4>(private s: [F; N], private s': F, public i: Fin<2>) where s == s {
                let r = random<F>;
                a <- r * s[i];
                b <- r * s';
                verify(a == b)
            }"#,
        );

        let tc = TransClos::prover(&g);

        for (_, op) in tc.clos.iter() {
            assert!(
                !matches!(op, Op::Bin(_, a, _, _) if matches!(a.get(), Op::Bin(_, _, _, _))),
                "found nested Bin in left child"
            );
            assert!(
                !matches!(op, Op::Bin(_, _, b, _) if matches!(b.get(), Op::Bin(_, _, _, _))),
                "found nested Bin in right child"
            );
        }
    }

    #[test]
    fn trans_clos_prover_sees_all_inputs() {
        let g = make_qualified_dag(
            r#"
            proto foo<F: Field>(private a: F, public b: F) where a == a {
                let r = random<F>;
                c <- r * a;
                verify(c == c)
            }"#,
        );

        let tc_prover = TransClos::prover(&g);

        assert!(
            tc_prover.vars.iter().any(|p| p.is_private()),
            "prover should see private inputs"
        );
        assert!(
            tc_prover.vars.iter().any(|p| p.is_public()),
            "prover should see public inputs"
        );
    }

    #[test]
    fn trans_clos_prover_stops_at_transcript() {
        let g = make_qualified_dag(
            r#"
            proto foo<F: Field>(private a: F, public b: F) where a == b {
                let r = random<F>;
                c <- r * a;
                verify(c == r * b)
            }"#,
        );

        let tc_prover = TransClos::prover(&g);

        assert!(
            !tc_prover.clos.is_empty(),
            "prover should have reachable ops"
        );

        // Prover should include both private and public input vars
        assert!(
            tc_prover.vars.iter().any(|p| p.is_private()),
            "prover should see private inputs"
        );
        assert!(
            tc_prover.vars.iter().any(|p| p.is_public()),
            "prover should see public inputs"
        );
    }

    #[test]
    fn trans_clos_verifier_does_not_leak_prover_ops() {
        let g = make_qualified_dag(
            r#"
            proto foo<F: Field>(private a: F, public b: F) where a == b {
                let r = random<F>;
                c <- r * a;
                verify(c == r * b)
            }"#,
        );

        let tc = TransClos::verifier(&g);

        assert!(
            tc.vars.iter().all(|p| p.is_public()),
            "verifier vars should all be public, got: {:?}",
            tc.vars
        );
        assert!(
            !tc.vars.is_empty(),
            "verifier should have at least one public arg"
        );
        assert!(!tc.clos.is_empty(), "verifier should have reachable ops");

        let has_transcript_source = tc
            .clos
            .iter()
            .any(|(_, op)| matches!(op, Op::Challenge(_, _) | Op::Random(_, _)));
        assert!(
            has_transcript_source,
            "verifier should see at least one transcript source (Challenge/Random)"
        );

        // Verifier clos should not contain any private-input Vars
        let private_vars: HashSet<NodeIndex> = g
            .input_args()
            .into_iter()
            .filter(|n| match &g[*n] {
                Node::Arg(_, _, qual, _, _) => qual.is_private(),
                _ => false,
            })
            .collect();
        for (verifier_var, _) in tc.clos.iter() {
            assert!(
                !private_vars.contains(&verifier_var.node()),
                "verifier clos entry at node {:?} should not be a private input",
                verifier_var.node()
            );
        }
    }

    #[test]
    fn trans_clos_remap_preserves_structure() {
        let g = make_qualified_dag(
            r#"
            proto foo<F: Field>(private s: F, public b: F) where s == b {
                let r = random<F>;
                c <- r * s;
                verify(c == r * b)
            }"#,
        );

        let tc = TransClos::prover(&g);
        let original_clos_len = tc.clos.len();
        let original_vars_len = tc.vars.len();

        let mut tc2 = TransClos::prover(&g);
        tc2.remap(&|var| var.clone());

        assert_eq!(
            tc2.clos.len(),
            original_clos_len,
            "identity remap should preserve clos length"
        );
        assert_eq!(
            tc2.vars.len(),
            original_vars_len,
            "identity remap should preserve vars length"
        );

        for (orig, remapped) in tc.clos.iter().zip(tc2.clos.iter()) {
            assert_eq!(
                orig.0.node(),
                remapped.0.node(),
                "remap should preserve node identity"
            );
        }
    }

    #[test]
    fn trans_clos_check_unwrapped() {
        let g = make_qualified_dag(
            r#"
            proto foo<F: Field>(private a: F, public b: F) where a == b {
                verify(a == b)
            }"#,
        );

        let tc = TransClos::prover(&g);

        for (_, op) in tc.clos.iter() {
            assert!(
                !matches!(op, Op::Check(_)),
                "Op::Check should be unwrapped in transitive closure, found: {:?}",
                op
            );
        }
    }

    fn verify_topo_order<C: ArkConfig>(tc: &TransClos<C>) {
        let node_to_pos: HashMap<NodeIndex, usize> = tc
            .clos
            .iter()
            .enumerate()
            .map(|(i, (var, _))| (var.node(), i))
            .collect();

        for (i, (_, op)) in tc.clos.iter().enumerate() {
            for r in op.references() {
                if let Some(&dep_pos) = node_to_pos.get(&r.node())
                    && dep_pos != i
                {
                    assert!(
                        dep_pos < i,
                        "topo violation: dependency at clos[{}] ({:?}) appears after dependent at clos[{}]",
                        dep_pos,
                        r.node(),
                        i
                    );
                }
            }
        }
    }

    #[test]
    fn trans_clos_prover_topological_order() {
        let g = make_qualified_dag(
            r#"
            proto foo<F: Field>(private s: [F; 10], private s': F, public i: Fin<5>) where s == s {
                let r = random<F>;
                a <- r * s[i + 2];
                b <- r * s';
                verify(a == b)
            }"#,
        );

        let tc = TransClos::prover(&g);
        verify_topo_order(&tc);
    }

    #[test]
    fn trans_clos_verifier_topological_order() {
        let g = make_qualified_dag(
            r#"
            proto foo<F: Field>(private a: F, public b: F) where a == b {
                let r = random<F>;
                c <- r * a;
                verify(c == r * b)
            }"#,
        );

        let tc = TransClos::verifier(&g);
        verify_topo_order(&tc);
    }

    #[test]
    fn trans_clos_relation_topological_order() {
        let g = make_qualified_dag(
            r#"
            proto foo<F: Field>(private s: [F; 10], private s': F, public i: Fin<5>) where s == s {
                let r = random<F>;
                a <- r * s[i + 2];
                b <- r * s';
                verify(a == b)
            }"#,
        );

        let tc = TransClos::relation(&g);
        verify_topo_order(&tc);
    }
}
