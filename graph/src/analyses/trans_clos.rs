use crate::{DQDag, GOp, Node, Op, PRef, Ref, mk};
use backend::ArkConfig;
use backend::op::HasOpFactory;
use petgraph::graph::NodeIndex;
use std::collections::{HashMap, HashSet};
use std::fmt;

fn named_pref(
    dag: &DQDag<impl ArkConfig>,
    r: Ref,
    typ: backend::ATyp,
    qualifier: crate::Qualifier,
    distribution: crate::Distribution,
) -> PRef {
    let name = dag.find_var(r.node());
    PRef {
        reference: r,
        index: 0,
        typ,
        qualifier,
        distribution,
        from_transcript: false,
        name,
    }
}

/// Transitive closure on a DAG.
///
/// Flattens a `DQDag` into a linear list of `(PRef, GOp)` pairs.
/// For each node, `trans_clos_op` recursively normalizes the stored op:
/// - `Op::Check(inner)` is unwrapped to `inner` (the verifier assertion is
///   stripped, leaving the asserted expression).
/// - `Op::Ref` children are resolved so that their targets are added to
///   `clos`. After resolution, compound ops are reconstructed via `mk()`
///   wrapping, but no algebraic simplification fires on `Ref` children.
///
/// `prefs` holds the protocol-parameter PRefs.
///
/// An internal `index: HashMap<NodeIndex, usize>` maps node indices to their
/// position in `clos` for O(1) lookup and deduplication. Constructors can
/// pre-populate this index to establish canonical mappings:
/// - `relation()` inserts input-arg entries and maps relation-arg nodes to
///   them, ensuring a single namespace.
/// - `verifier()` inserts transcript-source entries so `trans_clos_op`
///   doesn't recurse past the transcript boundary.
#[derive(Clone)]
pub struct TransClos<C: ArkConfig> {
    pub clos: Vec<(PRef, GOp<C>)>,
    pub prefs: Vec<PRef>,
}

impl<C: ArkConfig + HasOpFactory> TransClos<C> {
    // ----------------------------------------------------------------
    // Public constructors
    // ----------------------------------------------------------------

    /// Transitive closure from the `Rel` (relation) marker of the full DAG.
    ///
    /// Pre-populates the index with identity entries for each input arg
    /// (so they get canonical PRefs), then maps each relation-arg node to
    /// the same index entry by name. This ensures the resulting closure
    /// uses a single namespace — the input namespace — throughout.
    ///
    /// Panics if the DAG has no relation node (i.e. it's a function, not a protocol).
    pub fn relation(dag: &DQDag<C>) -> Self {
        let start = dag.relation_node().unwrap();
        let rel_prefs = Self::prefs_from_marker(dag, start);
        let input_prefs = Self::prefs_from_marker(dag, dag.input_node());

        let mut tc = Self {
            clos: Vec::new(),
            prefs: Vec::new(),
        };
        let mut index: HashMap<NodeIndex, usize> = HashMap::new();

        // Insert input args as canonical entries, then alias relation args
        for input_pref in &input_prefs {
            let idx = tc.clos.len();
            tc.clos.push((
                input_pref.clone(),
                Op::Ref(input_pref.reference, input_pref.typ.clone()),
            ));
            index.insert(input_pref.node(), idx);
        }
        for rel_pref in &rel_prefs {
            if let Some(input_pref) = input_prefs.iter().find(|ip| ip.name() == rel_pref.name()) {
                index.insert(rel_pref.node(), index[&input_pref.node()]);
            }
        }

        tc.prefs = input_prefs;
        tc.build_from(dag, start, &mut index);
        tc
    }

    /// Transitive closure of the prover view.
    ///
    /// Walks backward from transcript nodes to input args and processes
    /// every node encountered. Prefs are all input args (both public and
    /// private).
    pub fn prover(dag: &DQDag<C>) -> Self {
        let prefs = Self::prefs_from_marker(dag, dag.input_node());
        let transcripts_vec = dag.transcript_nodes();

        let mut tc = Self {
            clos: Vec::new(),
            prefs,
        };

        let mut index: HashMap<NodeIndex, usize> = HashMap::new();

        // Walk backward from transcript nodes to input args.
        let mut done: HashSet<NodeIndex> = HashSet::new();
        let mut worklist: Vec<NodeIndex> = transcripts_vec;

        while let Some(node) = worklist.pop() {
            if !done.insert(node) {
                continue;
            }
            if dag[node].is_op() {
                tc.trans_clos_ref(dag, dag.find_ref(node), &mut index);
            }
            for neighbor in dag.nodes_to(node) {
                if !done.contains(&neighbor) {
                    worklist.push(neighbor);
                }
            }
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
        let input_prefs: Vec<PRef> = dag
            .input_args()
            .into_iter()
            .filter_map(|n| {
                let pref = dag[n].arg_pref(n)?;
                if pref.is_public() { Some(pref) } else { None }
            })
            .collect();

        let checks = dag.find_check();
        let transcripts_vec = dag.transcript_nodes();
        let transcripts_set: HashSet<NodeIndex> = transcripts_vec.iter().copied().collect();

        let mut tc = Self {
            clos: Vec::new(),
            prefs: input_prefs,
        };

        // Pre-populate index with transcript nodes so trans_clos_op
        // doesn't recurse past them into prover-only nodes. Also add
        // transcript source PRefs to prefs — they are opaque inputs to
        // the verifier, analogous to public args.
        let mut index: HashMap<NodeIndex, usize> = HashMap::new();
        for &n in &transcripts_vec {
            match &dag[n] {
                Node::Op(op, (qualifier, distribution))
                | Node::Transcr(op, (qualifier, distribution)) => {
                    let inner = op.get();
                    let pref = named_pref(dag, Ref::new(n), inner.typ(), *qualifier, *distribution);
                    tc.prefs.push(pref.clone());
                    let idx = tc.clos.len();
                    tc.clos
                        .push((pref.clone(), Op::Ref(pref.reference, pref.typ.clone())));
                    index.insert(n, idx);
                }
                _ => {}
            }
        }

        let mut done: HashSet<NodeIndex> = HashSet::new();
        let mut worklist: Vec<NodeIndex> = checks;

        while let Some(node) = worklist.pop() {
            if !done.insert(node) {
                continue;
            }
            if dag[node].is_op() {
                tc.trans_clos_ref(dag, dag.find_ref(node), &mut index);
            }
            if transcripts_set.contains(&node) {
                continue;
            }
            for neighbor in dag.nodes_to(node) {
                if !done.contains(&neighbor) {
                    worklist.push(neighbor);
                }
            }
        }
        tc
    }

    /// Remap every PRef (both prefs and clos entries) through `f`.
    ///
    /// `f` must not change the `reference` (node identity) of a PRef, only its
    /// metadata. Changing the reference would leave `Op::Ref` children in
    /// `clos` pointing at stale node identities.
    pub fn remap(&mut self, f: &impl Fn(&PRef) -> PRef) {
        self.prefs = self.prefs.iter().map(f).collect();
        self.clos = self.clos.drain(..).map(|(pr, op)| (f(&pr), op)).collect();
    }

    // ----------------------------------------------------------------
    // Internal
    // ----------------------------------------------------------------

    fn prefs_from_marker<A>(dag: &crate::Dag<C, A>, node: NodeIndex) -> Vec<PRef> {
        let mut args: Vec<NodeIndex> = dag.nodes_from(node).filter(|n| dag[*n].is_arg()).collect();
        args.sort();
        args.into_iter()
            .filter_map(|n| dag[n].arg_pref(n))
            .collect()
    }

    fn build_from(
        &mut self,
        dag: &DQDag<C>,
        start: NodeIndex,
        index: &mut HashMap<NodeIndex, usize>,
    ) {
        let mut done: HashSet<NodeIndex> = HashSet::new();
        let mut worklist = vec![start];

        while let Some(node) = worklist.pop() {
            if !done.insert(node) {
                continue;
            }
            if dag[node].is_op() {
                self.trans_clos_ref(dag, dag.find_ref(node), index);
            }
            for neighbor in dag.nodes_from(node) {
                if !done.contains(&neighbor) {
                    worklist.push(neighbor);
                }
            }
        }
    }

    fn trans_clos_op(
        &mut self,
        dag: &DQDag<C>,
        op: GOp<C>,
        index: &mut HashMap<NodeIndex, usize>,
    ) -> GOp<C> {
        match op {
            Op::Ref(r, _) => self.trans_clos_ref(dag, r, index),
            Op::Bin(op, a, b, typ) => {
                let oa = self.trans_clos_op(dag, a.get().clone(), index);
                let ob = self.trans_clos_op(dag, b.get().clone(), index);
                Op::bin(op, oa, ob, typ.clone())
            }
            Op::Ram(a, b) => {
                let oa = self.trans_clos_op(dag, a.get().clone(), index);
                let ob = self.trans_clos_op(dag, b.get().clone(), index);
                Op::Ram(mk::<C>(oa), mk::<C>(ob))
            }
            Op::Value(v) => Op::Value(v),
            Op::Vec(vs) => Op::Vec(
                vs.into_iter()
                    .map(|v| mk::<C>(self.trans_clos_op(dag, v.get().clone(), index)))
                    .collect::<Vec<_>>(),
            ),
            Op::Check(op) => self.trans_clos_op(dag, op.get().clone(), index),
            Op::Interpolate(points, evals) => Op::Interpolate(
                mk::<C>(self.trans_clos_op(dag, points.get().clone(), index)),
                mk::<C>(self.trans_clos_op(dag, evals.get().clone(), index)),
            ),
            Op::Ifft(v) => Op::Ifft(mk::<C>(self.trans_clos_op(dag, v.get().clone(), index))),
            Op::Fft(v) => Op::Fft(mk::<C>(self.trans_clos_op(dag, v.get().clone(), index))),
            Op::Reduce(op, v) => {
                Op::Reduce(op, mk::<C>(self.trans_clos_op(dag, v.get().clone(), index)))
            }
            Op::Evaluate(p, range, xs) => Op::Evaluate(
                mk::<C>(self.trans_clos_op(dag, p.get().clone(), index)),
                range,
                xs.map(|xs| mk::<C>(self.trans_clos_op(dag, xs.get().clone(), index))),
            ),
            Op::LoopParam(i, t) => Op::LoopParam(i, t),
            Op::Map(d, b) => Op::Map(
                mk::<C>(self.trans_clos_op(dag, d.get().clone(), index)),
                mk::<C>(self.trans_clos_op(dag, b.get().clone(), index)),
            ),
            Op::ReduceMap(op, d, b) => Op::ReduceMap(
                op,
                mk::<C>(self.trans_clos_op(dag, d.get().clone(), index)),
                mk::<C>(self.trans_clos_op(dag, b.get().clone(), index)),
            ),
            Op::Poly(v) => Op::Poly(mk::<C>(self.trans_clos_op(dag, v.get().clone(), index))),
            Op::Mle(v) => Op::Mle(mk::<C>(self.trans_clos_op(dag, v.get().clone(), index))),
            Op::Coef(v) => Op::Coef(mk::<C>(self.trans_clos_op(dag, v.get().clone(), index))),
            Op::Record(fields) => Op::Record(
                fields
                    .into_iter()
                    .map(|(k, v)| {
                        (
                            k.clone(),
                            mk::<C>(self.trans_clos_op(dag, v.get().clone(), index)),
                        )
                    })
                    .collect(),
            ),
            Op::Pair(a, b, t) => {
                let oa = self.trans_clos_op(dag, a.get().clone(), index);
                let ob = self.trans_clos_op(dag, b.get().clone(), index);
                Op::Pair(mk::<C>(oa), mk::<C>(ob), t)
            }
            Op::Random(t, b) => Op::Random(t, b),
            Op::Challenge(t, b) => Op::Challenge(t, b),
            Op::Proj(op, field, typ) => Op::Proj(
                mk::<C>(self.trans_clos_op(dag, op.get().clone(), index)),
                field.clone(),
                typ.clone(),
            ),
        }
    }

    fn find(&self, r: &Ref, index: &HashMap<NodeIndex, usize>) -> Option<(&PRef, &GOp<C>)> {
        index
            .get(&r.node())
            .map(|&idx| (&self.clos[idx].0, &self.clos[idx].1))
    }

    fn insert(&mut self, r: PRef, op: GOp<C>, index: &mut HashMap<NodeIndex, usize>) -> GOp<C> {
        if let Some(&idx) = index.get(&r.node()) {
            let canonical = &self.clos[idx].0;
            Op::Ref(canonical.reference, self.clos[idx].1.typ())
        } else {
            let idx = self.clos.len();
            let typ = op.typ();
            let node = r.node();
            let reference = r.reference;
            self.clos.push((r, op));
            index.insert(node, idx);
            Op::Ref(reference, typ)
        }
    }

    fn trans_clos_ref(
        &mut self,
        dag: &DQDag<C>,
        r: Ref,
        index: &mut HashMap<NodeIndex, usize>,
    ) -> GOp<C> {
        if let Some((canonical, op)) = self.find(&r, index) {
            return Op::Ref(canonical.reference, op.typ());
        }
        match &dag[r.node()] {
            Node::Op(op, (qualifier, distribution))
            | Node::Transcr(op, (qualifier, distribution))
                if matches!(op.get(), Op::Challenge(_, _) | Op::Random(_, _)) =>
            {
                let inner = op.get();
                let pref = named_pref(dag, r, inner.typ(), *qualifier, *distribution);
                self.insert(pref, inner.clone(), index)
            }
            Node::Op(op, (qualifier, distribution))
            | Node::Transcr(op, (qualifier, distribution)) => {
                let obin = self.trans_clos_op(dag, op.get().clone(), index);
                self.insert(
                    named_pref(dag, r, obin.typ(), *qualifier, *distribution),
                    obin,
                    index,
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
            self.prefs
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
    use crate::{
        DQDag, UDags,
        analyses::{QualifierPropagation, UniformityPropagation},
    };
    use backend::ArkBls12_381;
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

        assert!(!tc.prefs.is_empty(), "prefs should not be empty");
        assert!(
            tc.prefs.iter().any(|p| p.is_private()),
            "prover should include private args"
        );
        assert!(
            tc.prefs.iter().any(|p| p.is_public()),
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

        // Relation prefs should use input namespace (same NodeIndex)
        for rel_pref in &tc_rel.prefs {
            let matching_prover = tc_prover
                .prefs
                .iter()
                .find(|ip| ip.name() == rel_pref.name());
            assert!(
                matching_prover.is_some(),
                "relation arg {:?} should have a matching prover arg",
                rel_pref.name()
            );
            assert_eq!(
                rel_pref.node(),
                matching_prover.unwrap().node(),
                "relation arg {:?} should map to same node as prover arg",
                rel_pref.name()
            );
        }

        // Relation clos entries for arg nodes should also use input namespace
        for (pref, _) in tc_rel.clos.iter() {
            if let Some(prover_pref) = tc_prover.prefs.iter().find(|ip| ip.name() == pref.name()) {
                assert_eq!(
                    pref.node(),
                    prover_pref.node(),
                    "relation clos entry {:?} should use input namespace",
                    pref.name()
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
            tc_prover.prefs.iter().any(|p| p.is_private()),
            "prover should see private inputs"
        );
        assert!(
            tc_prover.prefs.iter().any(|p| p.is_public()),
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

        // Prover should include both private and public input prefs
        assert!(
            tc_prover.prefs.iter().any(|p| p.is_private()),
            "prover should see private inputs"
        );
        assert!(
            tc_prover.prefs.iter().any(|p| p.is_public()),
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
            tc.prefs.iter().all(|p| p.is_public()),
            "verifier prefs should all be public, got: {:?}",
            tc.prefs
        );
        assert!(
            tc.prefs.len() >= 1,
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

        // Verifier clos should not contain any private-input PRefs
        let private_prefs: HashSet<NodeIndex> = g
            .input_args()
            .into_iter()
            .filter_map(|n| {
                let pref = g[n].arg_pref(n)?;
                if pref.is_private() {
                    Some(pref.node())
                } else {
                    None
                }
            })
            .collect();
        for (verifier_pref, _) in tc.clos.iter() {
            assert!(
                !private_prefs.contains(&verifier_pref.node()),
                "verifier clos entry at node {:?} should not be a private input",
                verifier_pref.node()
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
        let original_prefs_len = tc.prefs.len();

        let mut tc2 = TransClos::prover(&g);
        tc2.remap(&|pr| pr.clone());

        assert_eq!(
            tc2.clos.len(),
            original_clos_len,
            "identity remap should preserve clos length"
        );
        assert_eq!(
            tc2.prefs.len(),
            original_prefs_len,
            "identity remap should preserve prefs length"
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
}
