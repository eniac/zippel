//! Prover, verifier and relation projections of a [`Dag`].

use super::*;
use lang::typ::Distribution;

/// Methods requiring hash-consing
impl<C: Backend, A> Dag<C, A> {
    /// Rewrites every `NodeIndex` — both the graph's own and those buried
    /// inside [`Ref`]s in hash-consed operations — through `f`.
    ///
    /// This is what makes subgraph projection sound: a projected DAG is built
    /// with cloned ops that still point at source-graph indices, and this pass
    /// translates them to the projection's own indices.
    pub fn map_node_indices<F: Fn(NodeIndex) -> NodeIndex>(&self, f: &F) -> Dag<C, A>
    where
        A: Clone,
    {
        Dag {
            graph: self
                .graph
                .map(|_, w| respan(w, |node| node.map_node_indices(f)), |_, e| *e),
            bindings: self.bindings.clone(),
            transcript_vars: self.transcript_vars.clone(),
        }
    }

    /// Get the prover graph, by reachability analysis starting from the transcript nodes
    ///
    /// Seeds are `prover_roots` and the walk runs backwards along
    /// incoming edges. The input marker and its `Arg` nodes are replicated
    /// first so the projection keeps index 0 as its input and the same argument
    /// structure. Returns the projected DAG together with the map from source
    /// node indices to references in it.
    ///
    /// # Panics
    /// Panics if remapping encounters a reference to a source node that was not
    /// copied into the projection, which would mean the reachability walk and
    /// the operations' references disagree.
    pub fn project_prover(&self) -> (Dag<C, A>, HashMap<NodeIndex, Ref>)
    where
        A: Clone,
    {
        let mut prover = Dag::new();
        // Add all nodes to the prover graph: everything backwards-reachable
        // from the prover's obligations (see `prover_roots`).
        let mut worklist: Vec<NodeIndex> = self.prover_roots();
        // Map old node indices to new references
        let mut node_map: HashMap<NodeIndex, Ref> = HashMap::new();

        // Add input node first, so it is NodeIndex::new(0)
        let n_input = prover.add_weight(self.graph[self.input_node()].clone());
        node_map.insert(self.input_node(), Ref(n_input));
        // Replicate input Arg nodes (so the projected dag has the same arg structure).
        for arg_idx in self.input_args() {
            let new_arg = prover.add_weight(self.graph[arg_idx].clone());
            prover.add_edge(n_input, new_arg, Dep::data());
            node_map.insert(arg_idx, Ref(new_arg));
        }

        while let Some(n) = worklist.pop() {
            if node_map.contains_key(&n) {
                continue;
            }
            // Add node to prover graph
            let new_node = prover.add_weight(self.graph[n].clone());
            node_map.insert(n, Ref(new_node));

            // Add previous neighbors to worklist
            for e in self.graph.edges_directed(n, Direction::Incoming) {
                // Add neighbors to worklist
                worklist.push(e.source());
            }
        }

        // Propagate bindings and transcript_vars for mapped nodes
        for (old_idx, new_ref) in &node_map {
            if let Some(names) = self.bindings.get(old_idx) {
                prover.bindings.insert(&new_ref.node(), names);
            }
            if let Some(is_transcript) = self.transcript_vars.get(old_idx) {
                prover
                    .transcript_vars
                    .insert(&new_ref.node(), is_transcript);
            }
        }

        // Add edges to prover graph using the mapped node indices
        let source_input_node = self.input_node();
        for edge_ref in self.graph.edge_references() {
            let old_source_idx = edge_ref.source();
            let old_target_idx = edge_ref.target();
            let weight = *edge_ref.weight();

            if old_source_idx == source_input_node && self[old_target_idx].is_input_arg() {
                continue;
            }

            if let (Some(new_source_idx), Some(new_target_idx)) =
                (node_map.get(&old_source_idx), node_map.get(&old_target_idx))
            {
                prover.add_edge(new_source_idx.node(), new_target_idx.node(), weight);
            }
        }

        // Remap node indices in Ref to the new node indices
        let remapped = prover.map_node_indices(&|n| {
            node_map.get(&n).map(|r| r.node()).unwrap_or_else(|| {
                panic!(
                    "Aliasing error: node {}: {} in prover not found in {} protocol dag",
                    n.index(),
                    self[n].drop_annotation(),
                    self.name()
                )
            })
        });

        (remapped, node_map)
    }

    /// Get the relation graph, by reachability analysis starting from the relation node
    ///
    /// # Errors
    /// Returns [`GraphError::RelationNotFound`] if this DAG has no `Node::Rel`
    /// marker, i.e. it is a `fun` rather than a protocol.
    pub fn project_relation(&self) -> Result<Dag<C, A>, GraphError>
    where
        A: Clone,
    {
        let mut g_relation = Dag::new();
        let relation_node = self.relation_node().ok_or_else(|| {
            let name = Spanned::new(self.name(), self.span(self.input_node()));
            GraphError::relation_not_found(&name)
        })?;

        let mut worklist = vec![relation_node];
        let mut node_map_rel = HashMap::<NodeIndex, NodeIndex>::new();

        while let Some(n) = worklist.pop() {
            if node_map_rel.contains_key(&n) {
                continue;
            }
            let new_node = g_relation.add_weight(self.graph[n].clone());
            node_map_rel.insert(n, new_node);
            for e in self.graph.edges_directed(n, Direction::Outgoing) {
                worklist.push(e.target());
            }
        }

        // Add edges to relation graph using the mapped node indices
        for edge_ref in self.graph.edge_references() {
            let old_source_idx = edge_ref.source();
            let old_target_idx = edge_ref.target();
            let weight = *edge_ref.weight();

            if let (Some(new_source_idx), Some(new_target_idx)) = (
                node_map_rel.get(&old_source_idx),
                node_map_rel.get(&old_target_idx),
            ) {
                g_relation.add_edge(*new_source_idx, *new_target_idx, weight);
            }
        }
        Ok(g_relation.map_node_indices(&|n| node_map_rel[&n]))
    }

    /// Rebuilds the DAG with every operation rewritten by `f` and re-interned
    /// through the hash-consing factory. Annotations and edges are preserved.
    pub fn map_ops<F: Fn(&GOp<C>) -> GOp<C>>(&mut self, f: &F) -> Dag<C, A>
    where
        A: Clone,
    {
        Dag {
            graph: self.graph.map(
                |_, w| {
                    respan(w, |node| match node {
                        Node::Op(op, ann) => Node::Op(mk::<C>(f(op)), ann.clone()),
                        Node::Transcr(op, ann) => Node::Transcr(mk::<C>(f(op)), ann.clone()),
                        _ => node.clone(),
                    })
                },
                |_, e| *e,
            ),
            bindings: self.bindings.clone(),
            transcript_vars: self.transcript_vars.clone(),
        }
    }

    /// Projects verifier computations by walking backwards from checks and challenges.
    /// Prover messages stop data-flow traversal; the entire transcript is retained.
    ///
    /// Instance arguments are replicated, challenge transcript nodes are kept
    /// as computations, and each non-challenge (proof) transcript node is
    /// turned into a `ArgKind::TranscriptInput` argument the verifier reads
    /// from the proof instead of recomputing.
    ///
    /// # Errors
    /// Returns [`GraphError::PrivateValueInVerifier`] if the backwards walk
    /// from a `Verify` node or challenge reaches a non-instance argument or a `random`
    /// sample without passing through the transcript — the verifier cannot
    /// depend on private data.
    ///
    /// # Panics
    /// Panics if the protocol contains no terminal `Verify` node, so there is
    /// nothing for the verifier to check.
    pub fn project_verifier(&self) -> Result<Dag<C, A>, GraphError>
    where
        A: Clone,
    {
        let transcript = self.transcript_nodes();
        let selected = self.verifier_nodes(&transcript)?;
        Ok(self.build_verifier(&selected, &transcript))
    }

    /// Selects verifier obligations and their computations, reporting the first private use.
    fn verifier_nodes(&self, transcript: &[NodeIndex]) -> Result<Vec<NodeIndex>, GraphError> {
        let mut selected = vec![self.input_node()];
        selected.extend(
            self.input_args()
                .into_iter()
                .filter(|&n| matches!(&self[n], Node::Arg(_, _, qual, _, _) if qual.is_instance())),
        );
        selected.extend_from_slice(transcript);
        let mut retained: HashSet<_> = selected.iter().copied().collect();
        // Proof messages and instance inputs are leaves. Challenges are retained,
        // but still need a visit to select and validate their exclusion operands.
        let mut visited: HashSet<_> = selected
            .iter()
            .copied()
            .filter(|&n| !self[n].is_challenge())
            .collect();

        // Start with checks, then challenges, preserving diagnostic traversal order.
        let mut worklist = self.find_verify();
        assert!(!worklist.is_empty(), "No verifier check found");
        worklist.extend(
            transcript
                .iter()
                .copied()
                .filter(|&n| self[n].is_challenge()),
        );
        // Each reached node ↦ the node that needed it, back to a check or a
        // challenge, for reporting leaks.
        let mut via: HashMap<NodeIndex, NodeIndex> = HashMap::new();

        while let Some(n) = worklist.pop() {
            if !visited.insert(n) {
                continue;
            }
            let Some(op) = self[n].op() else {
                continue;
            };

            // A `random` sample the verifier needs is a leak: the verifier would
            // draw its own value instead of the prover's.
            if matches!(&**op, Op::Random(_, _)) {
                // Reported where it is named, or at `random<..>` if it never is.
                let binding = self.binding(n);
                let (steps, check) = self.use_path(&via, via.get(&n).copied().unwrap_or(n));
                return Err(GraphError::private_value_in_verifier(
                    PrivateValue::Random,
                    binding.map(|b| b.node.clone()),
                    binding.map_or_else(|| self.span(n), |b| b.span.clone()),
                    steps,
                    check,
                ));
            }

            // So is any reference to a non-instance argument.
            for r in op.references() {
                let target = r.node();
                if self[target].is_input_arg()
                    && let Node::Arg(name, _, qual, _, _) = &self[target]
                    && !qual.is_instance()
                {
                    let (steps, check) = self.use_path(&via, n);
                    return Err(GraphError::private_value_in_verifier(
                        PrivateValue::Arg(*qual),
                        Some(name.clone()),
                        self.span(target),
                        steps,
                        check,
                    ));
                }
            }

            if retained.insert(n) {
                selected.push(n);
            }

            // Add parent neighbors to worklist
            for e in self.graph.edges_directed(n, Direction::Incoming) {
                if !retained.contains(&e.source()) {
                    debug!(
                        "Adding parent {} of {} to worklist",
                        self[e.source()].drop_annotation(),
                        self[n].drop_annotation()
                    );
                    via.entry(e.source()).or_insert(n);
                    worklist.push(e.source());
                }
            }
        }

        Ok(selected)
    }

    /// Builds proof reads and retained computations, then connects their dependencies.
    fn build_verifier(&self, selected: &[NodeIndex], transcript: &[NodeIndex]) -> Dag<C, A>
    where
        A: Clone,
    {
        let mut verifier = Dag::new();
        let input = self.input_node();
        let new_input = verifier.add_weight(self.graph[input].clone());
        let mut node_map = HashMap::from([(input, new_input)]);
        let mut taken = HashSet::new();

        for &n in selected {
            if let Node::Arg(name, _, _, _, _) = &self[n] {
                let arg = verifier.add_weight(self.graph[n].clone());
                verifier.add_edge(new_input, arg, Dep::data());
                node_map.insert(n, arg);
                taken.insert(name.clone());
            }
        }

        // Allocate proof inputs in transcript order. Messages read them directly;
        // their prover operations never enter the verifier graph.
        for &n in transcript.iter().filter(|&&n| self[n].is_proof()) {
            let Node::Transcr(op, ann) = &self[n] else {
                unreachable!("prover message must be a transcript node");
            };
            let name = self.find_var(n).expect("prover message must have a name");
            let typ = op.typ();
            let arg = verifier.add_node(
                Node::Arg(
                    unique_name(&name, &mut taken),
                    typ.clone(),
                    Qualifier::Instance,
                    Distribution::default(),
                    ArgKind::TranscriptInput,
                ),
                self.span(n),
            );
            verifier.add_edge(new_input, arg, Dep::data());
            let message = verifier.add_node(
                Node::Transcr(mk::<C>(GOp::var(&name, arg, typ)), ann.clone()),
                self.span(n),
            );
            node_map.insert(n, message);
        }

        // Finish the map before translating any source operations. Allocation
        // order does not need to be topological.
        for &n in selected {
            node_map
                .entry(n)
                .or_insert_with(|| verifier.add_weight(self.graph[n].clone()));
        }
        for &n in selected {
            if self[n].is_op() && !self[n].is_proof() {
                *verifier.node_mut(node_map[&n]) = self[n].map_node_indices(&|n| node_map[&n]);
            }
        }

        // Data edges come from final verifier operations, including proof reads.
        for n in verifier.node_indices_vec() {
            for reference in verifier[n].references() {
                verifier.add_edge(reference.node(), n, Dep::data());
            }
        }
        // Keep the entire transcript chain, including its input-marker anchor.
        for &n in transcript {
            if let Some(edge) = self.transcript_edge(n, Direction::Incoming) {
                verifier.add_edge(node_map[&edge.source()], node_map[&n], *edge.weight());
            }
        }

        verifier
    }
}
