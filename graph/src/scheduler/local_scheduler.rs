use crate::{Dag, UDag, Ref, Node};
use crate::scheduler::{TDag, CostModel, Scheduler, ThreadAlloc};
use backend::ArkConfig;
use std::collections::HashMap;
use petgraph::graph::NodeIndex;
pub struct LocalScheduler {
    cost_map: HashMap<NodeIndex, usize>,
}

impl LocalScheduler {
    pub fn new_with_system<C: ArkConfig, CM: CostModel<C, Ref>>(dag: &UDag<C>, cost_model: &CM, min_gap: f64) -> Self {
        let num_threads: usize = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1);
        Self::new(dag, num_threads - 1 , cost_model, min_gap)
    }

    pub fn new<C: ArkConfig, CM: CostModel<C, Ref>>(dag: &UDag<C>, num_threads: usize, cost_model: &CM, min_gap: f64) -> Self {
        let nodes = dag.nodes_indices();
        let mut cost_map: HashMap<NodeIndex, usize> = HashMap::new();
        for node in nodes {
            match &dag[node] {
                Node::Inp(_, _) | Node::Rel(_, _) => {
                    for _ in 0..1 {
                        cost_map.insert(node, 1); 
                    };
                }
                Node::Op(op, _) | Node::Transcr(op, _) => {
                    let starting = cost_model.cost(op, 1).0;
                    let mut previous = starting;
                    let mut set = false;
                    for t in 2..=num_threads {
                        let current = cost_model.cost(op, t).0;
                        let percent_change = (previous - current) / previous * 100.0;
                        if percent_change < min_gap {
                            set = true;
                            cost_map.insert(node, t - 1);
                            break;
                        }
                        previous = current;
                    }
                    if !set {
                        cost_map.insert(node, num_threads);
                    }
                }
            }
        }
        LocalScheduler { cost_map }
    }
}

impl Scheduler for LocalScheduler {
    fn schedule<C: ArkConfig>(self, dag: UDag<C>) -> TDag<C> {
        Dag { graph: dag.graph.map(
            |a, n| n.with_annotation(ThreadAlloc(self.cost_map[&a])),
            |_, e| e.clone(),
        ), vctx: dag.vctx.clone(), transcript_vars: dag.transcript_vars.clone() }
    }
}