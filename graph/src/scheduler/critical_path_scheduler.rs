use crate::scheduler::{CostModel, Scheduler, TDag, ThreadAlloc};
use crate::{Dag, Node, Ref, UDag};
use backend::ArkConfig;
use petgraph::Direction;
use petgraph::algo::toposort;
use petgraph::graph::NodeIndex;
use std::cmp::Ordering;
use std::collections::HashMap;

const EPSILON: f64 = 1e-9;

pub struct CriticalPathScheduler {
    cost_map: HashMap<NodeIndex, usize>,
}

#[derive(Clone, Copy)]
struct Candidate {
    node: NodeIndex,
    makespan: f64,
    improvement: f64,
    local_improvement: f64,
}

impl CriticalPathScheduler {
    pub fn new_with_system<C: ArkConfig, CM: CostModel<C, Ref>>(
        dag: &UDag<C>,
        cost_model: &CM,
        min_makespan_improvement: f64,
    ) -> Self {
        let max_threads: usize = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1)
            .max(2);
        Self::new(dag, max_threads - 1, cost_model, min_makespan_improvement)
    }

    pub fn new<C: ArkConfig, CM: CostModel<C, Ref>>(
        dag: &UDag<C>,
        max_threads: usize,
        cost_model: &CM,
        min_makespan_improvement: f64,
    ) -> Self {
        let max_threads = max_threads.max(1);
        let topo = toposort(&dag.graph, None).expect("cannot schedule a cyclic graph");
        let mut allocations = initial_allocations(dag);
        let durations = build_duration_curves(dag, max_threads, cost_model);
        let mut schedulable_nodes: Vec<NodeIndex> = durations.keys().copied().collect();
        schedulable_nodes.sort();

        let mut current_makespan = estimate_makespan(dag, &topo, &allocations, &durations);
        loop {
            let best = schedulable_nodes
                .iter()
                .filter_map(|node| {
                    let current_threads = allocations[node];
                    if current_threads >= max_threads {
                        return None;
                    }

                    let mut trial_allocations = allocations.clone();
                    trial_allocations.insert(*node, current_threads + 1);
                    let trial_makespan =
                        estimate_makespan(dag, &topo, &trial_allocations, &durations);
                    let improvement = current_makespan - trial_makespan;
                    if improvement <= min_makespan_improvement {
                        return None;
                    }

                    Some(Candidate {
                        node: *node,
                        makespan: trial_makespan,
                        improvement,
                        local_improvement: durations[node][current_threads]
                            - durations[node][current_threads + 1],
                    })
                })
                .max_by(compare_candidates);

            let Some(best) = best else {
                break;
            };
            allocations.insert(best.node, allocations[&best.node] + 1);
            current_makespan = best.makespan;
        }

        CriticalPathScheduler {
            cost_map: allocations,
        }
    }
}

fn initial_allocations<C: ArkConfig>(dag: &UDag<C>) -> HashMap<NodeIndex, usize> {
    dag.nodes_indices()
        .into_iter()
        .map(|node| (node, 1))
        .collect()
}

fn build_duration_curves<C: ArkConfig, CM: CostModel<C, Ref>>(
    dag: &UDag<C>,
    max_threads: usize,
    cost_model: &CM,
) -> HashMap<NodeIndex, Vec<f64>> {
    dag.nodes_indices()
        .into_iter()
        .filter_map(|node| match &dag[node] {
            Node::Op(op, _) | Node::Transcr(op, _) => Some((
                node,
                std::iter::once(0.0)
                    .chain((1..=max_threads).map(|threads| {
                        let cost = cost_model.cost(op, threads).0;
                        assert!(
                            cost.is_finite() && cost >= 0.0,
                            "cost model returned invalid cost {cost} for {threads} threads",
                        );
                        cost
                    }))
                    .collect(),
            )),
            Node::Inp(_) | Node::Rel(_) | Node::Arg(_, _, _, _, _) => None,
        })
        .collect()
}

fn estimate_makespan<C: ArkConfig>(
    dag: &UDag<C>,
    topo: &[NodeIndex],
    allocations: &HashMap<NodeIndex, usize>,
    durations: &HashMap<NodeIndex, Vec<f64>>,
) -> f64 {
    let mut finish_times: HashMap<NodeIndex, f64> = HashMap::new();
    let mut makespan = 0.0;

    for node in topo {
        let start_time = dag
            .graph
            .neighbors_directed(*node, Direction::Incoming)
            .map(|predecessor| finish_times[&predecessor])
            .fold(0.0, f64::max);
        let duration = durations
            .get(node)
            .map(|duration_curve| duration_curve[allocations[node]])
            .unwrap_or(0.0);
        let finish_time = start_time + duration;
        finish_times.insert(*node, finish_time);
        makespan = f64::max(makespan, finish_time);
    }

    makespan
}

fn compare_candidates(left: &Candidate, right: &Candidate) -> Ordering {
    compare_f64(left.improvement, right.improvement)
        .then_with(|| compare_f64(left.local_improvement, right.local_improvement))
        .then_with(|| right.node.cmp(&left.node))
}

fn compare_f64(left: f64, right: f64) -> Ordering {
    if (left - right).abs() <= EPSILON {
        Ordering::Equal
    } else {
        left.partial_cmp(&right)
            .expect("candidate improvements should be finite")
    }
}

impl Scheduler for CriticalPathScheduler {
    fn schedule<C: ArkConfig>(self, dag: UDag<C>) -> TDag<C> {
        Dag {
            graph: dag.graph.map(
                |node, graph_node| {
                    graph_node.with_annotation(ThreadAlloc::new(self.cost_map[&node]))
                },
                |_, edge| *edge,
            ),
            vctx: dag.vctx.clone(),
            transcript_vars: dag.transcript_vars.clone(),
        }
    }
}
