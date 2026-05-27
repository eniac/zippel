use crate::scheduler::{Cost, CostModel, CriticalPathScheduler, Scheduler, TDag};
use crate::tests::test_helpers::TestConfig;
use crate::{Dep, Node, Op, Ref, UDag, mk};
use backend::{ATyp, ArkConfig};
use lang::typ::Nothing;
use petgraph::graph::NodeIndex;

struct LinearCost;

impl<C: ArkConfig> CostModel<C, Ref> for LinearCost {
    fn cost(&self, op: &Op<C, Ref>, nthreads: usize) -> Cost {
        match op {
            Op::Random(ATyp::Vec(_, weight), _) => Cost(*weight as f64 / nthreads as f64),
            _ => Cost(1.0),
        }
    }
}

fn add_weighted_node(dag: &mut UDag<TestConfig>, weight: usize) -> NodeIndex {
    dag.add_node(Node::Op(
        mk::<TestConfig>(Op::random(ATyp::vec_scalar(weight))),
        Nothing,
    ))
}

fn allocated_threads(dag: &TDag<TestConfig>, node: NodeIndex) -> usize {
    match &dag[node] {
        Node::Op(_, allocation) | Node::Transcr(_, allocation) => allocation.get(),
        _ => panic!("expected schedulable node"),
    }
}

#[test]
fn critical_path_scheduler_prioritizes_span_over_local_cost() {
    let mut dag = UDag::new();
    let chain_first = add_weighted_node(&mut dag, 10);
    let chain_second = add_weighted_node(&mut dag, 10);
    let off_critical = add_weighted_node(&mut dag, 9);
    dag.add_edge(chain_first, chain_second, Dep::data());

    let scheduled = CriticalPathScheduler::new(&dag, 2, &LinearCost, 0.0).schedule(dag);

    assert_eq!(allocated_threads(&scheduled, chain_first), 2);
    assert_eq!(allocated_threads(&scheduled, chain_second), 2);
    assert_eq!(allocated_threads(&scheduled, off_critical), 1);
}

#[test]
fn critical_path_scheduler_shifts_threads_when_critical_branch_changes() {
    let mut dag = UDag::new();
    let long_branch = add_weighted_node(&mut dag, 18);
    let shorter_branch = add_weighted_node(&mut dag, 8);

    let scheduled = CriticalPathScheduler::new(&dag, 3, &LinearCost, 0.0).schedule(dag);

    assert_eq!(allocated_threads(&scheduled, long_branch), 3);
    assert_eq!(allocated_threads(&scheduled, shorter_branch), 2);
}

#[test]
fn critical_path_scheduler_is_deterministic_and_allocates_at_least_one_thread() {
    let mut dag = UDag::new();
    let first = add_weighted_node(&mut dag, 12);
    let second = add_weighted_node(&mut dag, 12);
    let third = add_weighted_node(&mut dag, 6);
    dag.add_edge(first, third, Dep::data());
    dag.add_edge(second, third, Dep::data());

    let scheduled_once =
        CriticalPathScheduler::new(&dag, 3, &LinearCost, 0.0).schedule(dag.clone());
    let scheduled_twice = CriticalPathScheduler::new(&dag, 3, &LinearCost, 0.0).schedule(dag);

    for node in [first, second, third] {
        let first_allocation = allocated_threads(&scheduled_once, node);
        assert!(first_allocation >= 1);
        assert_eq!(
            first_allocation,
            allocated_threads(&scheduled_twice, node),
            "allocation should be stable for {node:?}",
        );
    }
}
