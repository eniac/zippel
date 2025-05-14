#![feature(box_patterns)]
use std::thread;
use petgraph::graph::{self as petgraph_graph, EdgeIndex, NodeIndex};
use petgraph::graph::Graph;
use std::time::{Duration, SystemTime};
use std::sync::{Arc, Mutex};
use rayon::{string, ThreadPoolBuilder};
use graph::{UDag, Dag, Node, Op};
use backend::{ArkConfig, ATyp, Value};
use std::collections::{HashMap, HashSet};

pub struct RuntimeInformation<C: ArkConfig> {
    thread_num: usize,
    return_value: Mutex<Value<C>>, 
    finished_requirements: Mutex<Vec<NodeIndex>>
}

pub struct MutexGraph<C: ArkConfig>(pub Dag<C, Arc<RuntimeInformation<C>>>);

pub type TDag<C: ArkConfig> = Dag<C, usize>;

impl<C: ArkConfig> MutexGraph<C> {
    pub fn new(tdag: TDag<C>) -> Self {
        MutexGraph(Graph::new())
    }

    pub fn add_node(&mut self, n: Node<C, A>) -> NodeIndex {
        self.0.add_node(Arc::new(n))
    }

    pub fn add_edge(&mut self, a: NodeIndex, b: NodeIndex) -> EdgeIndex {
        self.0.add_edge(a, b, ())
    }
}

pub fn convert_graph<C: ArkConfig, A>(graph: &mut Dag<C, A>) -> MutexGraph<C, A> {
    let mut mutex_graph: MutexGraph<C, A> = MutexGraph::new();

    // for node in graph.node_indices() {
        // mutex_graph.add_node(graph.get_node(node).clone());
    // }

    return mutex_graph;
}

pub fn run_graph<C:ArkConfig, A>(graph: &mut MutexGraph<C, A>) {
    let mut ready_nodes: Vec<NodeIndex> = Vec::new();
    let mut running_nodes: Vec<NodeIndex> = Vec::new();

    for node in graph.0.node_indices() {
        if graph.0.neighbors_directed(node, petgraph::Direction::Incoming).count() == 0 {
            ready_nodes.push(node);
        }
    }
    let mut max_threads : usize = num_cpus::get();
    println!("max threads - {}", max_threads);
    let mut active_threads: usize = 1; 

    while !ready_nodes.is_empty() || !running_nodes.is_empty() {
        // Check if anything that is in ready nodes can start running
        let mut remove_from_ready : Vec<NodeIndex> = Vec::new();
        for i in 0..ready_nodes.len() {
            let node_index = ready_nodes[i];
            let thread_num_val = 1; // Cost model graph.0[node_index].threads_num
            if thread_num_val <= ((max_threads - active_threads) as u32) {
 
                let pool = rayon::ThreadPoolBuilder::new().num_threads( thread_num_val as usize).build().unwrap();

                // let dependencies: Vec<_> = graph.0
                //     .neighbors_directed(node_index, petgraph::Direction::Incoming)
                //     .map(|dep| graph.0[dep].return_value.lock().unwrap().unwrap())
                //     .collect();

                // let value_num_node = graph.0[node_index].value_num;
                let mut node = Arc::clone(&graph.0[node_index]);
                pool.spawn(move || {
                    println!("{:?}", node_index);
                });
                



                running_nodes.push(node_index);
                active_threads += thread_num_val as usize;
                remove_from_ready.push(node_index)
                
            }
        }

        let remove_set: HashSet<NodeIndex> = remove_from_ready.into_iter().collect();
        ready_nodes.retain(|x| !remove_set.contains(x));       

        let mut remove_from_running : Vec<NodeIndex> = Vec::new();
        for i in 0..running_nodes.len() {
            let node_index = running_nodes[i];
            // let mut return_val = graph.0[node_index].return_value.lock().unwrap();
            // let mut finished: bool =  !return_val.is_none();
            // drop(return_val);
            let finished: bool = true; 
            if finished {
                remove_from_running.push(node_index);
                active_threads -= 1; //graph.0[node_index].threads_num as usize;

                let mut fix_finished_requirements: Vec<NodeIndex> = Vec::new();
                let dependents = graph.0.neighbors_directed(node_index, petgraph::Direction::Outgoing) ;
                for dependent in dependents{
                    let incoming_nodes: Vec<_> = graph.0.neighbors_directed(dependent, petgraph::Direction::Incoming).collect();
                    let mut ready: bool = true;
                    // for income_node in &incoming_nodes {
                    //     let mut finished_requirements_lock = graph.0[dependent].finished_requirements.lock().unwrap();
                    //     if !(*income_node == node_index || finished_requirements_lock.contains(income_node)) {
                    //         ready = false;
                    //         break;
                    //     }
                    // }

                    if ready {
                        ready_nodes.push(dependent);
                    } else {
                        fix_finished_requirements.push(dependent);
                    }
                }
                // for dependent in fix_finished_requirements {
                //     let mut node = Arc::clone(&graph.0[dependent]);
                //     node.add_finished_requirements(node_index);
                // }
            }
        }

        let remove_finished_set: HashSet<NodeIndex> = remove_from_running.into_iter().collect();
        running_nodes.retain(|x| !remove_finished_set.contains(x));      
    }
}

fn main() {
    let ex1 = Exp::combine(Exp::Var(0), Exp::bool(false));
    println!("[{:?}] Staging {:?}", SystemTime::now(), ex1);
    let f = stage(ex1.clone());
    let inputs = vec![Value::Bool(true)];
    println!("[{:?}] Evaluating {:?}", SystemTime::now(), ex1);
    println!("Result {:?}", f(inputs));
}
