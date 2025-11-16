#![feature(associated_type_defaults)]
#![feature(trait_alias)]
#![feature(box_patterns)]
use petgraph::graph::NodeIndex;
use spongefish::{ProverState, DuplexSpongeInterface, BytesToUnitSerialize};
use std::sync::{Arc, Mutex};
use backend::{ArkConfig, Value, value_to_bytes};
use graph::{domain_seperator, Dag, Node, Op, GOp};
use graph::scheduler::{ThreadAlloc, TDag};
use rand::rngs::ThreadRng;
use lang::ast::BinOp;
use std::collections::HashSet;
use lang::id::Vid;
use graph::Ref;
use share::Ctx;

pub struct RuntimeInformation<C: ArkConfig> {
    thread_num: usize,
    return_value: Mutex<Option<Value<C>>>, 
    finished_requirements: Mutex<Vec<NodeIndex>>
}

impl<C: ArkConfig> RuntimeInformation<C> {
    pub fn new(thread_num: usize) -> Self {
        RuntimeInformation {
            thread_num, return_value: Mutex::new(None), finished_requirements: Mutex::new(Vec::new()) 
        }
    }
}


pub struct MutexGraph<C: ArkConfig> {
    mutex_graph: Dag<C, Arc<RuntimeInformation<C>>>,
}

impl<C: ArkConfig> MutexGraph<C> {
    pub fn new(tdag: TDag<C>) -> Self {
        MutexGraph {
            mutex_graph:tdag.map_annotations(&|_, nthreads: &ThreadAlloc| Arc::new(RuntimeInformation::<C>::new(
                nthreads.get()
            ))),
        }
    }

    pub fn print_edges(&self) {
        for node in self.mutex_graph.node_indices() {
            for neighbor in self.mutex_graph.neighbors_directed(node, petgraph::Direction::Outgoing) {
                println!("Edge from {:?} to {:?}", node, neighbor);
            }
        }
    }
    
    pub fn get_value(&self, r: graph::Ref, inputs: Arc<Ctx<Vid, Value<C>>>) -> Value<C> {
        let node = r.node();

        match &self.mutex_graph[node] {
            Node::Op(_, annotation) 
            | Node::Transcr(_, annotation) => {
                let return_val = annotation.return_value.lock().unwrap();
                match &*return_val {
                    Some(val) => val.clone(),
                    None => panic!("Value should exist")
                }
            },
            Node::Inp(_, _) | Node::Rel(_, _) => {
                let vid = r.var().expect("Input should be a variable");
                inputs.get(&vid)
                .expect(format!("Value for {} should exist", vid).as_str())
                .clone()
            }
        }
    }

    pub fn handle_op(&self, operation: &Op<C, Ref>, inputs: Arc<Ctx<Vid, Value<C>>>) -> Value<C>{
        match operation {
            Op::Value(val) => {
                return val.clone();
            },
            Op::Ref(r, _ATyp) => {
               return self.get_value(r.clone(), inputs); 
            },
            Op::Vec(vec) => {
                let value_vector: Vec<Value<C>> = vec.iter().map(|op| self.handle_op(&op, Arc::clone(&inputs))).collect::<Vec<Value<C>>>();
                return  Value::value_vec(value_vector);
            },
            Op::Ram(box v, box index_val) => {
                let inputs_v_clone = Arc::clone(&inputs);
                let inputs_index_val_clone = Arc::clone(&inputs);
                let v_val: Value<C> = self.handle_op(v, inputs_v_clone);
                let index_val_value: Value<C> = self.handle_op(index_val, inputs_index_val_clone); 
                return v_val.ram(index_val_value);
            }
            Op::Check(box a) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(a, inputs_a_clone);

                return a_val;
            }
            Op::Bin(op, box a, box b, _typ) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let inputs_b_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(a, inputs_a_clone);
                let b_val: Value<C> = self.handle_op(b, inputs_b_clone);
                match op {
                    BinOp::Add => {
                        return a_val + b_val;
                    },
                    BinOp::Mul => {
                        return  a_val * b_val;
                    },
                    BinOp::Equ => {
                        return a_val.value_equ(&b_val);
                    }
                    BinOp::Sub => {
                        return a_val - b_val;
                    },
                    BinOp::Div => {
                        return a_val / b_val;
                    },
                    BinOp::Pow => {
                        return a_val ^ b_val;
                    },
                    BinOp::Dot => {
                        return a_val.dot(b_val);
                    },
                    BinOp::Concat => {
                        return a_val.value_concat(b_val);
                    },
                    BinOp::Rem => {
                        return a_val % b_val;
                    },
                    BinOp::And => {
                        return a_val & b_val;
                    }
               } 
            },
            Op::Random(typ, _) => {
                let mut rng = ThreadRng::default();
                return Value::random(&mut rng, typ);
 
            },
            Op::Challenge(typ, _) => {
                let mut rng = ThreadRng::default();
                //TODO: Implement challenge
                return Value::random(&mut rng, typ);
            },
            Op::Eval(box p, box x) => {
                let inputs_p_clone = Arc::clone(&inputs);
                let inputs_x_clone = Arc::clone(&inputs);
                let p_val: Value<C> = self.handle_op(p, inputs_p_clone);
                let x_val: Value<C> = self.handle_op(x, inputs_x_clone);
                return p_val.value_eval(x_val);
            }
            Op::Coef(box a) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(a, inputs_a_clone);
                return a_val.value_coef();
            }
            Op::Pair(box a, box b, _) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let inputs_b_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(a, inputs_a_clone);
                let b_val: Value<C> = self.handle_op(b, inputs_b_clone); 
                return a_val.pair(b_val);
            },
            Op::Poly(box a) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(a, inputs_a_clone);
                return a_val.value_poly();
            }
            Op::Ifft(box a) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(a, inputs_a_clone);
                return a_val.value_ifft();
            }
            Op::Fft(box a)  => {
                let inputs_a_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(a, inputs_a_clone);
                return a_val.value_fft();
            }
            Op::Mle(box a) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(a, inputs_a_clone);
                return a_val.value_mle();
            }
        }
    }

    pub fn handle_node(&self, node_curr: NodeIndex, inputs: Arc<Ctx<Vid, Value<C>>>) {

        let node = &self.mutex_graph[node_curr];
    
        match node {
            Node::Op(operation, annotation) => {
                let return_val = self.handle_op(operation, inputs);
                let mut return_value_lock = annotation.return_value.lock().unwrap();
                *return_value_lock = Some(return_val);  
            },
            Node::Transcr(operation, annotation)  => {
                let return_val = self.handle_op(operation, inputs);
                let mut return_value_lock = annotation.return_value.lock().unwrap();
                *return_value_lock = Some(return_val);  
            },
            Node:: Inp(_, _) => { 
            },
            Node::Rel(_, _) => {
            }
        }

    }

    pub fn run_graph<H: DuplexSpongeInterface>(g: Arc<MutexGraph<C>>, inputs: Arc<Ctx<Vid, Value<C>>>, prover_state: &mut ProverState<H>) -> Vec<Value<C>> {
        // add in context for the challenge

        let mut final_return: Vec<Value<C>> = Vec::new();
        let mut ready_nodes: Vec<NodeIndex> = Vec::new();
        let mut running_nodes: Vec<NodeIndex> = Vec::new();

        for node in g.mutex_graph.node_indices() {
            if g.mutex_graph.neighbors_directed(node, petgraph::Direction::Incoming).count() == 0 {
                ready_nodes.push(node);
            }
        }

        let max_threads: usize = num_cpus::get();
        let mut active_threads: usize = 1;

        while !ready_nodes.is_empty() || !running_nodes.is_empty() {
            let mut remove_from_ready: Vec<NodeIndex> = Vec::new();

            for i in 0..ready_nodes.len() {
                let node_index = ready_nodes[i];
                let thread_num_val;

                match &g.mutex_graph[node_index] {
                    Node::Op(_, annotation) | Node::Transcr(_, annotation) => {
                        thread_num_val = annotation.thread_num;
                    },
                    Node::Inp(_, _) | Node::Rel(_, _) => {
                        thread_num_val = 0;
                    }
                }

                if thread_num_val <= (max_threads - active_threads) {
                    let pool = rayon::ThreadPoolBuilder::new()
                        .num_threads(thread_num_val)
                        .build()
                        .unwrap();

                    // check if node is a challenge node
                    let mut challenge_node = false;
                    let mut input_node = false;
                    let node = &g.mutex_graph[node_index];
                    match node {
                        Node::Op(op, annotation) | Node::Transcr(op, annotation) => {
                            match op {
                                GOp::Challenge(_c_typ, _) => {
                                    let return_val = Value::<C>::challenge(prover_state);
                                    let mut return_value_lock = annotation.return_value.lock().unwrap();
                                    *return_value_lock = Some(return_val); 
                                    challenge_node = true;
                                }
                                _ => {}
                            }
                        },
                        Node::Inp(_c, prefs) => {
                            for pref in prefs.clone() {
                                if pref.qualifier.is_public() {
                                    prover_state.add_bytes(&value_to_bytes(inputs.get(&pref.var().unwrap()).unwrap()).unwrap()).unwrap();
                                }
                            }
                            input_node = true;
                        },
                        Node::Rel(_, _) => {}
                    } 

                    if !challenge_node && !input_node {

                        let graph = Arc::clone(&g);
                        let inputs_arc = Arc::clone(&inputs);
                        pool.spawn(move || {
                            graph.handle_node(node_index, inputs_arc);
                        });

                    }
                    running_nodes.push(node_index);
                    active_threads += thread_num_val;
                    remove_from_ready.push(node_index);
                }
            }

            let remove_set: HashSet<NodeIndex> = remove_from_ready.into_iter().collect();
            ready_nodes.retain(|x| !remove_set.contains(x));

            let mut remove_from_running: Vec<NodeIndex> = Vec::new();
            for i in 0..running_nodes.len() {
                let node_index = running_nodes[i];

                let finished: bool = match &g.mutex_graph[node_index] {
                    Node::Op(_, annotation) | Node::Transcr(_, annotation) => {
                        let return_val = annotation.return_value.lock().unwrap();
                        return_val.is_some()
                    },
                    Node::Inp(_, _) | Node::Rel(_, _) => true,
                };

                if finished {
                    remove_from_running.push(node_index);
                    match &g.mutex_graph[node_index] {
                        Node::Op(_, annotation) => {
                            active_threads -= annotation.thread_num;
                        },
                        Node::Transcr(_, annotation) => {
                            active_threads -= annotation.thread_num;
                            let serialized_return_val = value_to_bytes(&annotation.return_value.lock().unwrap().clone().unwrap()).unwrap();
                            prover_state.add_bytes(&serialized_return_val).unwrap();
                        },
                        Node::Inp(_, _) | Node::Rel(_, _) => {
                            
                        }
                    }

                    let mut fix_finished_requirements: Vec<NodeIndex> = Vec::new();
                    let dependents = g.mutex_graph.neighbors_directed(node_index, petgraph::Direction::Outgoing);
                    for dependent in dependents {
                        let incoming_nodes: Vec<_> = g.mutex_graph.neighbors_directed(dependent, petgraph::Direction::Incoming).collect();
                        let mut ready: bool = true;
                        for income_node in &incoming_nodes {
                            let finished_requirements_lock = match &g.mutex_graph[dependent] {
                                Node::Op(_, annotation) | Node::Transcr(_, annotation) => {
                                    annotation.finished_requirements.lock().unwrap()
                                },
                                Node::Inp(_, _) | Node::Rel(_, _) => panic!("Not possible"),
                            };
                            if !(*income_node == node_index || *income_node == dependent || finished_requirements_lock.contains(income_node)) {
                                ready = false;
                                break;
                            }
                        }

                        if ready {
                            if !ready_nodes.contains(&dependent) {
                                ready_nodes.push(dependent);
                            }
                        } else {
                            fix_finished_requirements.push(dependent);
                        }
                    }
                    for dependent in fix_finished_requirements {
                        let node = &g.mutex_graph[dependent];
                
                        match node {
                            Node::Op(_, annotation) | Node::Transcr(_, annotation)  => {
                                let mut finished_req = annotation.finished_requirements.lock().unwrap();
                                finished_req.push(node_index);
                            },
                            Node:: Inp(_, _) | Node::Rel(_, _) => {
                
                            }
                        } 
                    }
                }
            }
            if remove_from_running == running_nodes && ready_nodes.is_empty() {
                let node_index = remove_from_running.first().unwrap();
                let node = &g.mutex_graph[*node_index];
                match node {
                    Node::Op(_, annotation) => {
                        let return_val = annotation.return_value.lock().unwrap();
                        if return_val.is_some() {
                            final_return.push(return_val.clone().unwrap());
                        }
                    },
                    Node::Transcr(_, _) => {
                        let transcript_nodes = g.mutex_graph.transcript_nodes();


                        for node_transcript in transcript_nodes {
                            let transcript_node = &g.mutex_graph[node_transcript];
                            match transcript_node {
                                Node::Transcr(_, annotation) => {
                                    let return_val = annotation.return_value.lock().unwrap();
                                    if return_val.is_some() {
                                        final_return.push(return_val.clone().unwrap());
                                    }
                                }
                                _ => {
                                    panic!("Not possible");
                                }
                            }
                            
                        }
                    },
                    Node::Inp(_, _) | Node::Rel(_, _) => {
                    }
                }
            }
            let remove_finished_set: HashSet<NodeIndex> = remove_from_running.into_iter().collect();
            running_nodes.retain(|x| !remove_finished_set.contains(x));
        }
        final_return
    }
}