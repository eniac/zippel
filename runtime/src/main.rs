#![feature(box_patterns)]
use std::thread;
use lang::id::Vid;
use petgraph::graph::{self as petgraph_graph, EdgeIndex, NodeIndex};
use petgraph::graph::Graph;
use rand::rngs::ThreadRng;
use std::time::{Duration, SystemTime};
use std::sync::{Arc, Mutex};
use rayon::{string, ThreadPoolBuilder};
use graph::{UDags, Dag, Node, Op, analyses};
use backend::{ArkConfig, ATyp, Value, ABase};
use std::collections::{HashMap, HashSet};
use share::unwrap;
use lang::ast::{BinOp, UModule};
use backend::ArkBls12_381;
use graph::Ref;
use ark_std::test_rng;
use rand::Rng;
use lang::typ::{Nothing, lub::Lub};
use ark_std::UniformRand;

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


pub struct MutexGraph<C: ArkConfig>(pub Dag<C, Arc<RuntimeInformation<C>>>);

pub type TDag<C: ArkConfig> = Dag<C, usize>;



impl<C: ArkConfig> MutexGraph<C> {
    pub fn new(tdag: TDag<C>) -> Self {
        MutexGraph(
            tdag.map_annotations(|_, nthreads| Arc::new(RuntimeInformation::<C>::new(*nthreads)))
        )
    }

    pub fn get_value(&self, reference: graph::Ref, inputs: Arc<HashMap<Vid, Value<C>>>) -> Value<C> {
        let val: Value<C> = match reference {
            Ref::Node(node_index) => {
                let node = &self.0[node_index];
                match node {
                    Node::Op(_, annotation) | Node::Transcr(_, annotation) => {
                        let return_val = annotation.return_value.lock().unwrap();
                        match &*return_val {
                            Some(val) => val.clone(),
                            None => panic!("Value should exist")
                        }
                    },
                    _ => {
                        panic!("No value");
                    }
                }
            },
            Ref::Var(vid, node_index) => {
                println!("{:?}", vid);
                println!("getting value");
                let input_val = inputs.contains_key(&vid);
                if input_val {
                    inputs[&vid].clone()
                }
                else {
                    let node = &self.0[node_index];
                    match node {
                        Node::Op(_, annotation) | Node::Transcr(_, annotation) => {
                            let return_val = annotation.return_value.lock().unwrap();
                            match &*return_val {
                                Some(val) => val.clone(),
                                None => panic!("Value should exist")
                            }
                        },
                        _ => {
                            panic!("No value");
                        }
                    } 
                }
            }
        };
        return val;
    }

    pub fn handle_op(&self, operation: &Op<C, Ref>, inputs: Arc<HashMap<Vid, Value<C>>>) -> Value<C>{
        match operation {
            Op::Value(val) => {
                return val.clone();
            },
            Op::Ref(r, ATyp) => {
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
                println!("running ram");
                return v_val.ram(index_val_value);
            }
            Op::Check(box a) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(a, inputs_a_clone);

                println!("{}", a_val);
                if Value::Bool(true) == a_val {
                    println!("Program Succeeded")
                }

                return a_val;
            }
            Op::Bin(BinOperation, box a, box b, ATyp) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let inputs_b_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(a, inputs_a_clone);
                let b_val: Value<C> = self.handle_op(b, inputs_b_clone);
                match BinOperation {
                    BinOp::Add => {
                        println!("running add");
                        return a_val + b_val;
                    },
                    BinOp::Mul => {
                        println!("running mul");
                        return  a_val * b_val;
                    },
                    BinOp::Equ => {
                        println!("running equ");
                        println!("{}", a_val);
                        println!("{}", b_val);
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
            Op::Random(ATyp, _) => {
                let mut rng = ThreadRng::default();
                println!("running random");
                return Value::random(&mut rng, ATyp);
 
            },
            Op::Challenge(ATyp, _) => {
                let mut rng = ThreadRng::default();
                println!("running challenge");
                return Value::random(&mut rng, ATyp);
            },
            Op::Pair(box a, box b, ATyp) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let inputs_b_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(a, inputs_a_clone);
                let b_val: Value<C> = self.handle_op(b, inputs_b_clone); 
                return a_val.pair(b_val);
            },
            Op::Coef(box a) => {
                println!("running coef");
                let inputs_a_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(a, inputs_a_clone);
                return a_val.value_ifft();
            }
            Op::Eval(box a)  => {
                println!("running eval");
                let inputs_a_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(a, inputs_a_clone);
                return a_val.value_fft();
            }
        }
    }
    pub fn handle_node(&self, node_curr: NodeIndex, inputs: Arc<HashMap<Vid, Value<C>>>) {
        // println!("running Node Index: {:?}", node_curr);

        let node = &self.0[node_curr];
        

        match node {
            Node::Op(operation, annotation) | Node::Transcr(operation, annotation)  => {
                let return_val = self.handle_op(operation, inputs);
                println!("Done for {:?} with output {}", node_curr, return_val.clone()); 
                let mut return_value_lock = annotation.return_value.lock().unwrap();
                *return_value_lock = Some(return_val);  
            },
            Node:: Inp(_, _) | Node::Rel(_, _) => {
                println!("Not Processing");
                // println!("Done for {:?}", node_curr);
            }
        }

    }

    pub fn run_graph(g: Arc<MutexGraph<C>>, inputs: Arc<HashMap<Vid, Value<C>>>) {
        let mut ready_nodes: Vec<NodeIndex> = Vec::new();
        let mut running_nodes: Vec<NodeIndex> = Vec::new();

        for node in g.0.node_indices() {
            if g.0.neighbors_directed(node, petgraph::Direction::Incoming).count() == 0 {
                ready_nodes.push(node);
            }
        }

        let max_threads: usize = num_cpus::get();
        println!("max threads - {}", max_threads);
        let mut active_threads: usize = 1;

        let mut final_return: Value<C>;

        while !ready_nodes.is_empty() || !running_nodes.is_empty() {
            let mut remove_from_ready: Vec<NodeIndex> = Vec::new();

            for i in 0..ready_nodes.len() {
                let node_index = ready_nodes[i];
                let mut thread_num_val: usize = 0;

                match &g.0[node_index] {
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

                    // let dependencies: Vec<NodeIndex> = g.0
                    //     .neighbors_directed(node_index, petgraph::Direction::Incoming)
                    //     .collect();

                    let graph = Arc::clone(&g);
                    let inputs_arc = Arc::clone(&inputs);
                    pool.spawn(move || {
                        println!("{:?}", node_index);
                        graph.handle_node(node_index, inputs_arc);
                    });

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

                let finished: bool = match &g.0[node_index] {
                    Node::Op(_, annotation) | Node::Transcr(_, annotation) => {
                        let return_val = annotation.return_value.lock().unwrap();
                        return_val.is_some()
                    },
                    Node::Inp(_, _) | Node::Rel(_, _) => true,
                };

                if finished {
                    remove_from_running.push(node_index);
                    match &g.0[node_index] {
                        Node::Op(_, annotation) | Node::Transcr(_, annotation) => {
                            active_threads -= annotation.thread_num;
                        },
                        Node::Inp(_, _) | Node::Rel(_, _) => {
                            
                        }
                    }

                    let mut fix_finished_requirements: Vec<NodeIndex> = Vec::new();
                    let dependents = g.0.neighbors_directed(node_index, petgraph::Direction::Outgoing);
                    for dependent in dependents {
                        let incoming_nodes: Vec<_> = g.0.neighbors_directed(dependent, petgraph::Direction::Incoming).collect();
                        let mut ready: bool = true;
                        for income_node in &incoming_nodes {
                            let mut finished_requirements_lock = match &g.0[dependent] {
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
                        let node = &g.0[dependent];
                
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
            // if (remove_from_running == running_nodes) {
            //     let node_index = remove_from_running.first().unwrap();
            //     let node = &g.0[*node_index];
            //     match node {
            //         Node::Op(_, annotation) | Node::Transcr(_, annotation) => {
            //             let return_val = annotation.return_value.lock().unwrap();
            //             if return_val.is_some() {
            //                 final_return = return_val.unwrap();
            //             }
            //         },
            //         Node::Inp(_, _) | Node::Rel(_, _) => {
            //             panic!("Not possible");
            //         }
            //     }
            // }
            let remove_finished_set: HashSet<NodeIndex> = remove_from_running.into_iter().collect();
            running_nodes.retain(|x| !remove_finished_set.contains(x));
        }
    }
}


fn main() {
    // coef - ifft
    // eval - fft
    use analyses::TransClos;
    // let ex = r#"
    //     proto foo<F: Field>(private s: F, public v: [F; 10]) where s == s {
    //         let r = random<F>;
    //         c <- challenge<F>;
    //         a <- r * c;
    //         b <- r + c + s;
    //         x <- v[1..5];
    //         verify(a * s == b * x[3]);
    //     }"#;
    // let ex = r#"
    //     proto foo<F: Field>(private s: F, public a: F) where s == s {
    //         let r = random<F>;
    //         d <- r * s;
    //         b <- r * a;
    //         verify(d == b);
    //     }"#;
    let ex = r#"
        proto poly_mul<F: Field>(public a: Uni<F, 4>, public b: Uni<F, 4>) where a == a {
        let r = random<F*>;
        let p = a * b;
        verify(p(r) == (a(r) * b(r)));
    }"#;
    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    println!("{}", m);
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    gs.write_pdf("graph_foo").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });

    let mut tdag_example: TDag<ArkBls12_381> = gs[0].map_annotations(|_, _| 4);   
    let mut mutex_graph_example = MutexGraph::new(tdag_example);
    // mutex_graph_example.print(); 
    let mut arc_graph = Arc::new(mutex_graph_example);
    let mut inputs: HashMap<Vid, Value<ArkBls12_381>> = HashMap::new();
    let mut rng = test_rng();
    
    let a_coeffs = (0..4)
        .map(|_| <<ArkBls12_381 as ArkConfig>::F as UniformRand>::rand(&mut rng))
        .collect::<Vec<_>>();
    let a = Value::VecScalar(a_coeffs);

    let b_coeffs = (0..4)
        .map(|_| <<ArkBls12_381 as ArkConfig>::F as UniformRand>::rand(&mut rng))
        .collect::<Vec<_>>();
    let b = Value::VecScalar(b_coeffs);
    
    // let scalar_vec = Value::VecScalar((1..=10).map(|i| <ArkBls12_381 as ArkConfig>::F::from(i as u64)).collect::<Vec<_>>());
    
    // let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    // inputs.insert(Vid("s".to_string()), a.clone());
    // let v_val: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(10));
    // inputs.insert(Vid("v".to_string()), v_val);
    // let a_val: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(10));
    inputs.insert(Vid("a".to_string()), a);
    inputs.insert(Vid("b".to_string()), b);
    let result = MutexGraph::run_graph(arc_graph, Arc::new(inputs));
    // println!("Result: {}", result);
}
