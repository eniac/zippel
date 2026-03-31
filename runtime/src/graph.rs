use log::debug;
use petgraph::graph::NodeIndex;
use spongefish::{ProverState, DuplexSpongeInterface};
use std::sync::{Arc, Mutex};
use backend::{ArkConfig, Value, value_to_bytes, ArkScalarOps};
use backend::values::marginalize as backend_marginalize;
use backend::values::round_univariate_from_marginalize_evals as backend_round_univariate_from_marginalize_evals;
use graph::{Dag, Node, Op, GOp};
use graph::scheduler::{ThreadAlloc, TDag};
use rand::rngs::ThreadRng;
use lang::ast::BinOp;
use std::collections::HashSet;
use lang::id::Vid;
use share::Ctx;

pub struct RuntimeInformation<C: ArkConfig> {
    thread_num: usize,
    return_value: Mutex<Option<Value<C>>>,
    finished_requirements: Mutex<Vec<NodeIndex>>,
    is_challenge: Mutex<bool>,
}

impl<C: ArkConfig> RuntimeInformation<C> {
    pub fn new(thread_num: usize) -> Self {
        RuntimeInformation {
            thread_num, return_value: Mutex::new(None), finished_requirements: Mutex::new(Vec::new()), is_challenge: Mutex::new(false)
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
                debug!("Edge from {:?} to {:?}", node, neighbor);
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

    pub fn handle_op(&self, operation: &GOp<C>, inputs: Arc<Ctx<Vid, Value<C>>>) -> Value<C>{
        match operation {
            Op::Value(val) => {
                return val.clone();
            },
            Op::Ref(r, _atyp) => {
               return self.get_value(r.clone(), inputs);
            },
            Op::Vec(vec) => {
                let value_vector: Vec<Value<C>> = vec.iter().map(|op| self.handle_op(&*op, Arc::clone(&inputs))).collect::<Vec<Value<C>>>();
                return  Value::value_vec(value_vector);
            },
            Op::Record(fields) => {
                let mut record_values = share::Ctx::new();
                for (name, op) in fields.iter() {
                    let field_value = self.handle_op(&*op, Arc::clone(&inputs));
                    record_values.insert(name, &field_value);
                }
                return Value::Record(record_values);
            },
            Op::Ram(v, index_val) => {
                let inputs_v_clone = Arc::clone(&inputs);
                let inputs_index_val_clone = Arc::clone(&inputs);
                let v_val: Value<C> = self.handle_op(&*v, inputs_v_clone);
                let index_val_value: Value<C> = self.handle_op(&*index_val, inputs_index_val_clone);
                return v_val.ram(index_val_value);
            }
            Op::Check(a) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(&*a, inputs_a_clone);

                return a_val;
            }
            Op::Bin(op, a, b, _typ) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let inputs_b_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(&*a, inputs_a_clone);
                let b_val: Value<C> = self.handle_op(&*b, inputs_b_clone);
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
            Op::Eval(p, x) => {
                let inputs_p_clone = Arc::clone(&inputs);
                let inputs_x_clone = Arc::clone(&inputs);
                let p_val: Value<C> = self.handle_op(&*p, inputs_p_clone);
                let x_val: Value<C> = self.handle_op(&*x, inputs_x_clone);
                return p_val.value_eval(x_val);
            }
            Op::Coef(a) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(&*a, inputs_a_clone);
                return a_val.value_coef();
            }
            Op::Pair(a, b, _) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let inputs_b_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(&*a, inputs_a_clone);
                let b_val: Value<C> = self.handle_op(&*b, inputs_b_clone);
                return a_val.pair(b_val);
            },
            Op::Poly(a) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(&*a, inputs_a_clone);
                return a_val.value_poly();
            }
            Op::Ifft(a) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(&*a, inputs_a_clone);
                return a_val.value_ifft();
            }
            Op::Fft(a)  => {
                let inputs_a_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(&*a, inputs_a_clone);
                return a_val.value_fft();
            }
            Op::Mle(a) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let a_val: Value<C> = self.handle_op(&*a, inputs_a_clone);
                return a_val.value_mle();
            }
            Op::Reduce(op, v) => {
                let inputs_v_clone = Arc::clone(&inputs);
                let v_val: Value<C> = self.handle_op(&*v, inputs_v_clone);
                return v_val.value_reduce(*op);
            }
            Op::Marginalize(box a) => {
                let inputs_a_clone = Arc::clone(&inputs);
                let cfg_val: Value<C> = self.handle_op(a, inputs_a_clone);

                let record = match cfg_val {
                    Value::Record(r) => r,
                    _ => panic!("marginalize expects a record argument"),
                };

                let poly_val = record.get(&"poly".to_string()).expect("marginalize: missing field 'poly'");
                let num_vars_val = record.get(&"num_variables".to_string()).expect("marginalize: missing field 'num_variables'");
                let max_deg_val = record.get(&"max_degree".to_string()).expect("marginalize: missing field 'max_degree'");
                let challenge_val = record.get(&"challenge".to_string()).expect("marginalize: missing field 'challenge'");

                let poly = match poly_val {
                    Value::Poly(p) => p.clone(),
                    _ => panic!("marginalize: 'poly' must be a polynomial"),
                };

                let num_variables = match num_vars_val {
                    Value::Index(i) => *i,
                    _ => panic!("marginalize: 'num_variables' must be an index"),
                };

                let max_degree = match max_deg_val {
                    Value::Index(i) => *i,
                    _ => panic!("marginalize: 'max_degree' must be an index"),
                };

                let challenge = match challenge_val {
                    Value::Scalar(f) => Some(*f),
                    _ => panic!("marginalize: 'challenge' must be a scalar"),
                };

                let round = record
                    .get(&"round".to_string())
                    .map(|v| match v {
                        Value::Index(i) => *i,
                        _ => panic!("marginalize: 'round' must be an index"),
                    })
                    .unwrap_or(0usize);
                let (evals, next_poly) =
                    backend_marginalize::<C>(&poly, num_variables, max_degree, round, challenge);

                let mut out_fields = Ctx::new();
                out_fields.insert(&"evaluations".to_string(), &Value::VecScalar(evals));
                out_fields.insert(&"next_poly".to_string(), &Value::Poly(next_poly));

                return Value::Record(out_fields);
            }

            Op::Interpolate0dEval(box evals) => {
                let inputs_evals_clone = Arc::clone(&inputs);
                let evals_val: Value<C> = self.handle_op(evals, inputs_evals_clone);

                let evals: Vec<C::F> = match evals_val {
                    Value::VecScalar(v) => v,
                    Value::VecIndex(v) => v
                        .iter()
                        .map(|i| C::FOps::from_usize(*i))
                        .collect(),
                    _ => panic!("interpolate0d expects a vector of field evaluations"),
                };

                let poly = backend_round_univariate_from_marginalize_evals::<C::F>(&evals);
                return Value::Poly(poly);
            }
            Op::Proj(box record_op, field_name, _) => {
                let inputs_rec = Arc::clone(&inputs);
                let rec_val: Value<C> = self.handle_op(record_op, inputs_rec);
                match rec_val {
                    Value::Record(r) => r.get(&field_name).cloned().expect("Proj: missing field"),
                    _ => panic!("Proj expects a record value"),
                }
            }
        }
    }

    pub fn handle_node(&self, node_curr: NodeIndex, inputs: Arc<Ctx<Vid, Value<C>>>) {

        let node = &self.mutex_graph[node_curr];

        match node {
            Node::Op(operation, annotation) => {
                let return_val = self.handle_op(&**operation, inputs);
                let mut return_value_lock = annotation.return_value.lock().unwrap();
                *return_value_lock = Some(return_val);
            },
            Node::Transcr(operation, annotation)  => {
                let return_val = self.handle_op(&**operation, inputs);
                let mut return_value_lock = annotation.return_value.lock().unwrap();
                *return_value_lock = Some(return_val);
            },
            Node:: Inp(_, _) => {
            },
            Node::Rel(_, _) => {
            }
        }

    }

    pub fn run_graph<H: DuplexSpongeInterface<U = u8>>(g: Arc<MutexGraph<C>>, inputs: Arc<Ctx<Vid, Value<C>>>, prover_state: &mut ProverState<H>) -> Vec<Value<C>> {
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
                            if matches!(&**op, Op::Challenge(_, _)) {
                                    let return_val = Value::<C>::challenge(prover_state);
                                    let mut return_value_lock = annotation.return_value.lock().unwrap();
                                    *return_value_lock = Some(return_val);
                                    challenge_node = true;
                                    let mut is_challenge_lock = annotation.is_challenge.lock().unwrap();
                                    *is_challenge_lock = true;
                            }
                        },
                        Node::Inp(_c, prefs) => {
                            for pref in prefs.clone() {
                                if pref.qualifier.is_public() && !pref.from_transcript {
                                    prover_state.public_message(value_to_bytes(inputs.get(&pref.var().unwrap()).unwrap()).unwrap().as_slice());
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
                    if let Node::Op(op, annotation) = &g.mutex_graph[node_index] {
                        if matches!(op, GOp::Check(_)) {
                            let return_val_guard = annotation.return_value.lock().unwrap();
                            if let Some(return_val) = return_val_guard.as_ref() {
                                if matches!(return_val, Value::Bool(_)) {
                                    final_return.push(return_val.clone());
                                }
                            }
                        }
                    }
                    match &g.mutex_graph[node_index] {
                        Node::Op(_, annotation) => {
                            active_threads -= annotation.thread_num;
                        },
                        Node::Transcr(_, annotation) => {
                            active_threads -= annotation.thread_num;
                            let serialized_return_val = value_to_bytes(&annotation.return_value.lock().unwrap().clone().unwrap()).unwrap();
                            prover_state.public_message(serialized_return_val.as_slice());
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
                                    if return_val.is_some() && !*annotation.is_challenge.lock().unwrap() {
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
