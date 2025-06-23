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
use graph::{WritePdf, Ref};
use ark_std::test_rng;
use rand::Rng;
use lang::typ::{Nothing, lub::Lub};
use ark_std::UniformRand;
use graph::scheduler::{Scheduler, AsymptoticCost};
use graph::scheduler::ilp::GurobiScheduler;
use ark_std::time::Instant;
use runtime::*;

macro_rules! start_timer {
    ($msg:expr) => {{
        println!("{}", $msg);
        Instant::now()
    }};
}

fn run_poly_test() {
    let size = 16;
    let ex = r#"
        proto poly_mul<F: Field, N: 16>(public a: Uni<F, N>, public b: Uni<F, N>) where a == a {
        let r = random<F*>;
        let p = a * b;
        verify(p(r) == (a(r) * b(r)));
    }"#;

   let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    gs.write_pdf("graph_foo").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });

    let cost_model = AsymptoticCost::new();
    let scheduler = GurobiScheduler::new_with_system(&gs[0], &cost_model, .5);
    let tdag = scheduler.schedule(gs[0].clone());
    let mut mutex_graph_example = MutexGraph::new(tdag);
    let mut arc_graph = Arc::new(mutex_graph_example);

    let mut inputs: HashMap<Vid, Value<ArkBls12_381>> = HashMap::new();
    let mut rng = test_rng();
    
    let a_coeffs = (0..size)
        .map(|_| <<ArkBls12_381 as ArkConfig>::F as UniformRand>::rand(&mut rng))
        .collect::<Vec<_>>();
    let a = Value::VecScalar(a_coeffs);

    let b_coeffs = (0..size)
        .map(|_| <<ArkBls12_381 as ArkConfig>::F as UniformRand>::rand(&mut rng))
        .collect::<Vec<_>>();
    let b = Value::VecScalar(b_coeffs);

    inputs.insert(Vid("a".to_string()), a);
    inputs.insert(Vid("b".to_string()), b);
    
    let start = start_timer!("Running the graph");
    let result = MutexGraph::run_graph(arc_graph, Arc::new(inputs));
    println!("Result: {:?}", result);
    let duration = start.elapsed();
    println!("Time taken: {:?} for size {}", duration, size); 
}

fn run_foo_test() {
    let ex = r#"
        proto foo<F: Field>(private s: F, public v: [F; 10]) where s == s {
            let r = random<F>;
            c <- challenge<F>;
            a <- r * c;
            b <- r + c + s;
            x <- v[1..5];
            verify(a * s == b * x[3]);
        }"#;

    let m = UModule::from_str(ex).unwrap().concretize().unwrap();
    let gs = unwrap!(UDags::<ArkBls12_381>::from_module(m));

    gs.write_pdf("graph_foo").unwrap_or_else(|e| {
        println!("Error writing to PDF, maybe [dot] is not installed? \n\n {}", e);
    });

    let cost_model = AsymptoticCost::new();
    let scheduler = GurobiScheduler::new_with_system(&gs[0], &cost_model);
    let tdag = scheduler.schedule(gs[0].clone(), 0.50);
    let mut mutex_graph_example = MutexGraph::new(tdag);
    let mut arc_graph = Arc::new(mutex_graph_example);

    let mut inputs: HashMap<Vid, Value<ArkBls12_381>> = HashMap::new();
    let mut rng = test_rng();

    let a = Value::<ArkBls12_381>::random(&mut rng, &ATyp::scalar());
    inputs.insert(Vid("s".to_string()), a.clone());
    let v_val: Value<ArkBls12_381> = Value::<ArkBls12_381>::random(&mut rng, &ATyp::vec_scalar(10));
    inputs.insert(Vid("v".to_string()), v_val);

    let start = start_timer!("Running the graph");
    let result = MutexGraph::run_graph(arc_graph, Arc::new(inputs));
    println!("Result: {:?}", result);
    let duration = start.elapsed();
    println!("Time taken: {:?}", duration);
}

fn main() {
    use analyses::TransClos;
    // run_poly_test();
    run_foo_test();
}
