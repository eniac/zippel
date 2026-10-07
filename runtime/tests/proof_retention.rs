//! A proof must not keep the prover's intermediate vectors alive.
//!
//! A slice is a view of its vector's buffer, and a view keeps the whole
//! buffer alive. A prover message that is a small slice of a large
//! intermediate vector would therefore hold that vector for as long as the
//! caller keeps the proof, unless the runtime copies views out of their
//! buffers as it collects the proof (`Value::compact`).
//!
//! This is its own test binary because it counts live heap bytes with a
//! global allocator.

use backend::config::ArkBls12_381;
use backend::{ArkConfig, Value};
use graph::UDags;
use lang::ast::UModule;
use lang::id::Tid;
use runtime::graph::ResultKind;
use runtime::{Inputs, MutexGraph, RunResult};
use share::Ctx;
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

/// The system allocator, counting the bytes currently allocated.
struct Counting;

static LIVE: AtomicUsize = AtomicUsize::new(0);

// SAFETY: every call is forwarded unchanged to `System`.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        LIVE.fetch_add(layout.size(), Ordering::Relaxed);
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        LIVE.fetch_sub(layout.size(), Ordering::Relaxed);
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static ALLOCATOR: Counting = Counting;

type C = ArkBls12_381;
type F = <C as ArkConfig>::F;

#[test]
fn a_one_element_message_does_not_retain_its_vector() {
    // `v` is an intermediate of N scalars; the only message is one of them.
    let src = r#"
        proto p<F: Field, N: Size>(instance a: [F; N]) where 1 == 1 {
            let v = [a[i] * a[i] for i in 0..N];
            s <- v[0..1];
            verify(s[0] == s[0])
        }
    "#;
    let n = 1usize << 18;
    let vector_bytes = n * size_of::<F>();

    let mut sizes: Ctx<Tid, usize> = Ctx::new();
    sizes.insert(&Tid::from("N"), &n);
    let (module, _diagnostics) = UModule::parse(src);
    let module = module.unwrap().concretize(&sizes).unwrap();
    let dags = UDags::<C>::from_module(module).unwrap();
    let dag = dags.protocols()[0].clone();
    let (prover, _) = dag.get_prover();
    let separator = graph::domain_seperator::ZippelDomainSeparator::new_zippel_domain_seperator(
        "proof_retention",
        &dag.clone().erase_ann(),
    );

    let before = LIVE.load(Ordering::Relaxed);
    // The graph, the inputs and the sponge are dropped with this block: only
    // the proof outlives the run.
    let proof = {
        let mut inputs = Inputs::<C>::new();
        inputs.insert("a", Value::vec_scalar(vec![F::from(3u64); n]));
        let mut prover_state = separator.std_prover();
        let graph = Arc::new(MutexGraph::new(prover));
        match MutexGraph::run_graph(graph, &inputs, &mut prover_state, ResultKind::Prover).unwrap()
        {
            RunResult::Prover(proof) => proof,
            RunResult::Verifier { .. } => unreachable!(),
        }
    };
    let held = LIVE.load(Ordering::Relaxed).saturating_sub(before);

    assert_eq!(proof, [Value::vec_scalar(vec![F::from(9u64)])]);
    assert!(
        held < vector_bytes / 8,
        "a one-element proof holds {held} bytes; the vector it was sliced from is {vector_bytes}"
    );
}
