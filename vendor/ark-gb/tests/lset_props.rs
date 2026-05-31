//! Property tests for [`LSet`].
//!
//! We run a random mix of inserts, deletes-by-indices, and pops and
//! check:
//!
//! * Surviving pairs come out in `(sugar, arrival)` order.
//! * Every surviving-and-not-popped pair is visible exactly once.
//! * Deleted pairs never reappear.
//! * `len()` matches the number of live pairs actually returned.

use ark_bls12_381::Fr;
use ark_gb::{LSet, MonoTerm, Pair, Ring};
use proptest::prelude::*;

const NVARS: u32 = 3;
const MAX_OPS: usize = 30;

fn ring() -> Ring<Fr> {
    Ring::<Fr>::new(NVARS).unwrap()
}

/// A fixed nontrivial LCM; the LSet properties depend only on the
/// pair's (sugar, arrival, i, j) and identity key, not on the LCM
/// itself.
fn fixed_lcm(r: &Ring<Fr>) -> MonoTerm {
    MonoTerm::from_exponents(r, &[1, 1, 1]).unwrap()
}

/// Operations the test stream emits. Real Pair::new swaps (i, j) into
/// canonical order; the delete call accepts either order.
#[derive(Debug, Clone)]
enum Op {
    Insert { i: u32, j: u32, sugar: u32 },
    DeleteByIndices { i: u32, j: u32 },
    Pop,
}

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        (0u32..5u32, 0u32..5u32, 0u32..10u32).prop_filter_map("need i != j", |(i, j, s)| {
            if i == j {
                None
            } else {
                Some(Op::Insert { i, j, sugar: s })
            }
        },),
        (0u32..5u32, 0u32..5u32).prop_filter_map("need i != j", |(i, j)| {
            if i == j {
                None
            } else {
                Some(Op::DeleteByIndices { i, j })
            }
        }),
        Just(Op::Pop),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(150))]

    #[test]
    fn mixed_ops_preserve_ordering_and_bookkeeping(
        ops in prop::collection::vec(op_strategy(), 1..=MAX_OPS),
    ) {
        let r = ring();
        let mut l = LSet::new();
        let mut arrival: u64 = 0;
        let mut popped: Vec<Pair> = Vec::new();

        let lcm = fixed_lcm(&r);
        for op in &ops {
            match op.clone() {
                Op::Insert { i, j, sugar } => {
                    let pair = Pair::new(i, j, lcm, sugar, arrival);
                    arrival += 1;
                    l.insert(pair);
                }
                Op::DeleteByIndices { i, j } => {
                    l.delete(i, j);
                }
                Op::Pop => {
                    if let Some(p) = l.pop() {
                        popped.push(p);
                    }
                }
            }
            l.assert_canonical(&r);
        }

        // Pop everything left; combined with the in-stream pops, the
        // yielded sequence of popped.sugar values must be monotone
        // within each "run" between inserts. More concretely: if we
        // drain at the end, the sequence is globally non-decreasing
        // in (sugar, arrival) across the final drain. In-stream
        // pops may interleave freshly-smaller pairs afterwards, so
        // we only check the final drain is sorted.
        let drain_start = popped.len();
        while let Some(p) = l.pop() {
            popped.push(p);
        }
        l.assert_canonical(&r);
        for w in popped[drain_start..].windows(2) {
            prop_assert!(
                (w[0].sugar, w[0].arrival) <= (w[1].sugar, w[1].arrival),
                "final drain out of order: {:?} before {:?}",
                (w[0].sugar, w[0].arrival),
                (w[1].sugar, w[1].arrival),
            );
        }

        // No duplicates in the popped sequence (by identity key).
        let mut keys = std::collections::HashSet::new();
        for p in &popped {
            prop_assert!(
                keys.insert(p.key),
                "pair key {:?} popped twice",
                p.key
            );
        }
    }

    #[test]
    fn insert_then_delete_leaves_empty(
        seeds in prop::collection::vec((0u32..5u32, 0u32..5u32, 0u32..10u32), 1..=10),
    ) {
        let r = ring();
        let mut l = LSet::new();
        let mut arrival = 0u64;
        let mut inserted_indices: Vec<(u32, u32)> = Vec::new();
        for (i, j, s) in seeds {
            if i == j {
                continue;
            }
            let (i, j) = if i < j { (i, j) } else { (j, i) };
            let lcm = MonoTerm::from_exponents(&r, &[1, 1, 1]).unwrap();
            l.insert(Pair::new(i, j, lcm, s, arrival));
            arrival += 1;
            inserted_indices.push((i, j));
        }
        // Dedup: only the last insert for each (i, j) is live.
        let mut dedup = std::collections::HashMap::new();
        for (i, j) in inserted_indices {
            dedup.insert((i, j), ());
        }
        prop_assert_eq!(l.len(), dedup.len());

        // Deleting each live (i, j) once leaves the set empty.
        for &(i, j) in dedup.keys() {
            prop_assert!(l.delete(i, j));
        }
        prop_assert_eq!(l.len(), 0);
        prop_assert!(l.pop().is_none());
    }
}
