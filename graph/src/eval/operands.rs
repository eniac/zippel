//! The operand values one evaluation reads.

use crate::{GOp, Op, Ref};
use arc_swap::ArcSwapOption;
use backend::{ArkConfig, Value};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

/// The values of the `Op::Ref` leaves of an operation, as `eval_op` reads
/// them.
///
/// Built with [`Operands::owned`], each operand is handed over (moved, not
/// cloned) at its last use, so an operation that holds the only reference to
/// a value can reuse its buffer instead of copying it. Uses inside a `Map` or
/// `ReduceMap` are evaluated once per element, so those operands are always
/// cloned. Built with [`Operands::borrowed`], every use clones.
pub struct Operands<C: ArkConfig> {
    slots: HashMap<Ref, Slot<C>>,
}

struct Slot<C: ArkConfig> {
    value: ArcSwapOption<Value<C>>,
    /// Uses not yet made, or [`PINNED`] for an operand that is never moved.
    uses: AtomicUsize,
}

/// The use count of an operand that is always cloned.
const PINNED: usize = usize::MAX;

impl<C: ArkConfig> Operands<C> {
    /// Operands for evaluating `op` once, each moved out at its last use.
    #[must_use]
    pub fn owned(op: &GOp<C>, values: HashMap<Ref, Arc<Value<C>>>) -> Self {
        let mut uses = HashMap::new();
        let mut pinned = HashSet::new();
        count_uses(op, false, &mut uses, &mut pinned);
        Self::with_uses(values, |r| {
            if pinned.contains(r) {
                PINNED
            } else {
                uses.get(r).copied().unwrap_or(0)
            }
        })
    }

    /// Operands that are only ever cloned, for a caller that keeps `values`.
    #[must_use]
    pub fn borrowed(values: &HashMap<Ref, Arc<Value<C>>>) -> Self {
        Self::with_uses(values.clone(), |_| PINNED)
    }

    fn with_uses(values: HashMap<Ref, Arc<Value<C>>>, uses: impl Fn(&Ref) -> usize) -> Self {
        let slots = values
            .into_iter()
            .map(|(r, v)| {
                let slot = Slot {
                    value: ArcSwapOption::new(Some(v)),
                    uses: AtomicUsize::new(uses(&r)),
                };
                (r, slot)
            })
            .collect();
        Operands { slots }
    }

    /// The value of `r` for one use: moved out at its last use, cloned before.
    /// `None` if `r` has no value.
    ///
    /// # Panics
    /// Panics if `r` is used more often than `op` contains it, which would
    /// mean the evaluator evaluated a subtree twice outside a loop.
    pub fn get(&self, r: Ref) -> Option<Arc<Value<C>>> {
        let slot = self.slots.get(&r)?;
        if slot.uses.load(Ordering::SeqCst) == PINNED {
            return slot.value.load_full();
        }
        let before = slot.uses.fetch_sub(1, Ordering::SeqCst);
        assert!(before > 0, "operand {r:?} used after its last counted use");
        if before == 1 {
            slot.value.swap(None)
        } else {
            slot.value.load_full()
        }
    }
}

/// Counts each `Op::Ref` of `op` outside loops into `uses`, and collects the
/// ones inside a `Map`/`ReduceMap` (evaluated per element) into `pinned`.
/// Visits the same leaves as `collect_refs`.
fn count_uses<C: ArkConfig>(
    op: &GOp<C>,
    in_loop: bool,
    uses: &mut HashMap<Ref, usize>,
    pinned: &mut HashSet<Ref>,
) {
    let mut walk = |child: &GOp<C>, in_loop: bool| count_uses(child, in_loop, uses, pinned);
    match op {
        Op::Value(_) | Op::Random(_, _) | Op::Challenge(_, _) | Op::LoopParam(_, _) => {}
        Op::Ref(r, _) if in_loop => {
            pinned.insert(*r);
        }
        Op::Ref(r, _) => *uses.entry(*r).or_insert(0) += 1,
        Op::Bin(_, a, b, _) | Op::Pair(a, b, _) | Op::Ram(a, b) | Op::Interpolate(a, b) => {
            walk(a, in_loop);
            walk(b, in_loop);
        }
        Op::Evaluate(a, _, maybe_b) => {
            walk(a, in_loop);
            if let Some(b) = maybe_b {
                walk(b, in_loop);
            }
        }
        Op::Vec(children) => {
            for child in children {
                walk(child, in_loop);
            }
        }
        Op::Record(fields) => {
            for (_, child) in fields.iter() {
                walk(child, in_loop);
            }
        }
        Op::Assert(a)
        | Op::Verify(a)
        | Op::Coef(a)
        | Op::ToScalar(a)
        | Op::Poly(a)
        | Op::Ifft(a)
        | Op::Fft(a)
        | Op::Mle(a)
        | Op::Proj(a, _, _)
        | Op::Reduce(_, a) => walk(a, in_loop),
        Op::Map(d, b) | Op::ReduceMap(_, d, b) => {
            walk(d, true);
            walk(b, true);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use backend::{ATyp, ArkBn254};
    use petgraph::graph::NodeIndex;

    type C = ArkBn254;

    fn r(i: usize) -> Ref {
        Ref(NodeIndex::new(i))
    }

    fn leaf(i: usize) -> GOp<C> {
        Op::Ref(r(i), ATyp::vec_scalar(2))
    }

    fn value() -> Arc<Value<C>> {
        Arc::new(Value::vec_scalar(vec![Default::default(); 2]))
    }

    #[test]
    fn a_single_use_moves_the_value_out() {
        let v = value();
        let ops = Operands::owned(&leaf(0), HashMap::from([(r(0), Arc::clone(&v))]));
        let got = ops.get(r(0)).unwrap();
        assert!(Arc::ptr_eq(&got, &v));
        assert_eq!(Arc::strong_count(&v), 2, "operands kept no reference");
    }

    #[test]
    fn earlier_uses_clone_and_the_last_moves() {
        let op = Op::mul(leaf(0), leaf(0), ATyp::vec_scalar(2));
        let v = value();
        let ops = Operands::owned(&op, HashMap::from([(r(0), Arc::clone(&v))]));
        let first = ops.get(r(0)).unwrap();
        assert_eq!(Arc::strong_count(&v), 3, "first use clones");
        let second = ops.get(r(0)).unwrap();
        assert_eq!(Arc::strong_count(&v), 3, "last use moves");
        drop((first, second));
    }

    #[test]
    fn uses_inside_a_map_are_never_moved() {
        let op = Op::map(leaf(1), leaf(0));
        let v = value();
        let ops = Operands::owned(&op, HashMap::from([(r(0), Arc::clone(&v))]));
        let uses: Vec<_> = (0..5).map(|_| ops.get(r(0)).unwrap()).collect();
        assert_eq!(Arc::strong_count(&v), 7, "operands still holds it");
        drop(uses);
    }

    #[test]
    fn borrowed_operands_always_clone() {
        let v = value();
        let values = HashMap::from([(r(0), Arc::clone(&v))]);
        let ops = Operands::borrowed(&values);
        let uses: Vec<_> = (0..3).map(|_| ops.get(r(0)).unwrap()).collect();
        assert_eq!(Arc::strong_count(&v), 6);
        drop(uses);
    }

    #[test]
    fn a_missing_operand_is_none() {
        let ops = Operands::<C>::owned(&leaf(0), HashMap::new());
        assert!(ops.get(r(0)).is_none());
    }

    #[test]
    #[should_panic(expected = "after its last counted use")]
    fn a_use_past_the_count_panics() {
        let ops = Operands::owned(&leaf(0), HashMap::from([(r(0), value())]));
        let _ = ops.get(r(0));
        let _ = ops.get(r(0));
    }
}
