//! Operands delivered to a node by the nodes it reads.
//!
//! Values travel along the graph's edges: when a node finishes, it delivers
//! its value into the inbox of each successor that reads it, and a node
//! takes its whole inbox when it runs. A value is a cheap handle (cloning it
//! shares its buffers), so delivering to several readers clones the handle,
//! and a buffer lives exactly as long as some inbox or some running node
//! holds a handle to it, with no count of its readers kept anywhere.

use graph::Ref;
use std::collections::HashMap;
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, Ordering};

/// The operands one node reads: one expected source per node it references,
/// filled by that node's [`Inbox::deliver`] and emptied by
/// [`Inbox::take_all`].
///
/// Values are stored only once delivered: an inbox costs a `Ref` and a flag
/// per source until its first delivery, so a graph's inboxes stay small
/// however many edges it has.
pub(crate) struct Inbox<T> {
    /// Sorted, one per distinct reference, each flagged once it has
    /// delivered.
    sources: Vec<(Ref, AtomicBool)>,
    /// The delivered values, in delivery order.
    values: Mutex<Vec<(Ref, T)>>,
}

impl<T: Clone> Inbox<T> {
    /// An inbox expecting one delivery from each distinct node in `refs`.
    pub fn new(refs: impl IntoIterator<Item = Ref>) -> Self {
        let mut refs: Vec<Ref> = refs.into_iter().collect();
        refs.sort_unstable();
        refs.dedup();
        Inbox {
            sources: refs
                .into_iter()
                .map(|r| (r, AtomicBool::new(false)))
                .collect(),
            values: Mutex::new(Vec::new()),
        }
    }

    /// The nodes this inbox expects a delivery from.
    pub fn sources(&self) -> impl Iterator<Item = Ref> + '_ {
        self.sources.iter().map(|(r, _)| *r)
    }

    /// Delivers `from`'s value. Does nothing if this inbox does not read
    /// `from` (the edge only orders the two nodes).
    ///
    /// # Panics
    /// Panics if `from` has already delivered.
    pub fn deliver(&self, from: Ref, value: &T) {
        if let Ok(i) = self.sources.binary_search_by_key(&from, |(r, _)| *r) {
            let previous = self.sources[i].1.swap(true, Ordering::SeqCst);
            assert!(!previous, "{from:?} delivered twice");
            let mut values = self.values.lock().unwrap();
            if values.capacity() == 0 {
                values.reserve_exact(self.sources.len());
            }
            values.push((from, value.clone()));
        }
    }

    /// Takes every operand, leaving the inbox empty.
    ///
    /// # Panics
    /// Panics if an operand has not been delivered.
    pub fn take_all(&self) -> HashMap<Ref, T> {
        if let Some((r, _)) = self.sources.iter().find(|(_, d)| !d.load(Ordering::SeqCst)) {
            panic!("operand {r:?} was not delivered");
        }
        std::mem::take(&mut *self.values.lock().unwrap())
            .into_iter()
            .collect()
    }

    /// Whether no delivered value is still waiting to be taken.
    pub fn is_empty(&self) -> bool {
        self.values.lock().unwrap().is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use petgraph::graph::NodeIndex;
    use std::sync::Arc;

    fn r(i: usize) -> Ref {
        Ref(NodeIndex::new(i))
    }

    #[test]
    fn takes_what_was_delivered() {
        let inbox = Inbox::new([r(2), r(1), r(2)]);
        assert_eq!(inbox.sources().collect::<Vec<_>>(), [r(1), r(2)]);
        inbox.deliver(r(1), &"one");
        inbox.deliver(r(2), &"two");
        assert!(!inbox.is_empty());
        let env = inbox.take_all();
        assert_eq!((env[&r(1)], env[&r(2)]), ("one", "two"));
        assert!(inbox.is_empty());
    }

    #[test]
    fn ignores_nodes_it_does_not_read() {
        let inbox = Inbox::new([r(1)]);
        inbox.deliver(r(7), &7);
        assert!(inbox.is_empty());
    }

    #[test]
    /// A delivered handle is the reader's: once the sender drops its own,
    /// the inbox's copy is the only one.
    fn last_holder_owns_the_value() {
        let value = Arc::new(vec![0u8; 16]);
        let inbox = Inbox::new([r(1)]);
        inbox.deliver(r(1), &value);
        drop(value);
        let env = inbox.take_all();
        assert_eq!(Arc::strong_count(&env[&r(1)]), 1);
    }

    #[test]
    #[should_panic(expected = "delivered twice")]
    fn rejects_a_second_delivery() {
        let inbox = Inbox::new([r(1)]);
        inbox.deliver(r(1), &1);
        inbox.deliver(r(1), &1);
    }

    #[test]
    #[should_panic(expected = "was not delivered")]
    fn rejects_taking_a_missing_operand() {
        let inbox = Inbox::<u8>::new([r(1)]);
        inbox.take_all();
    }
}
