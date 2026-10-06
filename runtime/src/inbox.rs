//! Operands delivered to a node by the nodes it reads.
//!
//! Values travel along the graph's edges: when a node finishes, it delivers
//! its value into the inbox of each successor that reads it, and a node
//! takes its whole inbox when it runs. A value therefore lives exactly as
//! long as some inbox or some running node holds it, with no count of its
//! readers kept anywhere.

use arc_swap::ArcSwapOption;
use graph::Ref;
use std::collections::HashMap;
use std::sync::Arc;

/// The operands one node reads: one slot per node it references, filled by
/// that node's [`Inbox::deliver`] and emptied by [`Inbox::take_all`].
pub(crate) struct Inbox<T> {
    /// Sorted by `Ref`, one slot per distinct reference.
    slots: Vec<(Ref, ArcSwapOption<T>)>,
}

impl<T> Inbox<T> {
    /// An inbox expecting one delivery from each distinct node in `refs`.
    pub fn new(refs: impl IntoIterator<Item = Ref>) -> Self {
        let mut refs: Vec<Ref> = refs.into_iter().collect();
        refs.sort_unstable();
        refs.dedup();
        Inbox {
            slots: refs
                .into_iter()
                .map(|r| (r, ArcSwapOption::empty()))
                .collect(),
        }
    }

    /// The nodes this inbox expects a delivery from.
    pub fn sources(&self) -> impl Iterator<Item = Ref> + '_ {
        self.slots.iter().map(|(r, _)| *r)
    }

    /// Delivers `from`'s value. Does nothing if this inbox does not read
    /// `from` (the edge only orders the two nodes).
    ///
    /// # Panics
    /// Panics if `from` has already delivered.
    pub fn deliver(&self, from: Ref, value: &Arc<T>) {
        if let Ok(i) = self.slots.binary_search_by_key(&from, |(r, _)| *r) {
            let previous = self.slots[i].1.swap(Some(Arc::clone(value)));
            assert!(previous.is_none(), "{from:?} delivered twice");
        }
    }

    /// Takes every operand, leaving the inbox empty.
    ///
    /// # Panics
    /// Panics if an operand has not been delivered.
    pub fn take_all(&self) -> HashMap<Ref, Arc<T>> {
        self.slots
            .iter()
            .map(|(r, slot)| {
                let value = slot
                    .swap(None)
                    .unwrap_or_else(|| panic!("operand {r:?} was not delivered"));
                (*r, value)
            })
            .collect()
    }

    /// Whether no delivered value is still waiting to be taken.
    pub fn is_empty(&self) -> bool {
        self.slots.iter().all(|(_, slot)| slot.load().is_none())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use petgraph::graph::NodeIndex;

    fn r(i: usize) -> Ref {
        Ref(NodeIndex::new(i))
    }

    #[test]
    fn takes_what_was_delivered() {
        let inbox = Inbox::new([r(2), r(1), r(2)]);
        assert_eq!(inbox.sources().collect::<Vec<_>>(), [r(1), r(2)]);
        inbox.deliver(r(1), &Arc::new("one"));
        inbox.deliver(r(2), &Arc::new("two"));
        assert!(!inbox.is_empty());
        let env = inbox.take_all();
        assert_eq!((*env[&r(1)], *env[&r(2)]), ("one", "two"));
        assert!(inbox.is_empty());
    }

    #[test]
    fn ignores_nodes_it_does_not_read() {
        let inbox = Inbox::new([r(1)]);
        inbox.deliver(r(7), &Arc::new(7));
        assert!(inbox.is_empty());
    }

    #[test]
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
        inbox.deliver(r(1), &Arc::new(1));
        inbox.deliver(r(1), &Arc::new(1));
    }

    #[test]
    #[should_panic(expected = "was not delivered")]
    fn rejects_taking_a_missing_operand() {
        let inbox = Inbox::<u8>::new([r(1)]);
        inbox.take_all();
    }
}
