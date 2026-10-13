//! The Fiat-Shamir transcript of one run, shared by prover and verifier.
//!
//! Instance inputs and prover messages are queued as they are produced and
//! absorbed, in order, when the next challenge is squeezed. Instance inputs
//! are absorbed whole, however large (an R1CS instance's matrices are tens of
//! megabytes); the sponge is BLAKE3 (`graph::domain_seperator::Sponge`) so
//! that stays cheap.

use backend::{ArkConfig, Value, value_to_bytes};
use petgraph::graph::NodeIndex;
use spongefish::{DuplexSpongeInterface, ProverState};
use std::collections::HashMap;

/// A value queued for the sponge, absorbed before the next challenge.
enum PendingAbsorb<C: ArkConfig> {
    /// An instance input, or a verifier's copy of a prover message.
    Owned(Value<C>),
    /// A prover message the transcript also keeps for the proof: queued by
    /// node, so the message is held once.
    Kept(NodeIndex),
}

/// The Fiat-Shamir side of one run: the sponge, the values queued for it,
/// and, for the prover, the messages that form the proof.
///
/// Transcript nodes use it one at a time: the graph chains them in
/// transcript order, so only one is ever ready.
pub(crate) struct Transcript<'a, C: ArkConfig, H: DuplexSpongeInterface<U = u8>> {
    sponge: &'a mut ProverState<H>,
    /// Absorbed, in order, only when a challenge is squeezed: the sponge's
    /// only output is challenges, so values after the last challenge (every
    /// value, in a protocol with no challenges) never need serializing.
    pending: Vec<PendingAbsorb<C>>,
    /// Prover messages by node, for the proof; `None` for the verifier.
    messages: Option<HashMap<NodeIndex, Value<C>>>,
}

impl<'a, C: ArkConfig, H: DuplexSpongeInterface<U = u8>> Transcript<'a, C, H> {
    /// A transcript over `sponge`; `keep_messages` for the prover, whose
    /// messages form the proof.
    pub(crate) fn new(sponge: &'a mut ProverState<H>, keep_messages: bool) -> Self {
        Self {
            sponge,
            pending: Vec::new(),
            messages: keep_messages.then(HashMap::new),
        }
    }

    /// Queues an instance input for the sponge.
    pub(crate) fn instance(&mut self, value: Value<C>) {
        self.pending.push(PendingAbsorb::Owned(value));
    }

    /// Queues the message of transcript node `node` for the sponge, and
    /// keeps it for the proof.
    pub(crate) fn message(&mut self, node: NodeIndex, value: &Value<C>) {
        if let Some(messages) = &mut self.messages {
            messages.insert(node, value.clone());
            self.pending.push(PendingAbsorb::Kept(node));
        } else {
            self.pending.push(PendingAbsorb::Owned(value.clone()));
        }
    }

    /// Absorbs everything queued, then squeezes a challenge.
    pub(crate) fn challenge(&mut self) -> Value<C> {
        for p in self.pending.drain(..) {
            let value = match &p {
                PendingAbsorb::Owned(v) => v,
                PendingAbsorb::Kept(node) => &self.messages.as_ref().expect("kept messages")[node],
            };
            let bytes = value_to_bytes(value).expect("value serialization should not fail");
            self.sponge.public_message(bytes.as_slice());
        }
        Value::<C>::challenge(self.sponge)
    }

    /// The prover's messages by transcript node; empty for the verifier.
    pub(crate) fn into_messages(self) -> HashMap<NodeIndex, Value<C>> {
        self.messages.unwrap_or_default()
    }
}
