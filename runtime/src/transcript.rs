//! The Fiat-Shamir transcript of one run, shared by prover and verifier.
//!
//! Instance inputs and prover messages are queued as they are produced and
//! absorbed, in order, when the next challenge is drawn. Instance inputs are
//! absorbed whole, however large (an R1CS instance's matrices are tens of
//! megabytes); Zippel's sponge is BLAKE3 (`graph::domain_separator::Sponge`)
//! so that stays cheap.

use backend::{Backend, Value, value_to_bytes};
use lang::ast::Exclusion;
use petgraph::graph::NodeIndex;
use spongefish::{DuplexSpongeInterface, ProverState};
use std::collections::HashMap;

/// Where a run's Fiat-Shamir challenges come from: a transcript that binds public
/// values and derives challenges from them.
///
/// A run's default is Zippel's own, a spongefish [`ProverState`] opened with the
/// protocol's domain separator. Any other transcript can stand in for it (see
/// `CompiledProver::prove_with`): driving another implementation's transcript
/// makes a Zippel proof checkable by that implementation's verifier, and lets
/// Zippel's verifier check that implementation's proofs.
pub trait Challenger<C: Backend> {
    /// Binds instance input `value`. Every instance input comes first, in argument
    /// order; only values before a challenge are bound.
    fn instance(&mut self, value: &Value<C>);

    /// Binds prover message `value`, in transcript order.
    fn message(&mut self, value: &Value<C>);

    /// The next challenge, bound to every value absorbed so far. An excluded
    /// challenge is replaced by the next one.
    fn challenge(&mut self) -> Value<C>;
}

/// Zippel's transcript: each value's canonical bytes absorbed into the sponge, and
/// each challenge squeezed from it.
impl<C: Backend, H: DuplexSpongeInterface<U = u8>> Challenger<C> for ProverState<H> {
    fn instance(&mut self, value: &Value<C>) {
        self.public_message(value_to_bytes(value).as_slice());
    }

    fn message(&mut self, value: &Value<C>) {
        self.public_message(value_to_bytes(value).as_slice());
    }

    fn challenge(&mut self) -> Value<C> {
        Value::challenge(self)
    }
}

/// A value queued for the transcript, bound before the next challenge.
enum PendingAbsorb<C: Backend> {
    /// An instance input.
    Instance(Value<C>),
    /// A verifier's copy of a prover message.
    Message(Value<C>),
    /// A prover message the transcript also keeps for the proof: queued by
    /// node, so the message is held once.
    Kept(NodeIndex),
}

/// The Fiat-Shamir side of one run: the challenger, the values queued for it,
/// and, for the prover, the messages that form the proof.
///
/// Transcript nodes use it one at a time: the graph chains them in
/// transcript order, so only one is ever ready.
pub(crate) struct Transcript<'a, C: Backend, Ch: Challenger<C>> {
    challenger: &'a mut Ch,
    /// Absorbed, in order, only when a challenge is drawn: the transcript's
    /// only output is challenges, so values after the last challenge (every
    /// value, in a protocol with no challenges) never need serializing.
    pending: Vec<PendingAbsorb<C>>,
    /// Prover messages by node, for the proof; `None` for the verifier.
    messages: Option<HashMap<NodeIndex, Value<C>>>,
}

impl<'a, C: Backend, Ch: Challenger<C>> Transcript<'a, C, Ch> {
    /// A transcript over `challenger`; `keep_messages` for the prover, whose
    /// messages form the proof.
    pub(crate) fn new(challenger: &'a mut Ch, keep_messages: bool) -> Self {
        Self {
            challenger,
            pending: Vec::new(),
            messages: keep_messages.then(HashMap::new),
        }
    }

    /// Queues an instance input for the transcript.
    pub(crate) fn instance(&mut self, value: Value<C>) {
        self.pending.push(PendingAbsorb::Instance(value));
    }

    /// Queues the message of transcript node `node` for the transcript, and
    /// keeps it for the proof.
    pub(crate) fn message(&mut self, node: NodeIndex, value: &Value<C>) {
        if let Some(messages) = &mut self.messages {
            messages.insert(node, value.clone());
            self.pending.push(PendingAbsorb::Kept(node));
        } else {
            self.pending.push(PendingAbsorb::Message(value.clone()));
        }
    }

    /// Absorbs everything queued, then draws a challenge, drawn again while
    /// `exclusion` excludes it, as prover and verifier both do.
    pub(crate) fn challenge(&mut self, exclusion: Option<&Exclusion<Value<C>, usize>>) -> Value<C> {
        for p in self.pending.drain(..) {
            match &p {
                PendingAbsorb::Instance(v) => self.challenger.instance(v),
                PendingAbsorb::Message(v) => self.challenger.message(v),
                PendingAbsorb::Kept(node) => self
                    .challenger
                    .message(&self.messages.as_ref().expect("kept messages")[node]),
            }
        }
        let mut value = self.challenger.challenge();
        while exclusion.is_some_and(|x| value.is_excluded_by(x)) {
            value = self.challenger.challenge();
        }
        value
    }

    /// The prover's messages by transcript node; empty for the verifier.
    pub(crate) fn into_messages(self) -> HashMap<NodeIndex, Value<C>> {
        self.messages.unwrap_or_default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use backend::ArkBls12_381;
    use graph::UDag;
    use graph::domain_separator::ZippelDomainSeparator;

    type C = ArkBls12_381;

    /// The first `n` challenges from a fresh sponge, each resampled while
    /// `exclusion` excludes it.
    fn challenges(n: usize, exclusion: Option<&Exclusion<Value<C>, usize>>) -> Vec<Value<C>> {
        let separator =
            ZippelDomainSeparator::<C>::new_zippel_domain_separator("test", &UDag::<C>::new());
        let mut sponge = separator.prover_state();
        let mut transcript = Transcript::<C, _>::new(&mut sponge, false);
        (0..n).map(|_| transcript.challenge(exclusion)).collect()
    }

    /// A challenge is resampled while its exclusion excludes it.
    #[test]
    fn an_excluded_challenge_is_resampled() {
        let plain: Vec<_> = challenges(3, None)
            .into_iter()
            .map(|c| match c {
                Value::Scalar(x) => x,
                _ => unreachable!("a challenge is a scalar"),
            })
            .collect();
        let excluded = Exclusion::Values(Value::VecScalar(vec![plain[1], plain[0]].into()));
        assert_eq!(challenges(1, Some(&excluded)), [Value::Scalar(plain[2])]);
    }

    /// The challenges after absorbing instance inputs and prover messages,
    /// pinned: they depend on the sponge, the value encoding and the
    /// bytes-to-field reduction, which prover and verifier must share.
    #[test]
    fn challenges_are_pinned() {
        let separator =
            ZippelDomainSeparator::<C>::new_zippel_domain_separator("test", &UDag::<C>::new());
        let mut sponge = separator.prover_state();
        let mut transcript = Transcript::<C, _>::new(&mut sponge, true);
        let f = |i: u64| <C as backend::Backend>::F::from(i);
        transcript.instance(Value::Scalar(f(5)));
        transcript.instance(Value::VecScalar(vec![f(1), f(2)].into()));
        let first = transcript.challenge(None);
        transcript.message(NodeIndex::new(0), &Value::Index(3));
        let second = transcript.challenge(None);
        let third = transcript.challenge(None);
        insta::assert_snapshot!(format!("{first}\n{second}\n{third}"));
    }
}
