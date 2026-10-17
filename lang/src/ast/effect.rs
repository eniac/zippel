//! Direct syntactic effects, shared by purity queries and relation diagnostics.

use std::ops::Range;

use super::{Exp, ExpLiteral, ExpRef, Stmt, Visit};

/// A direct effect in the tree. Callee bodies are not inspected.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Effect {
    Random,
    Challenge,
    Log,
    Verify,
}

impl<'a, N: ExpLiteral> ExpRef<'a, N> {
    /// Direct effects and their source spans, in walk order. A log uses its statement's
    /// span; other effects use their expression's span. Calls only expose argument effects.
    pub(crate) fn effects(self) -> impl Iterator<Item = (Effect, &'a Range<usize>)> {
        self.walk().filter_map(|visit| match visit {
            Visit::Enter(e) => match e.node() {
                Exp::Random(..) => Some((Effect::Random, e.span())),
                Exp::Challenge(..) => Some((Effect::Challenge, e.span())),
                Exp::Verify(_) => Some((Effect::Verify, e.span())),
                _ => None,
            },
            Visit::EnterStmt(stmt) if matches!(stmt.node, Stmt::Log(..)) => {
                Some((Effect::Log, &stmt.span))
            }
            _ => None,
        })
    }

    /// Whether evaluating this expression has no protocol-visible effect:
    /// no transcript logging (`log`), no oracle `challenge`, no `random`
    /// sampling and no `verify`. Purity is what lets the graph
    /// builder duplicate, hoist or drop a subexpression freely.
    /// Calls are inspected through their arguments, not their callee bodies.
    pub fn is_pure(self) -> bool {
        self.effects().next().is_none()
    }

    /// Check if an expression is valid in a relation (where clause).
    ///
    /// Allows: `let`, `Random`, and all pure expressions.
    /// Rejects: `Challenge` (verifier oracle), `<-` (transcript),
    /// `Verify` (verifier-side check).
    pub fn is_relation_pure(self) -> bool {
        self.effects().all(|(effect, _)| effect == Effect::Random)
    }
}
