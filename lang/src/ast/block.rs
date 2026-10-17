//! Flat statement sequences and their optional expression result.

use super::{ExpId, Spanned};
use crate::id::Vid;

/// Statements evaluated in order, with bindings scoped to the rest of the block.
/// A block evaluates to its tail expression, or `()` when it has none.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Block {
    /// Statements, each spanning its source through its semicolon.
    pub stmts: Vec<Spanned<Stmt>>,
    /// The expression whose value the block returns.
    pub tail: Option<ExpId>,
}

impl Block {
    /// Whether statement `i` has something after it, a statement or the tail. Only then does
    /// its binder scope over anything.
    pub fn is_followed(&self, i: usize) -> bool {
        i + 1 < self.stmts.len() || self.tail.is_some()
    }
}

/// A statement owned by a block. Only its value is an expression in the arena.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Stmt {
    /// `let x = e;`: evaluate `e` and bind its value to `x`.
    Let(Spanned<Vid>, ExpId),
    /// `x <- e;`: send `e` to the transcript and bind its value to `x`.
    Log(Spanned<Vid>, ExpId),
    /// `e;`: evaluate `e` and discard its value.
    Discard(ExpId),
}

impl Stmt {
    /// The expression this statement evaluates.
    pub const fn value(&self) -> ExpId {
        match self {
            Self::Let(_, value) | Self::Log(_, value) | Self::Discard(value) => *value,
        }
    }

    /// The variable bound in the rest of the block, if any.
    pub const fn binder(&self) -> Option<&Spanned<Vid>> {
        match self {
            Self::Let(name, _) | Self::Log(name, _) => Some(name),
            Self::Discard(_) => None,
        }
    }
}
