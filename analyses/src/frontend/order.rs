//! Runtime monomial ordering data — a Singular-style product (block) ordering.
//!
//! Every Singular ring ordering is a product of blocks
//! `(o₁(n₁), o₂(n₂), …)`; "pure lex" / "pure grevlex" are single-block cases.
//! [`MonoOrder`] mirrors that model so it can drive both the ark-gb backend
//! (subset) and a future Singular backend (full set).
//!
//! The type is fully expressive. The ark-gb backend implements a subset and
//! returns [`BackendError::UnsupportedOrder`] for the rest; see
//! `analyses/src/backend/ark_gb.rs` (Phase 1).

use crate::PRef;

/// A monomial ordering as runtime data: a product of [`Block`]s.
///
/// Use the constructors for the common cases:
/// - [`MonoOrder::grevlex`] — single GrevLex block, vars inferred from the
///   ideal, `PRef::Ord` reverse-lex tiebreak. Zero-arg.
/// - [`MonoOrder::lex`] — single Lex block; requires an explicit variable
///   ranking (which variable is "largest" is positional).
/// - [`MonoOrder::block`] — arbitrary product of blocks.
#[derive(Clone, Debug)]
pub struct MonoOrder {
    blocks: Vec<Block>,
}

/// One block of a product ordering.
#[derive(Clone, Debug)]
pub struct Block {
    /// The variables in this block, in block order.
    ///
    /// `None` means "all remaining variables" and is valid only for the last
    /// block (mirrors Singular's auto-sized last block). The backend infers
    /// the variable set from the ideal.
    pub vars: Option<Vec<PRef>>,
    pub kind: BlockKind,
}

/// The ordering applied within a [`Block`].
#[derive(Clone, Debug)]
pub enum BlockKind {
    /// Lexicographic (`lp`).
    Lex,
    /// Degree reverse-lexicographic (`dp`). The reverse-lex tiebreak uses
    /// `PRef::Ord` implicitly.
    GrevLex,
}

/// Error returned by a Gröbner-basis backend.
///
/// `UnsupportedOrder` is the only structurally-meaningful variant for
/// cross-backend dispatch (the caller can fall back to another backend).
/// `Other` carries an opaque message for operational failures (e.g. a
/// missing binary or a parse glitch in the Singular backend); callers can
/// log it or surface it without knowing the internal failure taxonomy.
#[derive(Clone, Debug, thiserror::Error)]
pub enum BackendError {
    #[error("the requested monomial ordering is not supported by this backend")]
    UnsupportedOrder,
    #[error("{0}")]
    Other(String),
}

impl MonoOrder {
    /// Single GrevLex block; variables are inferred from the ideal and the
    /// reverse-lex tiebreak uses `PRef::Ord`.
    pub fn grevlex() -> Self {
        MonoOrder {
            blocks: vec![Block {
                vars: None,
                kind: BlockKind::GrevLex,
            }],
        }
    }

    /// Single Lex block with an explicit variable ranking. The first element
    /// of `var_order` is the "largest" (highest elimination priority).
    pub fn lex(var_order: Vec<PRef>) -> Self {
        MonoOrder {
            blocks: vec![Block {
                vars: Some(var_order),
                kind: BlockKind::Lex,
            }],
        }
    }

    /// Arbitrary product of blocks. The last block may carry `vars: None`.
    pub fn block(blocks: Vec<Block>) -> Self {
        MonoOrder { blocks }
    }

    /// Iterate the blocks in product order.
    pub fn blocks(&self) -> &[Block] {
        &self.blocks
    }

    /// Assign each variable in `all_vars` to its block, returning
    /// `(BlockKind, vars)` pairs in block order.
    ///
    /// A block with `vars: None` claims all remaining unassigned variables
    /// (mirrors Singular's auto-sized last block). Variables not covered by
    /// any explicit block are appended as a final implicit `GrevLex` block.
    ///
    /// Deduplication uses full `PRef` identity (not just `reference`), so
    /// distinct PRefs sharing the same `Ref`/`NodeIndex` are treated as
    /// separate variables.
    ///
    /// Empty blocks are skipped from the result. The returned Vec is
    /// self-contained — callers do not need to handle a separate "remaining"
    /// bucket.
    pub fn block_var_assignment(&self, all_vars: &[PRef]) -> Vec<(BlockKind, Vec<PRef>)> {
        let mut result: Vec<(BlockKind, Vec<PRef>)> = Vec::with_capacity(self.blocks.len() + 1);
        let mut seen: std::collections::HashSet<&PRef> = std::collections::HashSet::new();

        for block in &self.blocks {
            let mut bv = Vec::new();
            match &block.vars {
                Some(vs) => {
                    for v in vs {
                        if seen.insert(v) {
                            bv.push(v.clone());
                        }
                    }
                }
                None => {
                    for v in all_vars {
                        if seen.insert(v) {
                            bv.push(v.clone());
                        }
                    }
                }
            }
            if !bv.is_empty() {
                result.push((block.kind.clone(), bv));
            }
        }

        // Variables not covered by any explicit block: implicit final GrevLex.
        let remaining: Vec<PRef> = all_vars
            .iter()
            .filter(|v| !seen.contains(v))
            .cloned()
            .collect();
        if !remaining.is_empty() {
            result.push((BlockKind::GrevLex, remaining));
        }

        result
    }

    /// Compare two monomials under this ordering.
    /// Returns `Ordering::Less` if `a` is the leading monomial (the one that
    /// sorts first), matching zippel's convention.
    ///
    /// **Note**: this requires all variables in both monomials to be covered
    /// by the blocks. Variables not in any block are treated as belonging to
    /// a final implicit GrevLex block.
    pub fn compare(
        &self,
        a: &crate::frontend::Monomial,
        b: &crate::frontend::Monomial,
    ) -> core::cmp::Ordering {
        use core::cmp::Ordering;

        let mut all_vars: Vec<PRef> = a.vars();
        all_vars.extend(b.vars());
        all_vars.sort();
        all_vars.dedup();

        for (kind, block_vars) in self.block_var_assignment(&all_vars) {
            match kind {
                BlockKind::Lex => {
                    for v in &block_vars {
                        let ea = a.powers_for(v);
                        let eb = b.powers_for(v);
                        match ea.cmp(&eb) {
                            Ordering::Equal => continue,
                            ord => return ord,
                        }
                    }
                }
                BlockKind::GrevLex => {
                    let da: usize = block_vars.iter().map(|v| a.powers_for(v)).sum();
                    let db: usize = block_vars.iter().map(|v| b.powers_for(v)).sum();
                    match da.cmp(&db) {
                        Ordering::Equal => {}
                        ord => return ord.reverse(), // higher degree = leading = Less
                    }
                    // Right-to-left tiebreak: at the rightmost variable where
                    // exponents differ, smaller exponent = leading = Less.
                    for v in block_vars.iter().rev() {
                        let ea = a.powers_for(v);
                        let eb = b.powers_for(v);
                        match ea.cmp(&eb) {
                            Ordering::Equal => continue,
                            ord => return ord, // smaller exp = Less = leading
                        }
                    }
                }
            }
        }

        Ordering::Equal
    }
}
