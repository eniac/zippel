//! Runtime monomial ordering data — a Singular-style product (block) ordering.
//!
//! Every Singular ring ordering is a product of blocks
//! `(o₁(n₁), o₂(n₂), …)`; "pure lex" / "pure grevlex" are single-block cases.
//! [`MonoOrder`] mirrors that model so it can drive both the ark-gb backend
//! (subset) and a future Singular backend (full set).
//!
//! The type is fully expressive. The ark-gb backend implements a subset and
//! returns [`UnsupportedMonoOrder`] for the rest; see
//! `analyses/src/backend/ark_gb.rs` (Phase 1).

use graph::PRef;

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
    /// Degree lexicographic (`Dp`).
    DegLex,
    /// Weighted reverse-lexicographic (`wp`). Positive weights only.
    WeightedRevLex(Vec<i64>),
    /// Weighted lexicographic (`Wp`). Positive weights only.
    WeightedLex(Vec<i64>),
}

/// Error returned by a backend that does not support the requested ordering.
#[derive(Clone, Debug, thiserror::Error)]
#[error("the requested monomial ordering is not supported by this backend")]
pub struct UnsupportedMonoOrder;

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

        // Collect all variables from both monomials.
        let mut all_vars: Vec<PRef> = a.vars();
        all_vars.extend(b.vars());
        all_vars.sort();
        all_vars.dedup();

        // Assign each variable to a block.
        let mut seen = std::collections::HashSet::new();
        for block in &self.blocks {
            if let Some(vs) = &block.vars {
                for v in vs {
                    seen.insert(v.reference);
                }
            }
        }

        // For each block, compare the sub-monomials.
        for block in &self.blocks {
            let block_vars: &[PRef] = block.vars.as_deref().unwrap_or(&[]);

            match block.kind {
                BlockKind::Lex => {
                    for v in block_vars {
                        let ea = a.powers_for(v);
                        let eb = b.powers_for(v);
                        match ea.cmp(&eb) {
                            Ordering::Equal => continue,
                            ord => return ord,
                        }
                    }
                }
                BlockKind::GrevLex => {
                    // Total degree of the block.
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
                _ => {
                    // Unsupported orderings — fall through.
                }
            }
        }

        // Variables not in any explicit block: treat as a final GrevLex block.
        let remaining: Vec<&PRef> = all_vars
            .iter()
            .filter(|v| !seen.contains(&v.reference))
            .collect();
        let da: usize = remaining.iter().map(|v| a.powers_for(v)).sum();
        let db: usize = remaining.iter().map(|v| b.powers_for(v)).sum();
        match da.cmp(&db) {
            Ordering::Equal => {}
            ord => return ord.reverse(),
        }
        for v in remaining.iter().rev() {
            let ea = a.powers_for(v);
            let eb = b.powers_for(v);
            match ea.cmp(&eb) {
                Ordering::Equal => continue,
                ord => return ord,
            }
        }

        Ordering::Equal
    }
}
