//! Semantic analysis — checks that run after parsing but before type checking.
//!
//! These checks operate on the untyped AST (`UDecl`, `UExp`, etc.) and catch
//! errors that don't require full type inference:
//! - Variable scope (defined-before-use)
//! - Typevar kind validation (group references, range bounds, cycles)
//! - Size variable binding
//! - Duplicate declarations
//! - Type alias cycles
//! - Proto declaration requirement
//! - Relation purity

mod alias_cycle;
mod convert;
mod duplicate;
mod edit_distance;
mod proto;
mod purity;
mod scope;
mod size;
mod typevar;

use std::ops::Range;

use crate::id::{Tid, Vid};

pub use alias_cycle::check_type_alias_cycles;
pub use duplicate::check_duplicate_declarations;
pub use proto::check_proto_requirement;
pub use purity::check_purity;
pub use scope::check_scope;
pub use size::check_size_binding;
pub use typevar::check_typevars;

pub(crate) use edit_distance::levenshtein;

// ── SemanticError ──────────────────────────────────────────────────────

/// A semantic error found during semantic analysis (after parsing, before
/// type checking).
#[derive(Debug, Clone)]
pub enum SemanticError {
    /// Use of a variable before its definition (or undefined variable).
    UndefinedVariable {
        name: Vid,
        use_span: Range<usize>,
        similar: Vec<(Vid, Range<usize>)>,
    },
    /// Use of a size variable not declared in the typevar list.
    UnboundSizeVar { name: Tid, use_span: Range<usize> },
    /// A group reference in a kind resolves to a declared typevar but the
    /// kind doesn't match (e.g. `Pairing<F, F>` where `F: Field`).
    /// `ref_name` is the referenced typevar, `ref_span` is its use site,
    /// `tv_name` is the typevar whose kind contains the bad reference,
    /// `actual_kind` is a description of what `ref_name` actually is.
    InvalidGroupRef {
        ref_name: Tid,
        ref_span: Range<usize>,
        tv_name: Tid,
        actual_kind: String,
    },
    /// Two typevars share the same name in one declaration.
    DuplicateTypevar {
        name: Tid,
        first_span: Range<usize>,
        second_span: Range<usize>,
    },
    /// A range typevar has start > end.
    InvalidRangeBounds {
        name: Tid,
        span: Range<usize>,
        start: String,
        end: String,
    },
    /// A group reference in a kind doesn't resolve to any declared typevar.
    UnresolvedGroupRef { name: Tid, ref_span: Range<usize> },
    /// Circular reference among typevar kinds (e.g. V: Pairing<G>, G: Pairing<V>).
    /// `cycle` is a list of (typevar name, span of the kind reference) for
    /// each typevar in the cycle, in dependency order.
    CircularTypevarRef { cycle: Vec<(Tid, Range<usize>)> },
    /// Two declarations share the same signature.
    DuplicateDeclaration {
        name: String,
        first_span: Range<usize>,
        second_span: Range<usize>,
    },
    /// A type alias cycle (e.g. `type A = B; type B = A;`).
    /// `cycle` is a list of (alias name, span of the aliased type reference)
    /// for each alias in the cycle, in dependency order.
    TypeAliasCycle { cycle: Vec<(Tid, Range<usize>)> },
    /// No proto declaration in the file.
    NoProtoDeclaration { file_span: Range<usize> },
    /// Multiple proto declarations in the file.
    MultipleProtoDeclarations {
        first_span: Range<usize>,
        second_span: Range<usize>,
    },
    /// A proto relation contains impure constructs (Challenge/Log/Verify).
    ImpureRelation {
        span: Range<usize>,
        construct: String,
    },
}
