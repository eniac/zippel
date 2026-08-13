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
    /// A typevar's kind is invalid (e.g. Pairing referencing a non-Group).
    InvalidTypevarKind {
        name: Tid,
        span: Range<usize>,
        reason: KindError,
    },
    /// Two typevars share the same name in one declaration.
    DuplicateTypevar {
        name: Tid,
        first_span: Range<usize>,
        second_span: Range<usize>,
    },
    /// A range typevar has start > end.
    InvalidRangeBounds { name: Tid, span: Range<usize> },
    /// A group reference in a kind doesn't resolve to a declared typevar
    /// of the required kind.
    UnresolvedGroupRef {
        name: Tid,
        ref_span: Range<usize>,
        reason: KindError,
    },
    /// Circular reference among typevar kinds (e.g. V: Pairing<G>, G: Pairing<V>).
    CircularTypevarRef {
        cycle: Vec<Tid>,
        first_span: Range<usize>,
    },
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

/// Sub-category of kind errors for typevar validation.
#[derive(Debug, Clone)]
pub enum KindError {
    /// Expected a Group kind, found something else.
    NotAGroup,
    /// Expected a Scalar kind, found something else.
    NotAScalar,
    /// Expected a Range or SizeVar kind, found something else.
    NotARangeOrSize,
    /// The referenced typevar is not declared at all.
    GroupNotDeclared,
}
