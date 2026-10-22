//! Semantic analysis: the checks that report diagnostics about a module, apart from building,
//! concretizing and type-checking it.
//!
//! [`check_decls`] runs the checks that need no type information, on the parsed declarations:
//! - Variable scope (defined-before-use)
//! - Typevar kind validation (group references, range bounds, cycles)
//! - Size variable binding
//! - Duplicate declarations
//! - Type alias cycles
//! - Proto declaration requirement
//! - Relation purity
//! - Unused variables and functions
//!
//! `check_instances` runs the checks that follow resolved calls, on type-checked instances:
//! - Proto `verify` requirement
//!
//! [`check_protocol_instances`] checks that a protocol to run concretized to one instance.

mod alias_cycle;
mod dead_var;
mod duplicate;
mod edit_distance;
mod proto;
mod protocol;
mod purity;
mod scope;
mod size;
mod typevar;
mod unused_fn;
mod verify;

use std::ops::Range;

use crate::diagnostic::SecondaryLabel;
use crate::id::Tid;

pub use alias_cycle::check_type_alias_cycles;
pub use dead_var::check_dead_variables;
pub use duplicate::check_duplicate_declarations;
pub use proto::check_proto_requirement;
pub use protocol::check_protocol_instances;
pub use purity::check_purity;
pub use scope::check_scope;
pub use size::check_size_binding;
pub use typevar::check_typevars;
pub use unused_fn::check_unused_functions;

pub(crate) use edit_distance::levenshtein;

use crate::ast::Size;
use crate::ast::decl::{Body, BodyTypes, CBody, UDecl};
use crate::ast::sig::CSig;
use crate::ast::spanned::Spanned;
use crate::diagnostic::Diagnostic;
use crate::id::Vid;

/// What the checks that need no type information report about parsed declarations.
pub struct DeclChecks {
    /// Their diagnostics, in check order.
    pub diagnostics: Vec<Diagnostic>,
    /// Whether the type aliases form a cycle, so they cannot be inlined.
    pub alias_cycle: bool,
}

/// Runs every check that needs no type information on `decls`, parsed from a file spanning
/// `file_span`.
pub fn check_decls(decls: &[Spanned<UDecl>], file_span: Range<usize>) -> DeclChecks {
    let mut diagnostics = Vec::new();
    // Module-level checks.
    diagnostics.extend(check_duplicate_declarations(decls));
    diagnostics.extend(check_proto_requirement(decls, file_span));
    diagnostics.extend(check_unused_functions(decls));
    let alias_cycles = check_type_alias_cycles(decls);
    let alias_cycle = !alias_cycles.is_empty();
    diagnostics.extend(alias_cycles);
    // Per-declaration checks.
    for decl in decls {
        diagnostics.extend(check_typevars(&decl.node.sig));
        diagnostics.extend(check_size_binding(&decl.node.sig));
        diagnostics.extend(check_scope(&decl.node));
        diagnostics.extend(check_dead_variables(&decl.node));
        if let Body::Proto { relation, .. } = &decl.node.body {
            diagnostics.extend(check_purity(relation));
        }
    }
    DeclChecks {
        diagnostics,
        alias_cycle,
    }
}

/// Runs every check that follows resolved calls on type-checked `instances`, each of which must
/// have type-checked so that every call has a resolution. Each diagnostic comes with the
/// instance it is about.
pub(crate) fn check_instances<'a>(
    instances: impl IntoIterator<Item = (&'a CSig, &'a CBody, &'a BodyTypes)>,
) -> Vec<(&'a CSig, Diagnostic)> {
    verify::check_proto_verify(instances)
}

/// The names a range's bounds mention, as value names with the span of each mention, in source
/// order. Bounds are sizes, so each must be a size parameter of `sizes`; the others are returned.
fn values_in_range<'a>(
    range: &'a crate::ast::range::Range<Size>,
    sizes: &[&Tid],
) -> Vec<(Vid, &'a Range<usize>)> {
    let mut found = Vec::new();
    let mut todo: Vec<&Spanned<Size>> =
        [range.end.as_ref(), range.step.as_ref(), Some(&range.start)]
            .into_iter()
            .flatten()
            .collect();
    while let Some(size) = todo.pop() {
        match &size.node {
            Size::Var(name) if !sizes.contains(&name) => {
                found.push((Vid::from(name.0.as_str()), &size.span));
            }
            Size::Var(_) | Size::Lit(_) => {}
            Size::Add(a, b)
            | Size::Sub(a, b)
            | Size::Mul(a, b)
            | Size::Div(a, b)
            | Size::Pow(a, b) => {
                todo.push(b);
                todo.push(a);
            }
        }
    }
    found
}

/// The size parameters of `decl`.
fn size_params(decl: &crate::ast::decl::UDecl) -> Vec<&Tid> {
    decl.sig.typevars.0.iter().map(|tv| &tv.id.node).collect()
}

/// Render a cycle as (cycle_str, primary_span, secondary_labels).
/// Shared by `CircularTypevarRef` and `TypeAliasCycle` — only the verb differs.
pub(crate) fn render_cycle(
    cycle: &[(Tid, Range<usize>)],
    verb: &str,
) -> (String, Range<usize>, Vec<SecondaryLabel>) {
    let names: Vec<String> = cycle.iter().map(|(t, _)| t.0.to_string()).collect();
    let mut cycle_str = names.join(" → ");
    if let Some(first) = names.first() {
        cycle_str.push_str(" → ");
        cycle_str.push_str(first);
    }

    let primary_span = cycle.first().map(|(_, s)| s.clone()).unwrap_or(0..0);
    let secondary_labels: Vec<SecondaryLabel> = cycle
        .iter()
        .skip(1)
        .map(|(t, s)| SecondaryLabel {
            span: s.clone(),
            message: format!("`{t}` {verb}"),
        })
        .collect();

    (cycle_str, primary_span, secondary_labels)
}
