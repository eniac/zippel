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
//! - Proto `verify` requirement

mod alias_cycle;
mod dead_var;
mod duplicate;
mod edit_distance;
mod proto;
mod purity;
mod scope;
mod size;
mod typevar;
mod verify;

use std::ops::Range;

use crate::diagnostic::SecondaryLabel;
use crate::id::Tid;

pub use alias_cycle::check_type_alias_cycles;
pub use dead_var::check_dead_variables;
pub use duplicate::check_duplicate_declarations;
pub use proto::check_proto_requirement;
pub use purity::check_purity;
pub use scope::check_scope;
pub use size::check_size_binding;
pub use typevar::check_typevars;
pub use verify::check_proto_verify;

pub(crate) use edit_distance::levenshtein;

use crate::ast::Size;
use crate::ast::spanned::Spanned;
use crate::id::Vid;

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
