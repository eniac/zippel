//! Module errors and their diagnostics.

use crate::ast::CSig;
use crate::ast::decl::DeclError;
use crate::ast::spanned::Spanned;
use crate::diagnostic::{Diagnostic, Phase};
use crate::id::{Tid, Vid};
use thiserror::Error;

use super::one_line;

/// Failure while assembling or concretizing a module.
#[derive(Error, Debug)]
pub enum ModuleError {
    /// Two declarations concretized to the same signature, so a call could
    /// not be resolved to a unique body.
    #[error("Overlapping declarations: {0}")]
    OverlapDeclaration(CSig),
    /// Two declarations of the same name are each at least as specific as the other (e.g.
    /// they differ only in type-variable names or return types), so every call that fits one
    /// is ambiguous.
    #[error("Interchangeable declarations: {0} and {1}")]
    InterchangeableDeclarations(CSig, CSig),
    /// A declaration failed its own checks (size substitution, range
    /// instantiation, concretization); carries the span of its name.
    #[error("Declaration error: {1}")]
    DeclarationError(std::ops::Range<usize>, #[source] DeclError),
    /// No declaration with the requested name exists in the module.
    #[error("Declaration not found: {0}")]
    DeclarationNotFound(String),
    /// A size was given for a range-kinded type variable, which takes every
    /// value of its range.
    #[error("A size was given for range-kinded `{}: {range}`", var.node)]
    SizeForRange {
        /// The variable, where it is declared.
        var: Spanned<Tid>,
        /// Its declared range, as written (`1..S`).
        range: String,
    },
    /// A protocol concretized to several instances, one per value of each
    /// range-kinded type variable the sizes left unset, where one protocol
    /// is to run.
    #[error("Protocol `{}` concretizes to {instances} instances", name.node)]
    AmbiguousProtocol {
        /// The protocol's name, where it is declared.
        name: Spanned<Vid>,
        /// Its range-kinded type variables that took more than one value.
        ranges: Vec<ExpandedRange>,
        /// How many instances it concretized to.
        instances: usize,
    },
}

/// A range-kinded type variable and the values it took when its declaration
/// was concretized.
#[derive(Debug, Clone)]
pub struct ExpandedRange {
    /// The variable, where it is declared.
    pub var: Spanned<Tid>,
    /// Its declared range, as written (`1..S`).
    pub range: String,
    /// The values it took, ascending.
    pub values: Vec<usize>,
}

impl From<&ModuleError> for Diagnostic {
    fn from(e: &ModuleError) -> Self {
        if let ModuleError::AmbiguousProtocol {
            name,
            ranges,
            instances,
        } = e
        {
            let mut d = Diagnostic::error(
                Phase::Type,
                name.span.clone(),
                &format!(
                    "Protocol `{}` concretizes to {instances} instances, so which one to run is ambiguous",
                    name.node
                ),
            )
            .primary_label("this protocol");
            for r in ranges {
                d = d.secondary_label(
                    r.var.span.clone(),
                    &format!(
                        "`{}: {}` takes {} values: {}",
                        r.var.node,
                        r.range,
                        r.values.len(),
                        listed(&r.values)
                    ),
                );
            }
            return d.note(
                "a protocol must concretize to one instance; make each range admit one value \
                 for the given sizes, or declare the variable a `Size`",
            );
        }
        if let ModuleError::SizeForRange { var, range } = e {
            return Diagnostic::error(
                Phase::Type,
                var.span.clone(),
                &format!(
                    "`{}` is range-kinded, so it cannot be given a size",
                    var.node
                ),
            )
            .primary_label(&format!(
                "`{}: {range}` takes every value of its range",
                var.node
            ))
            .note("only `Size` variables take values from the sizes");
        }
        if let ModuleError::InterchangeableDeclarations(first, second) = e {
            return Diagnostic::error(
                Phase::Type,
                second.name.span.clone(),
                &format!(
                    "Declarations of `{}` accept the same arguments, so every call to them is ambiguous",
                    second.name.node
                ),
            )
            .primary_label(&format!("`{}`", one_line(&second.to_string())))
            .secondary_label(
                first.name.span.clone(),
                &format!("`{}`", one_line(&first.to_string())),
            );
        }
        let (span, summary) = match e {
            ModuleError::OverlapDeclaration(sig) => (
                sig.name.span.clone(),
                format!(
                    "Declarations of `{}` overlap after size concretization",
                    sig.name.node
                ),
            ),
            ModuleError::DeclarationError(span, DeclError::EvalError(e)) => (
                span.clone(),
                format!("Cannot evaluate a size expression: {e}"),
            ),
            ModuleError::DeclarationError(span, DeclError::InvalidRange(sig, e)) => (
                span.clone(),
                format!("Invalid range in `{}`: {e}", sig.name.node),
            ),
            ModuleError::DeclarationError(span, DeclError::SubstError(e)) => {
                (span.clone(), e.to_string())
            }
            ModuleError::DeclarationNotFound(name) => {
                (0..0, format!("Declaration `{name}` not found"))
            }
            ModuleError::AmbiguousProtocol { .. }
            | ModuleError::SizeForRange { .. }
            | ModuleError::InterchangeableDeclarations(..) => {
                unreachable!("handled above")
            }
        };
        let mut d = Diagnostic::error(Phase::Type, span, &one_line(&summary))
            .primary_label("while concretizing sizes for this declaration");
        if let ModuleError::OverlapDeclaration(sig) = e {
            d = d.note(&format!(
                "both declarations concretize to `{}`",
                one_line(&sig.to_string())
            ));
        }
        d
    }
}

/// `values`, comma-separated; long lists keep their first three and last.
fn listed(values: &[usize]) -> String {
    let show = |vs: &[usize]| {
        vs.iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(", ")
    };
    match values {
        [first @ .., last] if first.len() > 4 => format!("{}, …, {last}", show(&first[..3])),
        _ => show(values),
    }
}

impl From<ModuleError> for Diagnostic {
    fn from(e: ModuleError) -> Self {
        Diagnostic::from(&e)
    }
}
