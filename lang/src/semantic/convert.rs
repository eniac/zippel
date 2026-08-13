//! Convert `SemanticError` into `Diagnostic` for rendering.

use crate::diagnostic::{Diagnostic, Phase, SecondaryLabel, Severity, Suggestion};

use super::SemanticError;

impl From<SemanticError> for Diagnostic {
    fn from(err: SemanticError) -> Self {
        match err {
            SemanticError::UndefinedVariable {
                name,
                use_span,
                similar,
            } => {
                let mut suggestions = Vec::new();
                if !similar.is_empty() {
                    let names: Vec<String> =
                        similar.iter().map(|(n, _)| format!("`{n}`")).collect();
                    suggestions.push(Suggestion {
                        message: format!("did you mean {}?", names.join(", ")),
                        span: use_span.clone(),
                        replacement: similar[0].0 .0.clone(),
                        applicability: crate::diagnostic::Applicability::MaybeIncorrect,
                    });
                }
                Diagnostic {
                    severity: Severity::Error,
                    phase: Phase::Semantic,
                    span: use_span,
                    summary: format!("undefined variable `{name}`"),
                    primary_label: format!("`{name}` is not defined in this scope"),
                    secondary_labels: similar
                        .into_iter()
                        .map(|(n, span)| SecondaryLabel {
                            span,
                            message: format!("`{n}` defined here"),
                        })
                        .collect(),
                    notes: vec![],
                    suggestions,
                    code: None,
                }
            }
            SemanticError::UnboundSizeVar { name, use_span } => Diagnostic {
                severity: Severity::Error,
                phase: Phase::Semantic,
                span: use_span.clone(),
                summary: format!("unbound size variable `{name}`"),
                primary_label: format!("`{name}` is not declared as a type variable"),
                secondary_labels: vec![],
                notes: vec![],
                suggestions: vec![Suggestion {
                    message: format!("add `{name}: Size` to the type variable list"),
                    span: use_span,
                    replacement: String::new(),
                    applicability: crate::diagnostic::Applicability::MaybeIncorrect,
                }],
                code: None,
            },
            SemanticError::InvalidGroupRef {
                ref_name,
                ref_span,
                tv_name,
                actual_kind,
            } => Diagnostic {
                severity: Severity::Error,
                phase: Phase::Semantic,
                span: ref_span.clone(),
                summary: format!("`{ref_name}` is not a Group"),
                primary_label: format!(
                    "`{ref_name}` is {actual_kind}, but `{tv_name}` requires a Group"
                ),
                secondary_labels: vec![],
                notes: vec![],
                suggestions: vec![],
                code: None,
            },
            SemanticError::DuplicateTypevar {
                name,
                first_span,
                second_span,
            } => Diagnostic {
                severity: Severity::Error,
                phase: Phase::Semantic,
                span: second_span.clone(),
                summary: format!("duplicate type variable `{name}`"),
                primary_label: format!("`{name}` declared a second time here"),
                secondary_labels: vec![SecondaryLabel {
                    span: first_span,
                    message: format!("`{name}` first declared here"),
                }],
                notes: vec![],
                suggestions: vec![],
                code: None,
            },
            SemanticError::InvalidRangeBounds {
                name,
                span,
                start,
                end,
            } => Diagnostic {
                severity: Severity::Error,
                phase: Phase::Semantic,
                span: span.clone(),
                summary: format!("invalid range bounds for `{name}`"),
                primary_label: format!(
                    "range `{start}..{end}` is invalid: start ({start}) must be ≤ end ({end})"
                ),
                secondary_labels: vec![],
                notes: vec![],
                suggestions: vec![],
                code: None,
            },
            SemanticError::UnresolvedGroupRef { name, ref_span } => Diagnostic {
                severity: Severity::Error,
                phase: Phase::Semantic,
                span: ref_span.clone(),
                summary: format!("unresolved group reference `{name}`"),
                primary_label: format!("`{name}` is not declared as a type variable"),
                secondary_labels: vec![],
                notes: vec![],
                suggestions: vec![Suggestion {
                    message: format!("declare `{name}` as a type variable with `Group` kind"),
                    span: ref_span,
                    replacement: String::new(),
                    applicability: crate::diagnostic::Applicability::MaybeIncorrect,
                }],
                code: None,
            },
            SemanticError::CircularTypevarRef { cycle } => {
                // Close the cycle: V → G → V
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
                        message: format!("`{t}` references the next type variable in the cycle"),
                    })
                    .collect();

                Diagnostic {
                    severity: Severity::Error,
                    phase: Phase::Semantic,
                    span: primary_span,
                    summary: "circular type variable reference".to_string(),
                    primary_label: format!("cycle: {cycle_str}"),
                    secondary_labels,
                    notes: vec![],
                    suggestions: vec![],
                    code: None,
                }
            }
            SemanticError::DuplicateDeclaration {
                name,
                first_span,
                second_span,
            } => Diagnostic {
                severity: Severity::Error,
                phase: Phase::Semantic,
                span: second_span.clone(),
                summary: format!("duplicate declaration: {name}"),
                primary_label: format!("{name} declared a second time here"),
                secondary_labels: vec![SecondaryLabel {
                    span: first_span,
                    message: format!("{name} first defined here"),
                }],
                notes: vec![],
                suggestions: vec![],
                code: None,
            },
            SemanticError::TypeAliasCycle { cycle } => {
                // Close the cycle: A → B → C → A
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
                        message: format!("`{t}` aliases the next type in the cycle"),
                    })
                    .collect();

                Diagnostic {
                    severity: Severity::Error,
                    phase: Phase::Semantic,
                    span: primary_span,
                    summary: "circular type alias".to_string(),
                    primary_label: format!("cycle: {cycle_str}"),
                    secondary_labels,
                    notes: vec![],
                    suggestions: vec![],
                    code: None,
                }
            }
            SemanticError::NoProtoDeclaration { file_span } => Diagnostic {
                severity: Severity::Warning,
                phase: Phase::Semantic,
                span: file_span,
                summary: "no proto declaration found".to_string(),
                primary_label: "every file should contain at least one proto declaration"
                    .to_string(),
                secondary_labels: vec![],
                notes: vec![],
                suggestions: vec![Suggestion {
                    message: "add a `proto` declaration to this file".to_string(),
                    span: 0..0,
                    replacement: String::new(),
                    applicability: crate::diagnostic::Applicability::MachineApplicable,
                }],
                code: None,
            },
            SemanticError::MultipleProtoDeclarations {
                first_span,
                second_span,
            } => Diagnostic {
                severity: Severity::Error,
                phase: Phase::Semantic,
                span: second_span.clone(),
                summary: "multiple proto declarations".to_string(),
                primary_label: "a file should contain at most one proto declaration".to_string(),
                secondary_labels: vec![SecondaryLabel {
                    span: first_span,
                    message: "first proto declared here".to_string(),
                }],
                notes: vec![],
                suggestions: vec![],
                code: None,
            },
            SemanticError::ImpureRelation { span, construct } => Diagnostic {
                severity: Severity::Error,
                phase: Phase::Semantic,
                span: span.clone(),
                summary: format!("impure construct `{construct}` in proto relation"),
                primary_label: format!("`{construct}` is not allowed in a proto relation"),
                secondary_labels: vec![],
                notes: vec![crate::diagnostic::Note {
                    message: "proto relations must be relation-pure (no challenge, log, or verify)"
                        .to_string(),
                }],
                suggestions: vec![],
                code: None,
            },
        }
    }
}
