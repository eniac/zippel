//! Typevar validator — checks type variable declarations for correctness.
//!
//! Validates:
//! - No duplicate typevar names in one declaration
//! - Group references in Pairing/Scalar kinds resolve to declared typevars
//! - Range bounds are valid (start <= end)
//! - No circular references among typevar kinds

use std::collections::{BTreeSet, HashSet};
use std::ops::Range;

use crate::ast::Sig;
use crate::ast::size::Size;
use crate::ast::spanned::Spanned;
use crate::diagnostic::{Applicability, Diagnostic, Phase};
use crate::id::Tid;
use crate::typ::{Kind, TypeVar};
use lang_derive::Diagnostic as DiagnosticDerive;
use share::Ctx;

// ── Simple diagnostics (derive) ────────────────────────────────────────

/// E0006: Two or more typevars share the same name in one declaration.
/// Uses the builder API because `spans` produces a variable number of
/// secondary labels when a name appears 3+ times.
/// The first occurrence is the primary span so labels render left-to-right.
fn duplicate_typevar(name: &Tid, spans: &[Range<usize>]) -> Diagnostic {
    let primary_span = spans.first().cloned().unwrap_or(0..0);
    let mut d = Diagnostic::error(
        Phase::Semantic,
        primary_span,
        &format!("duplicate type variable `{name}`"),
    )
    .code("E0006")
    .primary_label(&format!("`{name}` first declared here"));

    // Subsequent declarations
    for s in spans.iter().skip(1) {
        d = d.secondary_label(s.clone(), &format!("`{name}` also declared here"));
    }

    d
}

/// E0007: A range typevar has start > end.
#[derive(DiagnosticDerive)]
#[diag("invalid range bounds for `{$name}`", code = "E0007", error, Semantic)]
struct InvalidRangeBounds {
    #[span(label = "range `{$start}..{$end}` is invalid: start ({$start}) must be ≤ end ({$end})")]
    span: Range<usize>,
    name: Tid,
    start: String,
    end: String,
}

// ── Complex diagnostics (builder) ──────────────────────────────────────

/// E0004: A group reference in a kind resolves to a declared typevar but the
/// kind doesn't match (e.g. `Pairing<F, F>` where `F: Field`).
/// Uses the builder API because `ref_spans` produces a variable number of
/// secondary labels.
fn invalid_group_ref(
    ref_name: &Tid,
    ref_spans: &[Range<usize>],
    tv_name: &Tid,
    actual_kind: &str,
) -> Diagnostic {
    let primary_span = ref_spans.first().cloned().unwrap_or(0..0);
    let mut d = Diagnostic::error(
        Phase::Semantic,
        primary_span,
        &format!("`{ref_name}` is not a Group"),
    )
    .code("E0004")
    .primary_label(&format!(
        "`{ref_name}` is {actual_kind}, but `{tv_name}` requires a Group"
    ));

    for s in ref_spans.iter().skip(1) {
        d = d.secondary_label(s.clone(), &format!("`{ref_name}` also referenced here"));
    }

    d
}

/// E0005: A group reference in a kind doesn't resolve to any declared typevar.
/// Uses the builder API because `ref_spans` produces a variable number of
/// secondary labels, and the replacement is conditional on `is_empty`.
fn unresolved_group_ref(
    name: &Tid,
    ref_spans: &[Range<usize>],
    typevar_span: &Range<usize>,
    is_empty: bool,
) -> Diagnostic {
    let primary_span = ref_spans.first().cloned().unwrap_or(0..0);
    let mut d = Diagnostic::error(
        Phase::Semantic,
        primary_span,
        &format!("unresolved group reference `{name}`"),
    )
    .code("E0005")
    .primary_label(&format!("`{name}` is not declared as a type variable"));

    for s in ref_spans.iter().skip(1) {
        d = d.secondary_label(s.clone(), &format!("`{name}` also referenced here"));
    }

    // Insert at beginning of typevar list (Rev F):
    // empty list: "N: Group", non-empty: "N: Group, "
    let replacement = if is_empty {
        format!("{name}: Group")
    } else {
        format!("{name}: Group, ")
    };
    let sugg_span = typevar_span.start..typevar_span.start;
    d = d.suggestion(
        &format!("declare `{name}` as a type variable with `Group` kind"),
        sugg_span,
        &replacement,
        Applicability::MachineApplicable,
    );

    d
}

/// E0008: Circular reference among typevar kinds.
/// Uses the builder API because the cycle produces a variable number of
/// secondary labels and a computed kind note.
fn circular_typevar_ref(cycle: Vec<(Tid, Range<usize>)>, kinds: Vec<(Tid, String)>) -> Diagnostic {
    let (cycle_str, primary_span, secondary_labels) =
        super::render_cycle(&cycle, "references the next type variable in the cycle");
    let kind_note = kinds
        .iter()
        .map(|(t, k)| format!("`{t}` has kind `{k}`"))
        .collect::<Vec<_>>()
        .join(", ");

    Diagnostic::error(
        Phase::Semantic,
        primary_span,
        "circular type variable reference",
    )
    .code("E0008")
    .primary_label(&format!("cycle: {cycle_str}"))
    .secondary_labels(secondary_labels)
    .note(&kind_note)
}

// ── Check function ─────────────────────────────────────────────────────

/// Check type variable declarations in a signature.
pub fn check_typevars(sig: &Sig<Size>) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    let typevars = &sig.typevars.node.0;
    let typevar_span = sig.typevars.span.clone();
    let is_empty = typevars.is_empty();

    // 1. Check for duplicate typevar names
    // Collect all declaration spans per name, then emit one diagnostic per
    // duplicated name (first = "first declared here", second = primary,
    // 3+ = "also declared here").
    let mut spans_by_name: Ctx<Tid, Vec<Range<usize>>> = Ctx::new();
    for tv in typevars {
        let name = &tv.node.id.node;
        let span = tv.node.id.span.clone();
        if let Some(spans) = spans_by_name.get_mut(name) {
            spans.push(span);
        } else {
            spans_by_name.insert(name, &vec![span]);
        }
    }
    for (name, spans) in spans_by_name.iter() {
        if spans.len() > 1 {
            errors.push(duplicate_typevar(name, spans));
        }
    }

    // 2. Check kind references resolve to declared typevars of the correct kind
    let declared: Ctx<Tid, &Kind<Size>> = typevars
        .iter()
        .map(|tv| (tv.node.id.node.clone(), &tv.node.kind))
        .collect();

    for tv in typevars {
        check_kind_refs(&tv.node, &declared, &typevar_span, is_empty, &mut errors);
    }

    // 3. Check for circular references among typevar kinds
    check_kind_cycles(typevars, &mut errors);

    // 4. Check range bounds for Range kinds
    for tv in typevars {
        if let Kind::Range(r) = &tv.node.kind {
            // Only check literal bounds here. Symbolic sizes (e.g. `N: 0..M`
            // where M is another typevar) cannot be compared until size
            // resolution, which happens later during concretization.
            let end_node = r.end.as_ref().map(|e| &e.node).unwrap_or(&r.start.node);
            if let (Size::Lit(start), Size::Lit(end)) = (&r.start.node, end_node)
                && start > end
            {
                errors.push(
                    InvalidRangeBounds {
                        span: tv.span.clone(),
                        name: tv.node.id.node.clone(),
                        start: start.to_string(),
                        end: end.to_string(),
                    }
                    .build(),
                );
            }
        }
    }

    errors
}

/// Check that group references in a kind resolve to declared typevars
/// of the correct kind. Groups refs by name so that `Pairing<F, F>` emits
/// one error (with multiple spans) instead of two identical errors.
fn check_kind_refs(
    tv: &TypeVar<Size>,
    declared: &Ctx<Tid, &Kind<Size>>,
    typevar_span: &Range<usize>,
    is_empty: bool,
    errors: &mut Vec<Diagnostic>,
) {
    // Collect all group refs from the kind, grouped by name.
    let mut refs_by_name: Ctx<Tid, Vec<Range<usize>>> = Ctx::new();
    for g in kind_group_refs_spanned(&tv.kind) {
        if let Some(spans) = refs_by_name.get_mut(&g.node) {
            spans.push(g.span.clone());
        } else {
            refs_by_name.insert(&g.node, &vec![g.span.clone()]);
        }
    }

    for (ref_name, ref_spans) in refs_by_name.iter() {
        if let Some(kind) = declared.get(ref_name) {
            if !kind.is_group() {
                errors.push(invalid_group_ref(
                    ref_name,
                    ref_spans,
                    &tv.id.node,
                    &format!("a {kind}"),
                ));
            }
        } else {
            errors.push(unresolved_group_ref(
                ref_name,
                ref_spans,
                typevar_span,
                is_empty,
            ));
        }
    }
}

/// Get all group references (as Spanned<Tid>) from a kind.
fn kind_group_refs_spanned(kind: &Kind<Size>) -> Vec<&Spanned<Tid>> {
    match kind {
        Kind::Scalar(groups) => groups.iter().collect(),
        Kind::Pairing(a, b) => vec![a, b],
        _ => vec![],
    }
}

// ── Cycle detection ─────────────────────────────────────────────────────

/// Detect circular references among typevar kinds.
///
/// A cycle occurs when typevar kinds reference each other in a loop, e.g.
/// `V: Pairing<G>` and `G: Pairing<V>`. We build a dependency graph where
/// each typevar depends on the group references in its kind, then run DFS
/// to find cycles.
fn check_kind_cycles(typevars: &[Spanned<TypeVar<Size>>], errors: &mut Vec<Diagnostic>) {
    // Build dependency graph: typevar name → list of (referenced name, ref span)
    let mut deps: Ctx<Tid, Vec<(Tid, Range<usize>)>> = Ctx::new();
    let mut kind_strs: Ctx<Tid, String> = Ctx::new();
    for tv in typevars {
        let name = tv.node.id.node.clone();
        let refs = kind_group_refs(&tv.node.kind);
        deps.insert(&name, &refs);
        kind_strs.insert(&name, &tv.node.kind.to_string());
    }

    // DFS cycle detection
    let mut visited: HashSet<Tid> = HashSet::new();
    let mut visiting: Vec<Tid> = Vec::new();
    // Track reported cycles (by sorted member set) to avoid duplicates.
    let mut reported: HashSet<BTreeSet<Tid>> = HashSet::new();

    for name in deps.keys() {
        if !visited.contains(&name) {
            dfs_cycle(
                &name,
                &deps,
                &kind_strs,
                &mut visiting,
                &mut visited,
                &mut reported,
                errors,
            );
        }
    }
}

/// Get all group references (name + span) from a kind.
fn kind_group_refs(kind: &Kind<Size>) -> Vec<(Tid, Range<usize>)> {
    match kind {
        Kind::Scalar(groups) => groups
            .iter()
            .map(|g| (g.node.clone(), g.span.clone()))
            .collect(),
        Kind::Pairing(a, b) => vec![
            (a.node.clone(), a.span.clone()),
            (b.node.clone(), b.span.clone()),
        ],
        _ => vec![],
    }
}

/// DFS traversal for cycle detection.
/// `visiting` is the current path stack; `visited` is the global visited set.
/// `reported` tracks sorted member sets of already-reported cycles to avoid
/// duplicate errors when a typevar has multiple edges into the same cycle.
fn dfs_cycle(
    name: &Tid,
    deps: &Ctx<Tid, Vec<(Tid, Range<usize>)>>,
    kind_strs: &Ctx<Tid, String>,
    visiting: &mut Vec<Tid>,
    visited: &mut HashSet<Tid>,
    reported: &mut HashSet<BTreeSet<Tid>>,
    errors: &mut Vec<Diagnostic>,
) {
    if visited.contains(name) {
        return;
    }

    visiting.push(name.clone());

    // Visit dependencies
    if let Some(refs) = deps.get(name) {
        for (dep, _) in refs {
            if visited.contains(dep) {
                continue;
            }
            if let Some(pos) = visiting.iter().position(|n| n == dep) {
                // Found a cycle: the path from `pos` to the end.
                let cycle_tids: Vec<Tid> = visiting[pos..].to_vec();
                // Deduplicate by sorted member set.
                let key: BTreeSet<Tid> = cycle_tids.iter().cloned().collect();
                if reported.contains(&key) {
                    continue;
                }
                reported.insert(key);
                let cycle: Vec<(Tid, Range<usize>)> = cycle_tids
                    .iter()
                    .enumerate()
                    .map(|(i, tid)| {
                        let next = &cycle_tids[(i + 1) % cycle_tids.len()];
                        let span = deps
                            .get(tid)
                            .and_then(|refs| refs.iter().find(|(r, _)| r == next))
                            .map(|(_, s)| s.clone())
                            .expect("cycle member must reference the next member");
                        (tid.clone(), span)
                    })
                    .collect();
                let kinds: Vec<(Tid, String)> = cycle_tids
                    .iter()
                    .filter_map(|tid| kind_strs.get(tid).map(|k| (tid.clone(), k.clone())))
                    .collect();
                errors.push(circular_typevar_ref(cycle, kinds));
            } else {
                dfs_cycle(dep, deps, kind_strs, visiting, visited, reported, errors);
            }
        }
    }

    visiting.pop();
    visited.insert(name.clone());
}
