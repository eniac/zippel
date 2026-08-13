//! Typevar validator — checks type variable declarations for correctness.
//!
//! Validates:
//! - No duplicate typevar names in one declaration
//! - Group references in Pairing/Scalar kinds resolve to declared typevars
//! - Range bounds are valid (start <= end)
//! - No circular references among typevar kinds

use std::collections::HashSet;
use std::ops::Range;

use crate::ast::size::Size;
use crate::ast::spanned::Spanned;
use crate::ast::Sig;
use crate::id::Tid;
use crate::typ::{Kind, TypeVar};
use share::Ctx;

use super::SemanticError;

/// Check type variable declarations in a signature.
pub fn check_typevars(sig: &Sig<Size>) -> Vec<SemanticError> {
    let mut errors = Vec::new();
    let typevars = &sig.typevars.node.0;

    // 1. Check for duplicate typevar names
    let mut seen: Ctx<Tid, Range<usize>> = Ctx::new();
    for tv in typevars {
        if let Some(first_span) = seen.get(&tv.node.id.node) {
            errors.push(SemanticError::DuplicateTypevar {
                name: tv.node.id.node.clone(),
                first_span: first_span.clone(),
                second_span: tv.node.id.span.clone(),
            });
        } else {
            seen.insert(&tv.node.id.node, &tv.node.id.span.clone());
        }
    }

    // 2. Check kind references resolve to declared typevars of the correct kind
    let declared: Ctx<Tid, &Kind<Size>> = typevars
        .iter()
        .map(|tv| (tv.node.id.node.clone(), &tv.node.kind))
        .collect();

    for tv in typevars {
        check_kind_refs(&tv.node, &declared, &mut errors);
    }

    // 3. Check for circular references among typevar kinds
    check_kind_cycles(typevars, &mut errors);

    // 4. Check range bounds for Range kinds
    for tv in typevars {
        if let Kind::Range(r) = &tv.node.kind {
            // For symbolic sizes, we can only check literal bounds
            let end_node = r.end.as_ref().map(|e| &e.node).unwrap_or(&r.start.node);
            if let (Size::Lit(start), Size::Lit(end)) = (&r.start.node, end_node) {
                if start > end {
                    errors.push(SemanticError::InvalidRangeBounds {
                        name: tv.node.id.node.clone(),
                        span: tv.span.clone(),
                        start: start.to_string(),
                        end: end.to_string(),
                    });
                }
            }
        }
    }

    errors
}

/// Check that group references in a kind resolve to declared typevars
/// of the correct kind.
fn check_kind_refs(
    tv: &TypeVar<Size>,
    declared: &Ctx<Tid, &Kind<Size>>,
    errors: &mut Vec<SemanticError>,
) {
    match &tv.kind {
        Kind::Scalar(groups) => {
            for g in groups.iter() {
                check_group_ref(g, &tv.id.node, declared, errors);
            }
        }
        Kind::Pairing(a, b) => {
            check_group_ref(a, &tv.id.node, declared, errors);
            check_group_ref(b, &tv.id.node, declared, errors);
        }
        Kind::Field | Kind::Group | Kind::Range(_) | Kind::SizeVar => {}
    }
}

/// Check a single group reference resolves to a declared Group typevar.
/// `group_ref` is the group reference (e.g. the `F` in `Pairing<F, G>`),
/// `tv_name` is the typevar whose kind contains the reference.
fn check_group_ref(
    group_ref: &Spanned<Tid>,
    tv_name: &Tid,
    declared: &Ctx<Tid, &Kind<Size>>,
    errors: &mut Vec<SemanticError>,
) {
    if let Some(kind) = declared.get(&group_ref.node) {
        if !kind.is_group() {
            errors.push(SemanticError::InvalidGroupRef {
                ref_name: group_ref.node.clone(),
                ref_span: group_ref.span.clone(),
                tv_name: tv_name.clone(),
                actual_kind: kind_description(kind),
            });
        }
    } else {
        errors.push(SemanticError::UnresolvedGroupRef {
            name: group_ref.node.clone(),
            ref_span: group_ref.span.clone(),
        });
    }
}

/// Human-readable description of a kind for error messages.
fn kind_description(kind: &Kind<Size>) -> String {
    match kind {
        Kind::Field => "a Field".to_string(),
        Kind::Group => "a Group".to_string(),
        Kind::Scalar(_) => "a Scalar".to_string(),
        Kind::Pairing(_, _) => "a Pairing".to_string(),
        Kind::Range(_) => "a Range".to_string(),
        Kind::SizeVar => "a Size".to_string(),
    }
}

// ── Cycle detection ─────────────────────────────────────────────────────

/// Detect circular references among typevar kinds.
///
/// A cycle occurs when typevar kinds reference each other in a loop, e.g.
/// `V: Pairing<G>` and `G: Pairing<V>`. We build a dependency graph where
/// each typevar depends on the group references in its kind, then run DFS
/// to find cycles.
fn check_kind_cycles(typevars: &[Spanned<TypeVar<Size>>], errors: &mut Vec<SemanticError>) {
    // Build dependency graph: typevar name → list of (referenced name, ref span)
    #[allow(clippy::type_complexity)]
    let mut deps: Vec<(Tid, Vec<(Tid, Range<usize>)>)> = Vec::new();

    for tv in typevars {
        let name = tv.node.id.node.clone();
        let refs = kind_group_refs(&tv.node.kind);
        deps.push((name, refs));
    }

    // DFS cycle detection
    let mut visited: HashSet<Tid> = HashSet::new();
    let mut visiting: Vec<Tid> = Vec::new();
    // Track reported cycles (by sorted member set) to avoid duplicates.
    let mut reported: HashSet<Vec<Tid>> = HashSet::new();

    for (name, _) in &deps {
        if !visited.contains(name) {
            dfs_cycle(
                name,
                &deps,
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
#[allow(clippy::type_complexity)]
fn dfs_cycle(
    name: &Tid,
    deps: &[(Tid, Vec<(Tid, Range<usize>)>)],
    visiting: &mut Vec<Tid>,
    visited: &mut HashSet<Tid>,
    reported: &mut HashSet<Vec<Tid>>,
    errors: &mut Vec<SemanticError>,
) {
    if visited.contains(name) {
        return;
    }

    visiting.push(name.clone());

    // Visit dependencies
    if let Some((_, refs)) = deps.iter().find(|(n, _)| n == name) {
        for (dep, _) in refs {
            if visited.contains(dep) {
                continue;
            }
            if let Some(pos) = visiting.iter().position(|n| n == dep) {
                // Found a cycle: the path from `pos` to the end.
                let cycle_tids: Vec<Tid> = visiting[pos..].to_vec();
                // Deduplicate by sorted member set.
                let mut key = cycle_tids.clone();
                key.sort();
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
                            .iter()
                            .find(|(n, _)| n == tid)
                            .and_then(|(_, refs)| refs.iter().find(|(r, _)| r == next))
                            .map(|(_, s)| s.clone())
                            .unwrap_or(0..0);
                        (tid.clone(), span)
                    })
                    .collect();
                errors.push(SemanticError::CircularTypevarRef { cycle });
            } else {
                dfs_cycle(dep, deps, visiting, visited, reported, errors);
            }
        }
    }

    visiting.pop();
    visited.insert(name.clone());
}
