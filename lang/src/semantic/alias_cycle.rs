//! Type alias cycle detection — `type A = B; type B = A;` is invalid.

use std::collections::HashSet;

use crate::ast::decl::UDecl;
use crate::ast::spanned::Spanned;
use crate::diagnostic::{Diagnostic, Phase};
use crate::id::Tid;
use crate::typ::{Typ, UTyp};
use share::Ctx;

/// E0011: A type alias cycle (e.g. `type A = B; type B = A;`).
/// Uses the builder API because the cycle produces a variable number of
/// secondary labels. The redundant `aliases` note from the old design has
/// been removed (Rev G) — the secondary labels already show each alias's
/// role in the cycle.
fn type_alias_cycle(cycle: Vec<(Tid, std::ops::Range<usize>)>) -> Diagnostic {
    let (cycle_str, primary_span, secondary_labels) =
        super::render_cycle(&cycle, "aliases the next type in the cycle");

    Diagnostic::error(Phase::Semantic, primary_span, "circular type alias")
        .code("E0011")
        .primary_label(&format!("cycle: {cycle_str}"))
        .secondary_labels(secondary_labels)
}

/// Check for type alias cycles.
pub fn check_type_alias_cycles(decls: &[Spanned<UDecl>]) -> Vec<Diagnostic> {
    // Collect type aliases: name → (aliased type, span)
    let mut type_ctx: Ctx<Tid, (UTyp, std::ops::Range<usize>)> = Ctx::new();
    for d in decls {
        if d.node.body.is_type_alias() {
            if let Some(ret) = &d.node.sig.ret {
                type_ctx.insert(
                    &Tid::from(d.node.sig.name.node.0.as_str()),
                    &(ret.node.clone(), ret.span.clone()),
                );
            }
        }
    }

    let mut errors = Vec::new();
    let mut visited: HashSet<Tid> = HashSet::new();

    for name in type_ctx.keys() {
        if visited.contains(&name) {
            continue;
        }
        // DFS with a path stack to capture the cycle when found.
        let mut path: Vec<Tid> = Vec::new();
        if let Some(cycle) = detect_cycle(&name, &type_ctx, &mut path, &mut visited) {
            // Pair each alias name with the span of its aliased type.
            let cycle_with_spans: Vec<(Tid, std::ops::Range<usize>)> = cycle
                .iter()
                .map(|t| {
                    let span = type_ctx
                        .get(t)
                        .map(|(_, s)| s.clone())
                        .expect("cycle member must have an aliased type");
                    (t.clone(), span)
                })
                .collect();
            errors.push(type_alias_cycle(cycle_with_spans));
        }
    }

    errors
}

/// DFS from `node`, returning the cycle path if one is found.
///
/// `path` is the current DFS stack (for cycle reconstruction).
/// `visited` tracks nodes fully explored across all DFS roots.
fn detect_cycle(
    node: &Tid,
    type_ctx: &Ctx<Tid, (UTyp, std::ops::Range<usize>)>,
    path: &mut Vec<Tid>,
    visited: &mut HashSet<Tid>,
) -> Option<Vec<Tid>> {
    // Cycle: node is already on the current DFS path.
    if let Some(pos) = path.iter().position(|n| n == node) {
        return Some(path[pos..].to_vec());
    }
    // Already fully explored from a previous DFS root.
    if visited.contains(node) {
        return None;
    }

    path.push(node.clone());
    visited.insert(node.clone());

    if let Some((typ, _)) = type_ctx.get(node) {
        for dep in type_dependencies(typ) {
            if type_ctx.contains(&dep) {
                if let Some(cycle) = detect_cycle(&dep, type_ctx, path, visited) {
                    return Some(cycle);
                }
            }
        }
    }

    path.pop();
    None
}

/// Extract type alias dependencies from a type (which Tids it references).
fn type_dependencies(typ: &UTyp) -> share::Set<Tid> {
    let mut deps = share::Set::new();
    collect_deps(typ, &mut deps);
    deps
}

fn collect_deps(typ: &UTyp, deps: &mut share::Set<Tid>) {
    match typ {
        Typ::Base(t) | Typ::Poly(t, _, _) => {
            deps.insert(t.clone());
        }
        Typ::Vec(box_typ, _) => collect_deps(box_typ, deps),
        Typ::Record(ctx) => {
            for (_, t) in ctx.iter() {
                collect_deps(t, deps);
            }
        }
        Typ::Fin(_) | Typ::Unit => {}
    }
}
