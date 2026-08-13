//! Typevar validator — checks type variable declarations for correctness.
//!
//! Validates:
//! - No duplicate typevar names in one declaration
//! - Group references in Pairing/Scalar kinds resolve to declared typevars
//! - Range bounds are valid (start <= end)
//! - No circular references among typevar kinds

use std::ops::Range;

use crate::ast::size::Size;
use crate::ast::spanned::Spanned;
use crate::ast::Sig;
use crate::id::Tid;
use crate::typ::Kind;
use crate::typ::TypeVar;
use share::Ctx;

use super::{KindError, SemanticError};

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

    // 2. Check kind references resolve to declared typevars
    // Build a map of declared typevar names → their kinds
    let declared: Ctx<Tid, &Kind<Size>> = typevars
        .iter()
        .map(|tv| (tv.node.id.node.clone(), &tv.node.kind))
        .collect();

    for tv in typevars {
        check_kind_refs(&tv.node, &declared, &mut errors);
    }

    // 3. Check range bounds for Range kinds
    for tv in typevars {
        if let Kind::Range(r) = &tv.node.kind {
            // For symbolic sizes, we can only check literal bounds
            let end_node = r.end.as_ref().map(|e| &e.node).unwrap_or(&r.start.node);
            if let (Size::Lit(start), Size::Lit(end)) = (&r.start.node, end_node) {
                if start > end {
                    errors.push(SemanticError::InvalidRangeBounds {
                        name: tv.node.id.node.clone(),
                        span: tv.span.clone(),
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
                check_group_ref(g, declared, &tv.id, errors);
            }
        }
        Kind::Pairing(a, b) => {
            check_group_ref(a, declared, &tv.id, errors);
            check_group_ref(b, declared, &tv.id, errors);
        }
        Kind::Field | Kind::Group | Kind::Range(_) | Kind::SizeVar => {}
    }
}

/// Check a single group reference resolves to a declared Group typevar.
fn check_group_ref(
    g: &Tid,
    declared: &Ctx<Tid, &Kind<Size>>,
    tv_id: &Spanned<Tid>,
    errors: &mut Vec<SemanticError>,
) {
    if let Some(kind) = declared.get(g) {
        if !kind.is_group() {
            errors.push(SemanticError::InvalidTypevarKind {
                name: tv_id.node.clone(),
                span: tv_id.span.clone(),
                reason: KindError::NotAGroup,
            });
        }
    } else {
        errors.push(SemanticError::UnresolvedGroupRef {
            name: g.clone(),
            ref_span: tv_id.span.clone(),
            reason: KindError::GroupNotDeclared,
        });
    }
}
