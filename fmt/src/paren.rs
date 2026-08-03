//! Parenthesization decisions for the formatter.
//!
//! Uses `BinOp::parser_precedence()` (which matches the chumsky pratt table)
//! to decide when child expressions need parentheses.

use lang::ast::BinOp;
use lang::ast::Exp;

/// Does the lhs of a binary op need parentheses?
pub fn lhs_needs_paren(op: BinOp, lhs: &Exp<lang::ast::Size>) -> bool {
    // Neg has prefix precedence 0 (lowest), so it always needs parens
    // when it's a child of a Bin — otherwise `-x * y` would re-parse as
    // `-(x * y)` instead of `(-x) * y`.
    if matches!(lhs, Exp::Neg(_)) {
        return true;
    }
    let parent_prec = op.parser_precedence();
    let right_assoc = op.is_right_assoc();
    matches!(lhs, Exp::Bin(child_op, _, _)
        if child_op.parser_precedence() < parent_prec
            || (child_op.parser_precedence() == parent_prec && right_assoc))
}

/// Does the rhs of a binary op need parentheses?
pub fn rhs_needs_paren(op: BinOp, rhs: &Exp<lang::ast::Size>) -> bool {
    // Same as lhs: Neg at precedence 0 needs parens inside any Bin.
    if matches!(rhs, Exp::Neg(_)) {
        return true;
    }
    let parent_prec = op.parser_precedence();
    let right_assoc = op.is_right_assoc();
    matches!(rhs, Exp::Bin(child_op, _, _)
        if child_op.parser_precedence() < parent_prec
            || (child_op.parser_precedence() == parent_prec && !right_assoc))
}
