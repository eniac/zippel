//! Rust expression lowering from typed Graph IR operations.

use lang::ast::BinOp;

use crate::error::{CompilerError, Result};

/// Lower a binary Graph IR operation to a Rust infix expression string.
///
/// Returns `CompilerError::UnsupportedOp` for operations without a direct
/// Rust infix equivalent at the supported types.
pub(crate) fn lower_bin(node: usize, op: BinOp, left: &str, right: &str) -> Result<String> {
    match op {
        BinOp::Add => Ok(format!("{left} + {right}")),
        BinOp::Sub => Ok(format!("{left} - {right}")),
        BinOp::Mul => Ok(format!("{left} * {right}")),
        BinOp::Equ => Ok(format!("{left} == {right}")),
        BinOp::And => Ok(format!("{left} && {right}")),
        other => Err(CompilerError::UnsupportedOp {
            node,
            op: format!("{other:?}"),
        }),
    }
}

/// Return a Rust code snippet that builds `instance_bytes: Vec<u8>` from the
/// Schnorr public arguments `g` and `h`.
///
/// The snippet is ready to be embedded verbatim into a generated function body.
/// It uses the `serialize_to_bytes` helper emitted by [`crate::transcript`].
pub(crate) fn schnorr_instance_bytes() -> &'static str {
    "    let mut instance_bytes = Vec::new();\n    instance_bytes.extend(serialize_to_bytes(&g)?);\n    instance_bytes.extend(serialize_to_bytes(&h)?);\n"
}
