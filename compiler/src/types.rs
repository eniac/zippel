//! Rust type rendering for typed Graph IR values.

use backend::{ABase, ATyp};

use crate::error::{CompilerError, Result};
use crate::options::CodegenOptions;

/// Render a Graph IR type into a Rust type string using default node context.
#[allow(dead_code)]
pub(crate) fn render_type(typ: &ATyp, options: &CodegenOptions) -> Result<String> {
    render_type_at_node(typ, options, 0)
}

/// Render a Graph IR type into a Rust type string, attaching `node` to any
/// error for diagnostics.
#[allow(dead_code)]
pub(crate) fn render_type_at_node(
    typ: &ATyp,
    options: &CodegenOptions,
    node: usize,
) -> Result<String> {
    match typ {
        ATyp::Base(ABase::Scalar) => Ok(options.target.scalar_type.to_string()),
        ATyp::Base(ABase::G1) => Ok(options.target.g1_type.to_string()),
        ATyp::Base(ABase::G2) => Ok(options.target.g2_type.to_string()),
        ATyp::Base(ABase::GT) => Ok(format!(
            "ark_ec::pairing::PairingOutput<{}>",
            options.target.pairing_type
        )),
        ATyp::Base(ABase::Bool) => Ok("bool".to_string()),
        ATyp::Base(ABase::Fin(_)) => Err(CompilerError::UnsupportedType {
            node,
            typ: format!("{typ:?}"),
        }),
        ATyp::Vec(inner, _) => {
            let inner_str = render_type_at_node(inner, options, node)?;
            Ok(format!("Vec<{inner_str}>"))
        }
        ATyp::Record(fields) => {
            let parts: Result<Vec<String>> = fields
                .iter()
                .map(|(_, v)| render_type_at_node(v, options, node))
                .collect();
            let parts = parts?;
            // Rust tuple syntax requires a trailing comma for exactly one element
            // so that `(T,)` is a tuple rather than the parenthesised expression `(T)`.
            Ok(match parts.len() {
                0 => "()".to_string(),
                1 => format!("({},)", parts[0]),
                _ => format!("({})", parts.join(", ")),
            })
        }
        ATyp::Uni(_) | ATyp::Mle(_) | ATyp::VPoly(_, _) => Err(CompilerError::UnsupportedType {
            node,
            typ: format!("{typ:?}"),
        }),
    }
}
