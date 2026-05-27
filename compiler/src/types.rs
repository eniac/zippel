//! Rust type rendering for typed Graph IR values.

use backend::{ABase, ATyp};

use crate::error::Result;
use crate::options::CodegenOptions;

/// Render a Graph IR type into a Rust type string using default node context.
#[allow(dead_code)]
pub(crate) fn render_type(typ: &ATyp, options: &CodegenOptions) -> Result<String> {
    render_type_at_node(typ, options, 0)
}

/// Render a Graph IR type into a Rust type string, attaching `node` to any
/// error for diagnostics.
#[allow(dead_code)]
#[allow(clippy::only_used_in_recursion)]
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
        ATyp::Base(ABase::Fin(_)) => Ok("usize".to_string()),
        ATyp::Vec(inner, _len) => {
            // Graph IR vectors carry a fixed compile-time length, but we
            // render them as heap-allocated `Vec<T>` for now.  A future pass
            // can switch to `[T; N]` once const-generic array generation is
            // supported.
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
        ATyp::Uni(_) | ATyp::VPoly(_, _) => {
            // Generated Rust currently represents univariate polynomial-shaped
            // intermediates as coefficient vectors.  This is sufficient for
            // the KZG codegen milestone; richer polynomial wrappers can be
            // introduced when more polynomial operations are emitted.
            Ok(format!("Vec<{}>", options.target.scalar_type))
        }
        ATyp::Mle(_) => Ok(format!("GeneratedMle<{}>", options.target.scalar_type)),
    }
}

#[cfg(test)]
mod tests {
    use backend::{ABase, ATyp};
    use lang::typ::CRange;
    use share::Ctx;

    use super::{render_type, render_type_at_node};
    use crate::options::CodegenOptions;

    fn opts() -> CodegenOptions {
        CodegenOptions::prover()
    }

    #[test]
    fn maps_bls12_381_base_types() {
        let opts = opts();

        assert_eq!(
            render_type(&ATyp::Base(ABase::Scalar), &opts).unwrap(),
            "ark_bls12_381::Fr"
        );
        assert_eq!(
            render_type(&ATyp::Base(ABase::G1), &opts).unwrap(),
            "ark_bls12_381::G1Projective"
        );
        assert_eq!(
            render_type(&ATyp::Base(ABase::G2), &opts).unwrap(),
            "ark_bls12_381::G2Projective"
        );
        assert_eq!(
            render_type(&ATyp::Base(ABase::GT), &opts).unwrap(),
            "ark_ec::pairing::PairingOutput<ark_bls12_381::Bls12_381>"
        );
        assert_eq!(
            render_type(&ATyp::Base(ABase::Bool), &opts).unwrap(),
            "bool"
        );
    }

    #[test]
    fn maps_vectors_and_records_without_value() {
        let opts = opts();

        let vec_typ = ATyp::Vec(Box::new(ATyp::Base(ABase::Scalar)), 3);
        assert_eq!(
            render_type(&vec_typ, &opts).unwrap(),
            "Vec<ark_bls12_381::Fr>"
        );

        let mut fields: Ctx<String, ATyp> = Ctx::new();
        fields.insert(&"ok".to_string(), &ATyp::Base(ABase::Bool));
        fields.insert(&"s".to_string(), &ATyp::Base(ABase::Scalar));
        let record_typ = ATyp::Record(fields);
        assert_eq!(
            render_type(&record_typ, &opts).unwrap(),
            "(bool, ark_bls12_381::Fr)"
        );
    }

    #[test]
    fn record_iteration_is_key_sorted_not_insertion_order() {
        let opts = opts();

        let mut fields: Ctx<String, ATyp> = Ctx::new();
        fields.insert(&"z".to_string(), &ATyp::Base(ABase::Bool));
        fields.insert(&"a".to_string(), &ATyp::Base(ABase::Scalar));
        let record_typ = ATyp::Record(fields);
        assert_eq!(
            render_type(&record_typ, &opts).unwrap(),
            "(ark_bls12_381::Fr, bool)"
        );
    }

    #[test]
    fn record_empty_renders_unit_tuple() {
        let opts = opts();
        let empty: Ctx<String, ATyp> = Ctx::new();
        assert_eq!(render_type(&ATyp::Record(empty), &opts).unwrap(), "()");
    }

    #[test]
    fn record_single_field_renders_one_element_tuple() {
        let opts = opts();
        let mut fields: Ctx<String, ATyp> = Ctx::new();
        fields.insert(&"x".to_string(), &ATyp::Base(ABase::Scalar));
        assert_eq!(
            render_type(&ATyp::Record(fields), &opts).unwrap(),
            "(ark_bls12_381::Fr,)"
        );
    }

    #[test]
    fn maps_nested_vec_of_records() {
        let opts = opts();

        let mut fields: Ctx<String, ATyp> = Ctx::new();
        fields.insert(&"b".to_string(), &ATyp::Base(ABase::Bool));
        fields.insert(&"s".to_string(), &ATyp::Base(ABase::Scalar));
        let record_typ = ATyp::Record(fields);
        let nested = ATyp::Vec(Box::new(record_typ), 2);
        assert_eq!(
            render_type(&nested, &opts).unwrap(),
            "Vec<(bool, ark_bls12_381::Fr)>"
        );
    }

    #[test]
    fn maps_fin_to_usize_for_index_codegen() {
        let opts = opts();
        let fin_typ = ATyp::Base(ABase::Fin(CRange::new(0, 4)));
        assert_eq!(render_type(&fin_typ, &opts).unwrap(), "usize");
    }

    #[test]
    fn maps_univariate_polynomial_types_to_scalar_vectors() {
        let opts = opts();

        for typ in [ATyp::Uni(4), ATyp::VPoly(1, 3)] {
            assert_eq!(render_type(&typ, &opts).unwrap(), "Vec<ark_bls12_381::Fr>");
        }
    }

    #[test]
    fn maps_mle_to_generated_dense_mle_type() {
        let opts = opts();
        assert_eq!(
            render_type(&ATyp::Mle(3), &opts).unwrap(),
            "GeneratedMle<ark_bls12_381::Fr>"
        );
    }

    #[test]
    fn records_can_contain_fin_and_mle_fields() {
        let opts = opts();
        let mut fields: Ctx<String, ATyp> = Ctx::new();
        fields.insert(
            &"index".to_string(),
            &ATyp::Base(ABase::Fin(CRange::new(0, 4))),
        );
        fields.insert(&"poly".to_string(), &ATyp::Mle(3));

        assert_eq!(
            render_type_at_node(&ATyp::Record(fields), &opts, 42).unwrap(),
            "(usize, GeneratedMle<ark_bls12_381::Fr>)"
        );
    }

    #[test]
    fn verifier_options_render_same_base_types() {
        let prover_opts = CodegenOptions::prover();
        let verifier_opts = CodegenOptions::verifier();

        for typ in [ATyp::Base(ABase::Scalar), ATyp::Base(ABase::G1)] {
            assert_eq!(
                render_type(&typ, &prover_opts).unwrap(),
                render_type(&typ, &verifier_opts).unwrap(),
                "prover and verifier must render {typ:?} identically"
            );
        }
    }

    #[test]
    fn maps_vec_of_vec_scalar() {
        let opts = opts();
        let inner = ATyp::Vec(Box::new(ATyp::Base(ABase::Scalar)), 4);
        let outer = ATyp::Vec(Box::new(inner), 3);
        assert_eq!(
            render_type(&outer, &opts).unwrap(),
            "Vec<Vec<ark_bls12_381::Fr>>"
        );
    }
}
