//! Tests that lower Zippel source or hand-built graphs and execute them
//! through `eval_op`, checking the lowering against the operators' semantics.
mod algebraic_properties;
mod cross_type_properties;
pub mod helpers;
mod op_tests;
mod polynomial_laws;
mod reduce_map_tests;
