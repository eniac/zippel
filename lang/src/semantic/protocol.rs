//! A protocol to run must concretize to one instance.

use crate::ast::decl::DeclError;
use crate::ast::module::{ExpandedRange, ModuleError};
use crate::ast::{CModule, UModule};
use crate::id::{Tid, Vid};
use crate::typ::{Kind, SizeSubsts};
use share::Ctx;

/// Checks that protocol `name` concretized to one instance in `cmodule`,
/// `module` concretized with `sizes`. Each range-kinded type variable
/// gives one instance per value it admits; a caller that runs one
/// protocol would otherwise run one of them without saying which.
///
/// # Errors
/// [`ModuleError::AmbiguousProtocol`] if it concretized to more than one
/// instance, with each range that took more than one value.
pub fn check_protocol_instances(
    module: &UModule,
    cmodule: &CModule,
    name: &Vid,
    sizes: &Ctx<Tid, usize>,
) -> Result<(), ModuleError> {
    let instances = cmodule
        .iter()
        .filter(|(sig, body)| body.is_proto() && sig.name.node == *name)
        .count();
    if instances <= 1 {
        return Ok(());
    }
    let Some((sig, _)) = module
        .iter()
        .find(|(sig, body)| body.is_proto() && sig.name.node == *name)
    else {
        return Err(ModuleError::DeclarationNotFound(name.to_string()));
    };
    let substs = SizeSubsts::from_typevars(&sig.typevars.node, sizes).map_err(|e| {
        ModuleError::DeclarationError(sig.name.span.clone(), DeclError::SubstError(e))
    })?;
    let ranges = sig
        .typevars
        .node
        .0
        .iter()
        .filter_map(|tv| {
            let Kind::Range(range) = &tv.node.kind else {
                return None;
            };
            let values: Vec<usize> = substs
                .iter()
                .filter_map(|s| s.get(&tv.node.id.node).copied())
                .collect::<std::collections::BTreeSet<_>>()
                .into_iter()
                .collect();
            (values.len() > 1).then(|| ExpandedRange {
                var: tv.node.id.clone(),
                range: range.to_string(),
                values,
            })
        })
        .collect();
    Err(ModuleError::AmbiguousProtocol {
        name: sig.name.clone(),
        ranges,
        instances,
    })
}
