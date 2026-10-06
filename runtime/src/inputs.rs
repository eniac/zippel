//! A protocol's named inputs.

use backend::{ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;
use std::collections::HashMap;
use std::sync::Arc;

/// A protocol's inputs, by argument name.
///
/// Values are shared (`Arc`), so running a protocol, or running it many
/// times, never copies an input: a run holds clones of the `Arc`s, and the
/// caller keeps its own. Build one once and reuse it.
pub struct Inputs<C: ArkConfig>(HashMap<Vid, Arc<Value<C>>>);

impl<C: ArkConfig> Inputs<C> {
    /// No inputs.
    #[must_use]
    pub fn new() -> Self {
        Inputs(HashMap::new())
    }

    /// Binds `name` to `value`, moving a `Value` in (or sharing an `Arc`).
    pub fn insert(&mut self, name: impl Into<Vid>, value: impl Into<Arc<Value<C>>>) {
        self.0.insert(name.into(), value.into());
    }

    /// The value bound to `name`.
    #[must_use]
    pub fn get(&self, name: &Vid) -> Option<&Arc<Value<C>>> {
        self.0.get(name)
    }

    /// The bound names, in no particular order.
    pub fn names(&self) -> impl Iterator<Item = &Vid> {
        self.0.keys()
    }
}

impl<C: ArkConfig> Default for Inputs<C> {
    fn default() -> Self {
        Self::new()
    }
}

/// Clones the `Arc`s, not the values.
impl<C: ArkConfig> Clone for Inputs<C> {
    fn clone(&self) -> Self {
        Inputs(self.0.clone())
    }
}

impl<C, N, V> FromIterator<(N, V)> for Inputs<C>
where
    C: ArkConfig,
    N: Into<Vid>,
    V: Into<Arc<Value<C>>>,
{
    fn from_iter<I: IntoIterator<Item = (N, V)>>(iter: I) -> Self {
        Inputs(
            iter.into_iter()
                .map(|(name, value)| (name.into(), value.into()))
                .collect(),
        )
    }
}

/// Copies each value once: a `Ctx` cannot give up its values. Fine for
/// small inputs; build large ones as `Inputs` directly.
impl<C: ArkConfig> From<Ctx<Vid, Value<C>>> for Inputs<C> {
    fn from(ctx: Ctx<Vid, Value<C>>) -> Self {
        ctx.into_iter().collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use backend::ArkBls12_381;

    type I = Inputs<ArkBls12_381>;

    #[test]
    fn clones_share_values() {
        let inputs: I = [("v", Value::VecScalar(vec![Default::default(); 4]))]
            .into_iter()
            .collect();
        let copy = inputs.clone();
        let name = Vid::from("v");
        assert!(Arc::ptr_eq(
            inputs.get(&name).unwrap(),
            copy.get(&name).unwrap()
        ));
    }

    #[test]
    fn insert_shares_a_given_arc() {
        let value = Arc::new(Value::Unit);
        let mut inputs = I::new();
        inputs.insert("u", Arc::clone(&value));
        assert!(Arc::ptr_eq(inputs.get(&Vid::from("u")).unwrap(), &value));
        assert_eq!(inputs.names().collect::<Vec<_>>(), [&Vid::from("u")]);
    }
}
