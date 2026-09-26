//! Helpers shared by the `Display` impls of the AST and types.

use std::fmt;

/// Writes `items` separated by `sep`.
pub(crate) fn sep<T: fmt::Display>(
    f: &mut fmt::Formatter<'_>,
    items: impl IntoIterator<Item = T>,
    sep: &str,
) -> fmt::Result {
    for (i, item) in items.into_iter().enumerate() {
        if i > 0 {
            f.write_str(sep)?;
        }
        write!(f, "{item}")?;
    }
    Ok(())
}
