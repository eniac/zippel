use share::{BoxAllocator, DocAllocator, DocBuilder, Pretty};
use std::fmt;

/// This is for no-type annotations and no principals
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Copy, Clone)]
pub struct Nothing;

////////////////////////////////////////////////////////////////////////////////////////
/* Pretty Formatting & Display */
////////////////////////////////////////////////////////////////////////////////////////
impl<'a, D, A> Pretty<'a, D, A> for Nothing
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        allocator.text("")
    }
    fn is_nil(&self) -> bool {
        true
    }
}

impl fmt::Display for Nothing {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Nothing as Pretty<'_, BoxAllocator, ()>>::pretty(*self, &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_nothing_pretty() {
        let nothing = Nothing;
        assert_eq!(nothing.to_string(), "");
        assert!(<Nothing as Pretty<'_, BoxAllocator, ()>>::is_nil(&nothing));
    }
}
