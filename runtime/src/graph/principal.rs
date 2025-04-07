use share::{Pretty, DocAllocator, DocBuilder, BoxAllocator};
use std::fmt;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Principal {
    Verifier,
    Prover,
    Any
}

impl Default for Principal {
    fn default() -> Self {
        Principal::Any
    }
}

////////////////////////////////////////////////////////////////////////////////////////
/* Pretty Formatting & Display */
////////////////////////////////////////////////////////////////////////////////////////
impl<'a, D, A> Pretty<'a, D, A> for Principal
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            Principal::Prover => allocator.text("Prover"),
            Principal::Verifier => allocator.text("Verifier"),
            Principal::Any => allocator.text("Any"),
        }
    }
    fn is_nil(&self) -> bool {
        false
    }
}

impl<'a> fmt::Display for Principal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Principal as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(20, f)
    }
}
