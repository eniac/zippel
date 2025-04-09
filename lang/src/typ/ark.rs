use std::fmt;

use lang::typ::Typ;
use share::{Pretty, BoxAllocator, DocAllocator, DocBuilder};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Ark {
    Scalar,
    G1,
    G2,
    G1Affine,
    G2Affine,
    GT
}

/// Pretty-printer for Ark
impl<'a, D, A> Pretty<'a, D, A> for Ark
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            Ark::Scalar => allocator.text("Scalar"),
            Ark::G1 => allocator.text("G1"),
            Ark::G2 => allocator.text("G2"),
            Ark::G1Affine => allocator.text("G1Affine"),
            Ark::G2Affine => allocator.text("G2Affine"),
            Ark::GT => allocator.text("GT"),
        }
    }

    fn is_nil(&self) -> bool {
        false
    }
}

impl<'a> fmt::Display for Ark {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Ark as Pretty<'a, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}
