use std::fmt;

use share::{BoxAllocator, DocAllocator, DocBuilder, Pretty};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Ark {
    Scalar,
    G1,
    G2,
    G1Affine,
    G2Affine,
    GT,
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
        <Ark as Pretty<'a, BoxAllocator, ()>>::pretty(*self, &BoxAllocator)
            .1
            .render_fmt(100, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ark_pretty_formatting() {
        let cases = [
            (Ark::Scalar, "Scalar"),
            (Ark::G1, "G1"),
            (Ark::G2, "G2"),
            (Ark::G1Affine, "G1Affine"),
            (Ark::G2Affine, "G2Affine"),
            (Ark::GT, "GT"),
        ];
        for (ark, expected) in cases {
            assert_eq!(ark.to_string(), expected);
            assert!(!<Ark as Pretty<'_, BoxAllocator, ()>>::is_nil(&ark));
        }
    }
}
