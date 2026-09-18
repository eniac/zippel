use std::fmt;

use share::{BoxAllocator, DocAllocator, DocBuilder, Pretty};

/// Names of the concrete `arkworks` element classes a source-level base type can denote.
///
/// This is the surface-language spelling of the backend's element kinds; the IR-level
/// counterpart is `backend::ATyp` / `ABase`. It carries no size or curve information — only
/// which family of `arkworks` value (scalar field element, curve point in either
/// representation, or target-group element) is meant.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Ark {
    /// An element of the scalar field of the configured curve.
    Scalar,
    /// A point of the first pairing source group, in projective coordinates.
    G1,
    /// A point of the second pairing source group, in projective coordinates.
    G2,
    /// A point of the first pairing source group, in affine coordinates.
    G1Affine,
    /// A point of the second pairing source group, in affine coordinates.
    G2Affine,
    /// An element of the pairing target group.
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
