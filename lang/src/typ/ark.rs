use std::fmt;

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ark_pretty_scalar() {
        let ark = Ark::Scalar;
        assert_eq!(ark.to_string(), "Scalar");
        assert!(!<Ark as Pretty<'_, BoxAllocator, ()>>::is_nil(&ark));
    }

    #[test]
    fn test_ark_pretty_g1() {
        let ark = Ark::G1;
        assert_eq!(ark.to_string(), "G1");
        assert!(!<Ark as Pretty<'_, BoxAllocator, ()>>::is_nil(&ark));
    }

    #[test]
    fn test_ark_pretty_g2() {
        let ark = Ark::G2;
        assert_eq!(ark.to_string(), "G2");
        assert!(!<Ark as Pretty<'_, BoxAllocator, ()>>::is_nil(&ark));
    }

    #[test]
    fn test_ark_pretty_g1_affine() {
        let ark = Ark::G1Affine;
        assert_eq!(ark.to_string(), "G1Affine");
        assert!(!<Ark as Pretty<'_, BoxAllocator, ()>>::is_nil(&ark));
    }

    #[test]
    fn test_ark_pretty_g2_affine() {
        let ark = Ark::G2Affine;
        assert_eq!(ark.to_string(), "G2Affine");
        assert!(!<Ark as Pretty<'_, BoxAllocator, ()>>::is_nil(&ark));
    }

    #[test]
    fn test_ark_pretty_gt() {
        let ark = Ark::GT;
        assert_eq!(ark.to_string(), "GT");
        assert!(!<Ark as Pretty<'_, BoxAllocator, ()>>::is_nil(&ark));
    }

    #[test]
    fn test_ark_equality() {
        assert_eq!(Ark::Scalar, Ark::Scalar);
        assert_ne!(Ark::Scalar, Ark::G1);
        assert_eq!(Ark::G1, Ark::G1);
        assert_ne!(Ark::G1, Ark::G2);
    }

    #[test]
    fn test_ark_clone() {
        let ark = Ark::Scalar;
        let cloned = ark.clone();
        assert_eq!(ark, cloned);
    }
}
