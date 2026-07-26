use std::fmt;

use share::{BoxAllocator, DocAllocator, DocBuilder, Pretty};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub enum Distribution {
    Uniform,
    UniformNonZero,
    #[default]
    Nonuniform,
}

impl Distribution {
    pub fn is_uniform(&self) -> bool {
        matches!(self, Distribution::Uniform)
    }
    pub fn is_uniform_nz(&self) -> bool {
        matches!(self, Distribution::UniformNonZero)
    }
    pub fn is_nonuniform(&self) -> bool {
        matches!(self, Distribution::Nonuniform)
    }

    // Assumes independence, adding two distributions
    pub fn add(&self, other: &Distribution) -> Distribution {
        match (self, other) {
            (Distribution::Uniform, _) | (_, Distribution::Uniform) => Distribution::Uniform,
            (Distribution::UniformNonZero, Distribution::UniformNonZero) => {
                Distribution::Nonuniform
            }
            (Distribution::UniformNonZero, Distribution::Nonuniform)
            | (Distribution::Nonuniform, Distribution::UniformNonZero) => Distribution::Nonuniform,
            (Distribution::Nonuniform, Distribution::Nonuniform) => Distribution::Nonuniform,
        }
    }

    pub fn sub(&self, other: &Distribution) -> Distribution {
        match (self, other) {
            (Distribution::Uniform, _) | (_, Distribution::Uniform) => Distribution::Uniform,
            (Distribution::UniformNonZero, Distribution::UniformNonZero) => {
                Distribution::Nonuniform
            }
            (Distribution::UniformNonZero, Distribution::Nonuniform)
            | (Distribution::Nonuniform, Distribution::UniformNonZero) => Distribution::Nonuniform,
            (Distribution::Nonuniform, Distribution::Nonuniform) => Distribution::Nonuniform,
        }
    }

    // Assumes independence, multiplying two distributions.
    //
    // Cryptographic reasoning:
    //
    // - UniformNonZero * Nonuniform = Nonuniform:
    //   A non-zero uniform field element perfectly masks any value (every
    //   output is equally likely conditioned on the mask). The result may
    //   include zero when the nonuniform factor is zero, hence Uniform
    //   rather than UniformNonZero.
    //
    // - Uniform * Nonuniform = Nonuniform:
    //   A uniform element that CAN be zero introduces bias — Pr[0] is
    //   elevated because the product is zero whenever either factor is zero.
    //   This breaks the masking property, so the result is Nonuniform.
    //
    // - Uniform * Uniform = Nonuniform:
    //   Both factors may be zero, compounding the bias. Pr[0] ≈ 2/|F|
    //   instead of 1/|F|, so the product is not uniformly distributed.
    pub fn mul(&self, other: &Distribution) -> Distribution {
        match (self, other) {
            // UniformNZ * UniformNZ = UniformNZ (product of non-zero uniform values is non-zero uniform)
            (Distribution::UniformNonZero, Distribution::UniformNonZero) => {
                Distribution::UniformNonZero
            }
            // Uniform * UniformNZ or vice versa = Uniform (zero possible from the Uniform factor)
            (Distribution::Uniform, Distribution::UniformNonZero)
            | (Distribution::UniformNonZero, Distribution::Uniform) => Distribution::Uniform,
            // UniformNZ * Nonuniform = Nonuniform (Nonuniform may always be zero,
            // which would produce a biased result even with a non-zero mask)
            (Distribution::UniformNonZero, Distribution::Nonuniform)
            | (Distribution::Nonuniform, Distribution::UniformNonZero) => Distribution::Nonuniform,
            // Uniform * Uniform = Nonuniform (zero-biased: Pr[0] = 2/|F| - 1/|F|^2)
            (Distribution::Uniform, Distribution::Uniform) => Distribution::Nonuniform,
            // Uniform * Nonuniform = Nonuniform (zero bias from Uniform factor breaks masking)
            (Distribution::Uniform, Distribution::Nonuniform)
            | (Distribution::Nonuniform, Distribution::Uniform) => Distribution::Nonuniform,
            // Nonuniform * Nonuniform = Nonuniform
            (Distribution::Nonuniform, Distribution::Nonuniform) => Distribution::Nonuniform,
        }
    }

    pub fn inv(&self) -> Distribution {
        match self {
            Distribution::UniformNonZero => Distribution::Uniform,
            _ => Distribution::Nonuniform,
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////
/* Pretty Formatting & Display */
////////////////////////////////////////////////////////////////////////////////////////
impl<'a, D, A> Pretty<'a, D, A> for Distribution
where
    D: DocAllocator<'a, A>,
    D::Doc: Clone,
    A: 'a + Clone,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        match self {
            Distribution::Uniform => allocator.text("uniform "),
            Distribution::UniformNonZero => allocator.text("uniform*"),
            Distribution::Nonuniform => allocator.text(""),
        }
    }
    fn is_nil(&self) -> bool {
        self.is_nonuniform()
    }
}

impl fmt::Display for Distribution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Distribution as Pretty<'_, BoxAllocator, ()>>::pretty(*self, &BoxAllocator)
            .1
            .render_fmt(20, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_uniform() {
        assert!(Distribution::Uniform.is_uniform());
        assert!(!Distribution::UniformNonZero.is_uniform());
        assert!(!Distribution::Nonuniform.is_uniform());
    }

    #[test]
    fn test_is_uniform_nz() {
        assert!(!Distribution::Uniform.is_uniform_nz());
        assert!(Distribution::UniformNonZero.is_uniform_nz());
        assert!(!Distribution::Nonuniform.is_uniform_nz());
    }

    #[test]
    fn test_is_nonuniform() {
        assert!(!Distribution::Uniform.is_nonuniform());
        assert!(!Distribution::UniformNonZero.is_nonuniform());
        assert!(Distribution::Nonuniform.is_nonuniform());
    }

    #[test]
    fn test_distribution_ops_exhaustive() {
        use Distribution::*;

        // Exhaustive test for add
        let expected_add = [
            (Uniform, Uniform, Uniform),
            (Uniform, UniformNonZero, Uniform),
            (Uniform, Nonuniform, Uniform),
            (UniformNonZero, Uniform, Uniform),
            (UniformNonZero, UniformNonZero, Nonuniform),
            (UniformNonZero, Nonuniform, Nonuniform),
            (Nonuniform, Uniform, Uniform),
            (Nonuniform, UniformNonZero, Nonuniform),
            (Nonuniform, Nonuniform, Nonuniform),
        ];
        for (a, b, expected) in expected_add {
            assert_eq!(a.add(&b), expected, "{:?}.add({:?})", a, b);
        }

        // Exhaustive test for sub
        let expected_sub = [
            (Uniform, Uniform, Uniform),
            (Uniform, UniformNonZero, Uniform),
            (Uniform, Nonuniform, Uniform),
            (UniformNonZero, Uniform, Uniform),
            (UniformNonZero, UniformNonZero, Nonuniform),
            (UniformNonZero, Nonuniform, Nonuniform),
            (Nonuniform, Uniform, Uniform),
            (Nonuniform, UniformNonZero, Nonuniform),
            (Nonuniform, Nonuniform, Nonuniform),
        ];
        for (a, b, expected) in expected_sub {
            assert_eq!(a.sub(&b), expected, "{:?}.sub({:?})", a, b);
        }

        // Exhaustive test for mul
        let expected_mul = [
            (Uniform, Uniform, Nonuniform),
            (Uniform, UniformNonZero, Uniform),
            (Uniform, Nonuniform, Nonuniform),
            (UniformNonZero, Uniform, Uniform),
            (UniformNonZero, UniformNonZero, UniformNonZero),
            (UniformNonZero, Nonuniform, Nonuniform),
            (Nonuniform, Uniform, Nonuniform),
            (Nonuniform, UniformNonZero, Nonuniform),
            (Nonuniform, Nonuniform, Nonuniform),
        ];
        for (a, b, expected) in expected_mul {
            assert_eq!(a.mul(&b), expected, "{:?}.mul({:?})", a, b);
        }

        // Exhaustive test for inv
        assert_eq!(Uniform.inv(), Nonuniform);
        assert_eq!(UniformNonZero.inv(), Uniform);
        assert_eq!(Nonuniform.inv(), Nonuniform);
    }

    #[test]
    fn test_distribution_algebraic_properties() {
        use Distribution::*;
        let all_dists = [Uniform, UniformNonZero, Nonuniform];

        for &x in &all_dists {
            for &y in &all_dists {
                // Commutativity
                assert_eq!(
                    x.add(&y),
                    y.add(&x),
                    "add commutativity failed for {:?}, {:?}",
                    x,
                    y
                );
                assert_eq!(
                    x.mul(&y),
                    y.mul(&x),
                    "mul commutativity failed for {:?}, {:?}",
                    x,
                    y
                );

                // Uniform masking
                assert_eq!(Uniform.add(&x), Uniform);
                assert_eq!(x.add(&Uniform), Uniform);
                assert_eq!(Uniform.sub(&x), Uniform);

                for &z in &all_dists {
                    // Associativity
                    assert_eq!(
                        x.add(&y.add(&z)),
                        x.add(&y).add(&z),
                        "add associativity failed for {:?}, {:?}, {:?}",
                        x,
                        y,
                        z
                    );
                    assert_eq!(
                        x.mul(&y.mul(&z)),
                        x.mul(&y).mul(&z),
                        "mul associativity failed for {:?}, {:?}, {:?}",
                        x,
                        y,
                        z
                    );
                }
            }
        }
    }

    #[test]
    fn test_default() {
        assert_eq!(Distribution::default(), Distribution::Nonuniform);
    }

    #[test]
    fn test_display() {
        assert_eq!(Distribution::Uniform.to_string(), "uniform ");
        assert_eq!(Distribution::UniformNonZero.to_string(), "uniform*");
        assert_eq!(Distribution::Nonuniform.to_string(), "");
    }

    #[test]
    fn test_is_nil() {
        assert!(!<Distribution as Pretty<'_, BoxAllocator, ()>>::is_nil(
            &Distribution::Uniform
        ));
        assert!(!<Distribution as Pretty<'_, BoxAllocator, ()>>::is_nil(
            &Distribution::UniformNonZero
        ));
        assert!(<Distribution as Pretty<'_, BoxAllocator, ()>>::is_nil(
            &Distribution::Nonuniform
        ));
    }
}
