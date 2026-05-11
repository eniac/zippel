use from_pest::{ConversionError, FromPest};
use pest::iterators::Pairs;
use std::fmt;

use crate::parser::*;
use share::{BoxAllocator, DocAllocator, DocBuilder, Pretty};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Ord, PartialOrd, Default)]
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
            (Distribution::Uniform, Distribution::UniformNonZero)
            | (Distribution::UniformNonZero, Distribution::Uniform) => Distribution::UniformNonZero,
            (Distribution::Uniform, Distribution::Nonuniform)
            | (Distribution::Nonuniform, Distribution::Uniform) => Distribution::Uniform,
            (a, b) if a == b => *a,
            (_, _) => Distribution::Nonuniform,
        }
    }

    pub fn sub(&self, other: &Distribution) -> Distribution {
        match (self, other) {
            (Distribution::Uniform, Distribution::UniformNonZero)
            | (Distribution::UniformNonZero, Distribution::Uniform) => Distribution::UniformNonZero,
            (Distribution::Uniform, Distribution::Nonuniform)
            | (Distribution::Nonuniform, Distribution::Uniform) => Distribution::Uniform,
            (a, b) if a == b => *a,
            (_, _) => Distribution::Nonuniform,
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

impl<'a> fmt::Display for Distribution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <Distribution as Pretty<'_, BoxAllocator, ()>>::pretty(self.clone(), &BoxAllocator)
            .1
            .render_fmt(20, f)
    }
}

impl<'pest> FromPest<'pest> for Distribution {
    type Rule = Rule;
    type FatalError = InputError<'pest>;

    fn from_pest(
        pest: &mut Pairs<'pest, Self::Rule>,
    ) -> Result<Self, ConversionError<Self::FatalError>> {
        let pair = pest.next().ok_or(ConversionError::NoMatch)?;
        match pair.as_rule() {
            Rule::distribution => {
                let inner = pair.into_inner();
                if let Some(star_pair) = inner.peek() {
                    if star_pair.as_rule() == Rule::star {
                        return Ok(Distribution::UniformNonZero);
                    }
                }
                Ok(Distribution::Uniform)
            }
            _ => Err(ConversionError::NoMatch),
        }
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
    fn test_add_uniform_uniform_nz() {
        let result = Distribution::Uniform.add(&Distribution::UniformNonZero);
        assert_eq!(result, Distribution::UniformNonZero);
    }

    #[test]
    fn test_add_uniform_nz_uniform() {
        let result = Distribution::UniformNonZero.add(&Distribution::Uniform);
        assert_eq!(result, Distribution::UniformNonZero);
    }

    #[test]
    fn test_add_uniform_nonuniform() {
        let result = Distribution::Uniform.add(&Distribution::Nonuniform);
        assert_eq!(result, Distribution::Uniform);
    }

    #[test]
    fn test_add_nonuniform_uniform() {
        let result = Distribution::Nonuniform.add(&Distribution::Uniform);
        assert_eq!(result, Distribution::Uniform);
    }

    #[test]
    fn test_add_same() {
        assert_eq!(
            Distribution::Uniform.add(&Distribution::Uniform),
            Distribution::Uniform
        );
        assert_eq!(
            Distribution::UniformNonZero.add(&Distribution::UniformNonZero),
            Distribution::UniformNonZero
        );
        assert_eq!(
            Distribution::Nonuniform.add(&Distribution::Nonuniform),
            Distribution::Nonuniform
        );
    }

    #[test]
    fn test_add_uniform_nz_nonuniform() {
        let result = Distribution::UniformNonZero.add(&Distribution::Nonuniform);
        assert_eq!(result, Distribution::Nonuniform);
    }

    #[test]
    fn test_sub_uniform_uniform_nz() {
        let result = Distribution::Uniform.sub(&Distribution::UniformNonZero);
        assert_eq!(result, Distribution::UniformNonZero);
    }

    #[test]
    fn test_sub_uniform_nz_uniform() {
        let result = Distribution::UniformNonZero.sub(&Distribution::Uniform);
        assert_eq!(result, Distribution::UniformNonZero);
    }

    #[test]
    fn test_sub_uniform_nonuniform() {
        let result = Distribution::Uniform.sub(&Distribution::Nonuniform);
        assert_eq!(result, Distribution::Uniform);
    }

    #[test]
    fn test_sub_nonuniform_uniform() {
        let result = Distribution::Nonuniform.sub(&Distribution::Uniform);
        assert_eq!(result, Distribution::Uniform);
    }

    #[test]
    fn test_sub_same() {
        assert_eq!(
            Distribution::Uniform.sub(&Distribution::Uniform),
            Distribution::Uniform
        );
        assert_eq!(
            Distribution::UniformNonZero.sub(&Distribution::UniformNonZero),
            Distribution::UniformNonZero
        );
        assert_eq!(
            Distribution::Nonuniform.sub(&Distribution::Nonuniform),
            Distribution::Nonuniform
        );
    }

    #[test]
    fn test_mul_uniform_uniform_nz() {
        let result = Distribution::Uniform.mul(&Distribution::UniformNonZero);
        assert_eq!(result, Distribution::Uniform);
    }

    #[test]
    fn test_mul_uniform_nz_uniform() {
        let result = Distribution::UniformNonZero.mul(&Distribution::Uniform);
        assert_eq!(result, Distribution::Uniform);
    }

    #[test]
    fn test_mul_uniform_uniform() {
        let result = Distribution::Uniform.mul(&Distribution::Uniform);
        assert_eq!(result, Distribution::Nonuniform);
    }

    #[test]
    fn test_mul_uniform_nz_uniform_nz() {
        let result = Distribution::UniformNonZero.mul(&Distribution::UniformNonZero);
        assert_eq!(result, Distribution::UniformNonZero);
    }

    #[test]
    fn test_mul_with_nonuniform() {
        // Uniform * Nonuniform = Nonuniform (zero bias breaks masking)
        assert_eq!(
            Distribution::Uniform.mul(&Distribution::Nonuniform),
            Distribution::Nonuniform
        );
        assert_eq!(
            Distribution::Nonuniform.mul(&Distribution::Uniform),
            Distribution::Nonuniform
        );
        // UniformNonZero * Nonuniform = Nonuniform (Nonuniform may be always-zero)
        assert_eq!(
            Distribution::UniformNonZero.mul(&Distribution::Nonuniform),
            Distribution::Nonuniform
        );
        assert_eq!(
            Distribution::Nonuniform.mul(&Distribution::UniformNonZero),
            Distribution::Nonuniform
        );
    }

    #[test]
    fn test_inv_uniform_nz() {
        let result = Distribution::UniformNonZero.inv();
        assert_eq!(result, Distribution::Uniform);
    }

    #[test]
    fn test_inv_uniform() {
        let result = Distribution::Uniform.inv();
        assert_eq!(result, Distribution::Nonuniform);
    }

    #[test]
    fn test_inv_nonuniform() {
        let result = Distribution::Nonuniform.inv();
        assert_eq!(result, Distribution::Nonuniform);
    }

    #[test]
    fn test_default() {
        assert_eq!(Distribution::default(), Distribution::Nonuniform);
    }

    #[test]
    fn test_display_uniform() {
        assert_eq!(Distribution::Uniform.to_string(), "uniform ");
    }

    #[test]
    fn test_display_uniform_nz() {
        assert_eq!(Distribution::UniformNonZero.to_string(), "uniform*");
    }

    #[test]
    fn test_display_nonuniform() {
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

    /// Regression: UniformNonZero * Nonuniform must be Nonuniform, not Uniform.
    /// Nonuniform includes always-zero values; multiplying by a non-zero mask
    /// does not produce a uniform distribution when the other factor is always 0.
    #[test]
    fn test_mul_uniform_nz_nonuniform_is_nonuniform() {
        assert_eq!(
            Distribution::UniformNonZero.mul(&Distribution::Nonuniform),
            Distribution::Nonuniform
        );
        assert_eq!(
            Distribution::Nonuniform.mul(&Distribution::UniformNonZero),
            Distribution::Nonuniform
        );
    }
}
