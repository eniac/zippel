//! The encoding and sizes of a polynomial type, shared by the source types ([`Typ::Poly`])
//! and the backend types (`backend::ATyp::Poly`), together with the shape rules for combining
//! polynomials, so both layers follow one rule.
//!
//! [`Typ::Poly`]: crate::typ::Typ::Poly

use crate::ast::BinOp;
use crate::ast::spanned::Spanned;
use std::borrow::Borrow;

/// How a polynomial is represented, with exactly the sizes that representation has. `S` is the
/// size slot: `Spanned<N>` in source types, which keep where each size was written, and
/// `usize` in backend types.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PolyTyp<S> {
    /// Coefficient form in one variable, of degree at most `degree` (source `Uni<F, D>`).
    Uni {
        /// Degree bound.
        degree: S,
    },
    /// Evaluations on the Boolean hypercube of `vars` variables (source `Mle<F, N>`).
    Mle {
        /// Number of variables.
        vars: S,
    },
    /// Coefficient form in `vars` variables, of degree at most `degree` in each
    /// (source `Poly<F, V, D>`).
    General {
        /// Number of variables.
        vars: S,
        /// Degree bound in each variable.
        degree: S,
    },
}

/// Why two polynomial shapes do not combine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PolyShapeError {
    /// The polynomials have different numbers of variables. Lifting one to the other's
    /// variables has no single meaning (the new variables could be ignored or vanish), so it
    /// is never implicit.
    VariableCount,
    /// The resulting degree bound overflows `usize`.
    DegreeOverflow,
}

impl<S> PolyTyp<S> {
    /// The same encoding with every size mapped by `f`.
    ///
    /// # Errors
    /// The first error `f` returns.
    pub fn try_map<U, E>(self, mut f: impl FnMut(S) -> Result<U, E>) -> Result<PolyTyp<U>, E> {
        Ok(match self {
            PolyTyp::Uni { degree } => PolyTyp::Uni { degree: f(degree)? },
            PolyTyp::Mle { vars } => PolyTyp::Mle { vars: f(vars)? },
            PolyTyp::General { vars, degree } => PolyTyp::General {
                vars: f(vars)?,
                degree: f(degree)?,
            },
        })
    }

    /// The sizes this encoding stores, in declaration order (`vars` before `degree`).
    pub fn sizes(&self) -> Vec<&S> {
        match self {
            PolyTyp::Uni { degree } => vec![degree],
            PolyTyp::Mle { vars } => vec![vars],
            PolyTyp::General { vars, degree } => vec![vars, degree],
        }
    }

    /// Whether `self` and `other` are the same encoding, whatever their sizes.
    pub fn same_encoding<U>(&self, other: &PolyTyp<U>) -> bool {
        matches!(
            (self, other),
            (PolyTyp::Uni { .. }, PolyTyp::Uni { .. })
                | (PolyTyp::Mle { .. }, PolyTyp::Mle { .. })
                | (PolyTyp::General { .. }, PolyTyp::General { .. })
        )
    }
}

impl<N: Clone> PolyTyp<Spanned<N>> {
    /// The sizes without their source spans.
    #[must_use]
    pub fn unspanned(&self) -> PolyTyp<N> {
        self.clone()
            .try_map(|s| Ok::<_, std::convert::Infallible>(s.node))
            .unwrap_or_else(|never| match never {})
    }
}

impl<N> PolyTyp<N> {
    /// The same sizes, each with a dummy source span.
    #[must_use]
    pub fn spanned(self) -> PolyTyp<Spanned<N>> {
        self.try_map(|s| Ok::<_, std::convert::Infallible>(Spanned::dummy(s)))
            .unwrap_or_else(|never| match never {})
    }
}

/// The shape rules read concrete sizes from any slot that holds one: `usize` in backend types,
/// `Spanned<usize>` in source types, so neither has to drop or add spans to ask.
impl<S: Borrow<usize>> PolyTyp<S> {
    /// Number of variables: one for `Uni`.
    #[must_use]
    pub fn vars(&self) -> usize {
        match self {
            PolyTyp::Uni { .. } => 1,
            PolyTyp::Mle { vars } | PolyTyp::General { vars, .. } => *vars.borrow(),
        }
    }

    /// Degree bound in each variable: one for `Mle`.
    #[must_use]
    pub fn degree(&self) -> usize {
        match self {
            PolyTyp::Mle { .. } => 1,
            PolyTyp::Uni { degree } | PolyTyp::General { degree, .. } => *degree.borrow(),
        }
    }

    /// The shape of the sum, difference or join (two branches meeting) of polynomials of
    /// shapes `self` and `other`: the same encoding with the higher degree, or a general
    /// polynomial covering both.
    ///
    /// # Errors
    /// [`PolyShapeError::VariableCount`] when the numbers of variables differ.
    pub fn join<T: Borrow<usize>>(
        &self,
        other: &PolyTyp<T>,
    ) -> Result<PolyTyp<usize>, PolyShapeError> {
        let vars = self.same_vars(other)?;
        let degree = self.degree().max(other.degree());
        Ok(match (self, other) {
            (PolyTyp::Uni { .. }, PolyTyp::Uni { .. }) => PolyTyp::Uni { degree },
            (PolyTyp::Mle { .. }, PolyTyp::Mle { .. }) => PolyTyp::Mle { vars },
            _ => PolyTyp::General { vars, degree },
        })
    }

    /// The shape of the product of polynomials of shapes `self` and `other`: degrees add,
    /// a product of univariates stays univariate, any other is general.
    ///
    /// # Errors
    /// [`PolyShapeError::VariableCount`] when the numbers of variables differ,
    /// [`PolyShapeError::DegreeOverflow`] when the degree overflows.
    pub fn mul<T: Borrow<usize>>(
        &self,
        other: &PolyTyp<T>,
    ) -> Result<PolyTyp<usize>, PolyShapeError> {
        let vars = self.same_vars(other)?;
        let degree = self
            .degree()
            .checked_add(other.degree())
            .ok_or(PolyShapeError::DegreeOverflow)?;
        Ok(match (self, other) {
            (PolyTyp::Uni { .. }, PolyTyp::Uni { .. }) => PolyTyp::Uni { degree },
            _ => PolyTyp::General { vars, degree },
        })
    }

    /// The shape of `self op other` for `op` one of `==` (a join), `+`, `-` ([`Self::join`])
    /// or `*` ([`Self::mul`]).
    ///
    /// # Errors
    /// As [`Self::join`] and [`Self::mul`].
    ///
    /// # Panics
    /// For any other operator: no polynomial shape rule covers it, so a caller passing one is
    /// a bug.
    pub fn combine<T: Borrow<usize>>(
        &self,
        op: BinOp,
        other: &PolyTyp<T>,
    ) -> Result<PolyTyp<usize>, PolyShapeError> {
        match op {
            BinOp::Mul => self.mul(other),
            BinOp::Equ | BinOp::Add | BinOp::Sub => self.join(other),
            _ => panic!("no polynomial shape rule for {op:?}"),
        }
    }

    /// Whether a polynomial of shape `self` may stand where one of shape `expected` is
    /// declared (a return value, a record field, a call argument): only the same encoding,
    /// over the same variables, of at most the expected degree. A different encoding never
    /// fits even when it describes the same polynomials, because each encoding is a
    /// representation the analyses and the input check rely on; padding coefficients with
    /// zeros keeps the polynomial, so a lower degree fits.
    #[must_use]
    pub fn fits<T: Borrow<usize>>(&self, expected: &PolyTyp<T>) -> bool {
        self.same_encoding(expected)
            && self.vars() == expected.vars()
            && self.degree() <= expected.degree()
    }

    /// The shared number of variables of `self` and `other`.
    fn same_vars<T: Borrow<usize>>(&self, other: &PolyTyp<T>) -> Result<usize, PolyShapeError> {
        if self.vars() == other.vars() {
            Ok(self.vars())
        } else {
            Err(PolyShapeError::VariableCount)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::PolyShapeError::{DegreeOverflow, VariableCount};
    use super::PolyTyp;

    const fn uni(degree: usize) -> PolyTyp<usize> {
        PolyTyp::Uni { degree }
    }
    const fn mle(vars: usize) -> PolyTyp<usize> {
        PolyTyp::Mle { vars }
    }
    const fn general(vars: usize, degree: usize) -> PolyTyp<usize> {
        PolyTyp::General { vars, degree }
    }

    #[test]
    fn join_keeps_an_encoding_or_covers_both() {
        assert_eq!(uni(3).join(&uni(5)), Ok(uni(5)));
        assert_eq!(mle(4).join(&mle(4)), Ok(mle(4)));
        assert_eq!(general(2, 3).join(&general(2, 1)), Ok(general(2, 3)));
        assert_eq!(uni(3).join(&mle(1)), Ok(general(1, 3)));
        assert_eq!(mle(2).join(&general(2, 4)), Ok(general(2, 4)));
    }

    #[test]
    fn mul_adds_degrees() {
        assert_eq!(uni(3).mul(&uni(4)), Ok(uni(7)));
        assert_eq!(mle(3).mul(&mle(3)), Ok(general(3, 2)));
        assert_eq!(uni(5).mul(&mle(1)), Ok(general(1, 6)));
        assert_eq!(general(2, 3).mul(&mle(2)), Ok(general(2, 4)));
        assert_eq!(uni(usize::MAX).mul(&uni(1)), Err(DegreeOverflow));
    }

    #[test]
    fn different_numbers_of_variables_never_combine_or_fit() {
        for (a, b) in [
            (mle(2), mle(3)),
            (uni(3), mle(2)),
            (general(2, 2), general(3, 2)),
            (mle(2), general(3, 1)),
        ] {
            assert_eq!(a.join(&b), Err(VariableCount));
            assert_eq!(a.mul(&b), Err(VariableCount));
            assert!(!a.fits(&b));
        }
    }

    #[test]
    fn fits_keeps_the_encoding_and_variables() {
        assert!(uni(3).fits(&uni(5)));
        assert!(!uni(5).fits(&uni(3)));
        assert!(general(2, 3).fits(&general(2, 4)));
        assert!(mle(2).fits(&mle(2)));
        assert!(!uni(3).fits(&general(1, 3)));
        assert!(!mle(2).fits(&general(2, 1)));
        assert!(!general(1, 1).fits(&uni(1)));
    }
}
