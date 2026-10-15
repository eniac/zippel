use std::fmt;

/// What a `random` or `challenge` sample excludes: it is resampled while
/// excluded. `V` represents an excluded vector and `S` the order of the
/// excluded roots of unity.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Exclusion<V, S> {
    /// Zero: `T*`.
    Zero,
    /// The entries of a vector: `T - v`.
    Values(V),
    /// Every `x` with `x^n == 1`: `T - roots_of_unity(n)`.
    RootsOfUnity(S),
}

impl<V, S> Exclusion<V, S> {
    /// The excluded vector, if the exclusion lists one.
    pub const fn values(&self) -> Option<&V> {
        match self {
            Exclusion::Values(v) => Some(v),
            Exclusion::Zero | Exclusion::RootsOfUnity(_) => None,
        }
    }

    /// The same exclusion, borrowing its vector and order.
    pub const fn as_ref(&self) -> Exclusion<&V, &S> {
        match self {
            Exclusion::Zero => Exclusion::Zero,
            Exclusion::Values(v) => Exclusion::Values(v),
            Exclusion::RootsOfUnity(n) => Exclusion::RootsOfUnity(n),
        }
    }

    /// The same exclusion with its vector rewritten by `f`.
    pub fn map_values<W>(self, f: impl FnOnce(V) -> W) -> Exclusion<W, S> {
        match self {
            Exclusion::Zero => Exclusion::Zero,
            Exclusion::Values(v) => Exclusion::Values(f(v)),
            Exclusion::RootsOfUnity(n) => Exclusion::RootsOfUnity(n),
        }
    }

    /// The same exclusion with its vector rewritten by `f`.
    ///
    /// # Errors
    /// Returns the error of `f`.
    pub fn try_map_values<W, E>(
        self,
        f: impl FnOnce(V) -> Result<W, E>,
    ) -> Result<Exclusion<W, S>, E> {
        Ok(match self {
            Exclusion::Zero => Exclusion::Zero,
            Exclusion::Values(v) => Exclusion::Values(f(v)?),
            Exclusion::RootsOfUnity(n) => Exclusion::RootsOfUnity(n),
        })
    }
}

/// The source syntax after the sampled type: `*`, ` - v` or
/// ` - roots_of_unity(n)`.
impl<V: fmt::Display, S: fmt::Display> fmt::Display for Exclusion<V, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Exclusion::Zero => f.write_str("*"),
            Exclusion::Values(v) => write!(f, " - {v}"),
            Exclusion::RootsOfUnity(n) => write!(f, " - roots_of_unity({n})"),
        }
    }
}
