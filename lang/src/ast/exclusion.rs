use std::fmt;

/// The values a `random` or `challenge` sample is drawn again on, so that it
/// is uniform over the rest of its type: `T*` excludes zero, `T - v` the
/// entries of the vector `v`, and `T - roots_of_unity(n)` every `x` with
/// `x^n == 1`. `V` represents `v` and `S` represents `n`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Exclusion<V, S> {
    /// Zero: `T*`.
    Zero,
    /// The entries of a vector: `T - v`.
    Values(V),
    /// The `n`-th roots of unity: `T - roots_of_unity(n)`.
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

    /// The excluded vector, mutably, if the exclusion lists one.
    pub const fn values_mut(&mut self) -> Option<&mut V> {
        match self {
            Exclusion::Values(v) => Some(v),
            Exclusion::Zero | Exclusion::RootsOfUnity(_) => None,
        }
    }

    /// The same exclusion with its vector rewritten by `values` and its size
    /// by `size`.
    ///
    /// # Errors
    /// Returns the first error of `values` or `size`.
    pub fn try_map<W, T, E>(
        self,
        values: impl FnOnce(V) -> Result<W, E>,
        size: impl FnOnce(S) -> Result<T, E>,
    ) -> Result<Exclusion<W, T>, E> {
        Ok(match self {
            Exclusion::Zero => Exclusion::Zero,
            Exclusion::Values(v) => Exclusion::Values(values(v)?),
            Exclusion::RootsOfUnity(n) => Exclusion::RootsOfUnity(size(n)?),
        })
    }

    /// The same exclusion with its vector rewritten by `f`.
    pub fn map_values<W>(self, f: impl FnOnce(V) -> W) -> Exclusion<W, S> {
        match self {
            Exclusion::Zero => Exclusion::Zero,
            Exclusion::Values(v) => Exclusion::Values(f(v)),
            Exclusion::RootsOfUnity(n) => Exclusion::RootsOfUnity(n),
        }
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
