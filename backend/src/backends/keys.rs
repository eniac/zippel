//! Keys: point vectors a harness declares as operands reused across operations
//! (commitment and verifier keys), and the data a backend keeps for them.
//!
//! A key is data only. The backend's bulk operations ([`crate::Backend::msm_g1`],
//! [`crate::Backend::msm_g2`], [`crate::Backend::multi_pairing`]) receive the key of an
//! operand that has one and may use it; every other operation sees the points. A backend
//! that speeds up several operations keeps the data for all of them in its key type.

use std::ops::Range;

/// Data a backend keeps for a vector of points `P` declared as a key.
pub trait Key<P>: Send + Sync + 'static + Sized {
    /// The data for `points`, or `None` when none is worth keeping.
    fn prepare(points: &[P]) -> Option<Self>;

    /// The data for the points `self` describes at `view`, followed by those `other`
    /// describes at `other_view` (`None` views are whole buffers): a key may keep only
    /// what still applies to the concatenation, or `None` (the default) for nothing.
    fn concat(
        &self,
        _view: Option<Range<usize>>,
        _other: &Self,
        _other_view: Option<Range<usize>>,
    ) -> Option<Self> {
        None
    }
}

/// A key, and the part of the buffer it describes that an operand views (`None` for
/// all of it).
pub struct Keyed<'a, K> {
    /// The data the backend keeps.
    pub key: &'a K,
    /// The viewed part of the key's buffer.
    pub view: Option<Range<usize>>,
}

impl<K> Clone for Keyed<'_, K> {
    fn clone(&self) -> Self {
        Keyed {
            key: self.key,
            view: self.view.clone(),
        }
    }
}

/// Nothing kept: the key of a backend that keeps no data for reused operands.
pub enum NoKey {}

impl<P> Key<P> for NoKey {
    fn prepare(_: &[P]) -> Option<Self> {
        None
    }
}
