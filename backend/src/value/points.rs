//! Group point vectors with an optional key: the data a backend keeps for points a
//! harness declares reused (see [`crate::backends::keys`]). A vector value is its points;
//! only the backend's bulk operations read the key.

use crate::backends::keys::Keyed;
use crate::value::shared::Shared;
use rayon::prelude::*;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, Range};
use std::sync::Arc;

/// Points `T`, shared as a [`Shared`] vector, with an optional key `K` describing their
/// whole buffer.
///
/// The points are the value: equality, hashing and every operation but the backend's
/// bulk ones see only them. A view keeps its buffer's key, read at the view's range; any
/// copy (a gather, a compacted view, a write) has none.
pub struct Points<T, K> {
    points: Shared<T>,
    key: Option<Arc<K>>,
}

impl<T, K> Points<T, K> {
    /// `points`, with the key `prepare` keeps for them, if any.
    pub fn keyed(points: Vec<T>, prepare: impl FnOnce(&[T]) -> Option<K>) -> Self {
        let key = prepare(&points).map(Arc::new);
        Points {
            points: Shared::from(points),
            key,
        }
    }

    /// The key, and the part of its buffer this vector views.
    #[must_use]
    pub fn key(&self) -> Option<Keyed<'_, K>> {
        self.key.as_deref().map(|key| Keyed {
            key,
            view: self.points.range(),
        })
    }

    /// A view of `range` (relative to this view), sharing the buffer and its key.
    ///
    /// # Panics
    /// Panics if `range` is out of bounds for this view.
    #[must_use]
    pub fn slice(&self, range: Range<usize>) -> Self {
        Points {
            points: self.points.slice(range),
            key: self.key.clone(),
        }
    }
}

impl<T: Clone + Send + Sync, K> Points<T, K> {
    /// The elements at `indices`, in order: a contiguous run is a view sharing the
    /// buffer and its key; any other list gathers a copy of the points, without one.
    ///
    /// # Panics
    /// Panics if an index is out of bounds.
    #[must_use]
    pub fn select(&self, indices: &[usize]) -> Self {
        match crate::value::shared::contiguous_run(indices) {
            Some(run) => self.slice(run),
            None => self.points.select(indices).into(),
        }
    }

    /// The elements in a buffer of their own (see [`Shared::compact`]); a copied view
    /// has no key.
    #[must_use]
    pub fn compact(self) -> Self {
        match self.points.range() {
            None => self,
            Some(_) => self.points.compact().into(),
        }
    }

    /// The elements, for writing: the key no longer describes them.
    pub fn to_mut(&mut self) -> &mut Vec<T> {
        self.key = None;
        self.points.to_mut()
    }

    /// The elements as a `Vec` (see [`Shared::into_vec`]).
    #[must_use]
    pub fn into_vec(self) -> Vec<T> {
        self.points.into_vec()
    }
}

impl<T, K> Deref for Points<T, K> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        &self.points
    }
}

impl<T, K> From<Vec<T>> for Points<T, K> {
    fn from(v: Vec<T>) -> Self {
        Shared::from(v).into()
    }
}

impl<T, K> From<Shared<T>> for Points<T, K> {
    fn from(points: Shared<T>) -> Self {
        Points { points, key: None }
    }
}

/// Shares the buffer and its key.
impl<T, K> Clone for Points<T, K> {
    fn clone(&self) -> Self {
        Points {
            points: self.points.clone(),
            key: self.key.clone(),
        }
    }
}

impl<T, K> FromIterator<T> for Points<T, K> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Shared::from_iter(iter).into()
    }
}

impl<T: Send, K> FromParallelIterator<T> for Points<T, K> {
    fn from_par_iter<I: IntoParallelIterator<Item = T>>(iter: I) -> Self {
        Shared::from_par_iter(iter).into()
    }
}

impl<'a, T, K> IntoIterator for &'a Points<T, K> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T: fmt::Debug, K> fmt::Debug for Points<T, K> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

/// Compares the points.
impl<T: PartialEq, K> PartialEq for Points<T, K> {
    fn eq(&self, other: &Self) -> bool {
        **self == **other
    }
}

impl<T: Eq, K> Eq for Points<T, K> {}

/// Hashes the points.
impl<T: Hash, K> Hash for Points<T, K> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn keyed(points: Vec<u64>) -> Points<u64, &'static str> {
        Points::keyed(points, |_| Some("key"))
    }

    #[test]
    fn a_view_keeps_its_buffers_key_at_its_range() {
        let p = keyed(vec![1, 2, 3, 4]);
        assert_eq!(p.key().map(|k| (*k.key, k.view)), Some(("key", None)));
        let view = p.select(&[1, 2]);
        assert_eq!(&*view, &[2, 3]);
        assert_eq!(view.key().map(|k| k.view), Some(Some(1..3)));
        assert_eq!(view.slice(1..2).key().map(|k| k.view), Some(Some(2..3)));
    }

    #[test]
    fn a_copy_has_no_key() {
        let p = keyed(vec![1, 2, 3]);
        assert!(p.select(&[2, 0]).key().is_none());
        assert!(p.slice(1..3).compact().key().is_none());
        assert!(
            p.clone().compact().key().is_some(),
            "a whole buffer is kept"
        );
    }

    #[test]
    fn a_write_drops_the_key_and_equality_ignores_it() {
        let mut p = keyed(vec![1, 2]);
        assert_eq!(p, Points::from(vec![1, 2]));
        p.to_mut().push(3);
        assert!(p.key().is_none());
        assert_eq!(&*p, &[1, 2, 3]);
    }
}
