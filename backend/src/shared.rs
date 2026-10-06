//! Vectors that share their storage.

use ark_serialize::{CanonicalSerialize, Compress, SerializationError, Write};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, Range};
use std::sync::Arc;

/// A vector that may share its storage with others.
///
/// Cloning or slicing shares the buffer instead of copying it; reads see a
/// plain slice (`Deref<Target = [T]>`). A write goes through [`Shared::to_mut`],
/// which copies the viewed elements first only if the buffer is shared.
pub struct Shared<T> {
    buf: Arc<Vec<T>>,
    /// The viewed part of `buf`; `None` is all of it.
    range: Option<Range<usize>>,
}

impl<T> Shared<T> {
    /// A view of `range` (relative to this view), sharing the buffer.
    ///
    /// # Panics
    /// Panics if `range` is out of bounds for this view.
    #[must_use]
    pub fn slice(&self, range: Range<usize>) -> Self {
        assert!(
            range.start <= range.end && range.end <= self.len(),
            "slice {range:?} out of bounds for a vector of length {}",
            self.len()
        );
        let offset = self.range.as_ref().map_or(0, |r| r.start);
        let absolute = offset + range.start..offset + range.end;
        Shared {
            buf: Arc::clone(&self.buf),
            range: (absolute != (0..self.buf.len())).then_some(absolute),
        }
    }
}

impl<T: Clone> Shared<T> {
    /// The elements, for writing: copies the viewed elements first if the
    /// buffer is shared or this is a view of part of it.
    pub fn to_mut(&mut self) -> &mut Vec<T> {
        if self.range.is_some() || Arc::get_mut(&mut self.buf).is_none() {
            *self = Shared::from(self.to_vec());
        }
        Arc::get_mut(&mut self.buf).expect("buffer is unshared after the copy")
    }

    /// The elements as a `Vec`: moved out if this is the only owner of the
    /// whole buffer, copied otherwise.
    #[must_use]
    pub fn into_vec(self) -> Vec<T> {
        if self.range.is_some() {
            return self.to_vec();
        }
        Arc::try_unwrap(self.buf).unwrap_or_else(|buf| buf.to_vec())
    }
}

impl<T> Deref for Shared<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        match &self.range {
            None => &self.buf,
            Some(r) => &self.buf[r.clone()],
        }
    }
}

impl<T> From<Vec<T>> for Shared<T> {
    fn from(v: Vec<T>) -> Self {
        Shared {
            buf: Arc::new(v),
            range: None,
        }
    }
}

/// Shares the buffer.
impl<T> Clone for Shared<T> {
    fn clone(&self) -> Self {
        Shared {
            buf: Arc::clone(&self.buf),
            range: self.range.clone(),
        }
    }
}

impl<'a, T> IntoIterator for &'a Shared<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T: fmt::Debug> fmt::Debug for Shared<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

/// Compares the viewed elements.
impl<T: PartialEq> PartialEq for Shared<T> {
    fn eq(&self, other: &Self) -> bool {
        **self == **other
    }
}

impl<T: Eq> Eq for Shared<T> {}

impl<T: PartialEq> PartialEq<Vec<T>> for Shared<T> {
    fn eq(&self, other: &Vec<T>) -> bool {
        **self == **other
    }
}

impl<T: PartialEq> PartialEq<[T]> for Shared<T> {
    fn eq(&self, other: &[T]) -> bool {
        **self == *other
    }
}

/// Hashes the viewed elements.
impl<T: Hash> Hash for Shared<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

/// Serializes the viewed elements exactly as a `Vec` of them would.
impl<T: CanonicalSerialize> CanonicalSerialize for Shared<T> {
    fn serialize_with_mode<W: Write>(
        &self,
        writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        (**self).serialize_with_mode(writer, compress)
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        (**self).serialized_size(compress)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clones_and_slices_share_the_buffer() {
        let v = Shared::from(vec![1, 2, 3, 4]);
        let c = v.clone();
        let s = v.slice(1..3);
        assert!(std::ptr::eq(v.as_ptr(), c.as_ptr()));
        assert!(std::ptr::eq(&v[1], &s[0]));
        assert_eq!(&*s, &[2, 3]);
        assert_eq!(&*s.slice(1..2), &[3]);
    }

    #[test]
    fn a_full_slice_is_the_whole_buffer() {
        let v = Shared::from(vec![1, 2, 3]);
        assert!(v.slice(0..3).range.is_none());
    }

    #[test]
    fn to_mut_copies_only_when_shared() {
        let mut v = Shared::from(vec![1, 2, 3]);
        let p = v.as_ptr();
        v.to_mut()[0] = 9;
        assert_eq!(v.as_ptr(), p, "unshared: written in place");

        let other = v.clone();
        v.to_mut()[0] = 7;
        assert_ne!(v.as_ptr(), other.as_ptr(), "shared: copied first");
        assert_eq!(&*v, &[7, 2, 3]);
        assert_eq!(&*other, &[9, 2, 3]);
    }

    #[test]
    fn writing_a_view_copies_just_the_view() {
        let v = Shared::from(vec![1, 2, 3, 4]);
        let mut s = v.slice(1..3);
        s.to_mut().push(5);
        assert_eq!(&*s, &[2, 3, 5]);
        assert_eq!(&*v, &[1, 2, 3, 4]);
    }

    #[test]
    fn into_vec_moves_a_sole_owner() {
        let v = Shared::from(vec![1, 2, 3]);
        let p = v.as_ptr();
        let out = v.into_vec();
        assert_eq!(out.as_ptr(), p);
    }

    #[test]
    fn equality_and_hash_follow_the_view() {
        use std::collections::hash_map::DefaultHasher;
        let a = Shared::from(vec![0, 2, 3]).slice(1..3);
        let b = Shared::from(vec![2, 3]);
        assert_eq!(a, b);
        let h = |x: &Shared<i32>| {
            let mut s = DefaultHasher::new();
            x.hash(&mut s);
            s.finish()
        };
        assert_eq!(h(&a), h(&b));
    }
}
