//! Vectors that share their storage.

use rayon::prelude::*;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, Range};
use std::sync::Arc;

/// A vector that may share its storage with others.
///
/// Cloning or slicing shares the buffer instead of copying it; reads see a
/// plain slice (`Deref<Target = [T]>`). A write goes through [`Shared::to_mut`],
/// which first copies the viewed elements into a buffer of their own unless
/// this is the only owner of a whole buffer.
pub struct Shared<T> {
    buf: Arc<Vec<T>>,
    /// The viewed part of `buf`: `start..start + len`, or all of it when
    /// `len` is [`WHOLE`] (which follows the buffer's length when it is
    /// written through [`Shared::to_mut`]). Unlike an
    /// `Option<Range<usize>>`, this needs no discriminant, which keeps a
    /// handle at 24 bytes and so [`crate::Value`] small.
    start: usize,
    len: usize,
}

/// The `len` of a view of the whole buffer: no buffer has this many
/// elements, so no real view has this length.
const WHOLE: usize = usize::MAX;

impl<T> Shared<T> {
    /// The viewed range of the buffer; `None` is all of it.
    fn range(&self) -> Option<Range<usize>> {
        (self.len != WHOLE).then(|| self.start..self.start + self.len)
    }

    /// A handle on `buf` viewing `range`, or all of it for `None`.
    pub(crate) fn with_range(buf: Arc<Vec<T>>, range: Option<Range<usize>>) -> Self {
        match range {
            None => Shared {
                buf,
                start: 0,
                len: WHOLE,
            },
            Some(r) => Shared {
                buf,
                start: r.start,
                len: r.len(),
            },
        }
    }

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
        let offset = self.range().map_or(0, |r| r.start);
        let absolute = offset + range.start..offset + range.end;
        let whole = absolute == (0..self.buf.len());
        Shared::with_range(Arc::clone(&self.buf), (!whole).then_some(absolute))
    }
}

impl<T: Clone + Send + Sync> Shared<T> {
    /// The elements at `indices`, in order. A contiguous ascending run, which
    /// is what a slice `v[a..b]` lowers to, gives a view sharing this buffer;
    /// any other index list gathers a copy.
    ///
    /// # Panics
    /// Panics if an index is out of bounds.
    #[must_use]
    pub fn select(&self, indices: &[usize]) -> Self {
        match contiguous_run(indices) {
            Some(run) => self.slice(run),
            None => Shared::from(
                indices
                    .par_iter()
                    .map(|&i| self[i].clone())
                    .collect::<Vec<_>>(),
            ),
        }
    }
}

/// `start..end` when `indices` is `start, start + 1, …, end - 1` (an empty list
/// is the empty run `0..0`); `None` otherwise.
pub(crate) fn contiguous_run(indices: &[usize]) -> Option<Range<usize>> {
    let Some(&start) = indices.first() else {
        return Some(0..0);
    };
    let consecutive = indices.windows(2).all(|w| w[1] == w[0] + 1);
    consecutive.then(|| start..start + indices.len())
}

impl<T: Clone> Shared<T> {
    /// The elements, for writing: copies the viewed elements first if the
    /// buffer is shared or this is a view of part of it.
    pub fn to_mut(&mut self) -> &mut Vec<T> {
        if self.range().is_some() || Arc::get_mut(&mut self.buf).is_none() {
            *self = Shared::from(self.to_vec());
        }
        Arc::get_mut(&mut self.buf).expect("buffer is unshared after the copy")
    }

    /// The elements in a buffer of their own: a view is copied out of the
    /// buffer it would otherwise keep alive; a whole buffer is kept.
    #[must_use]
    pub fn compact(self) -> Self {
        if self.range().is_some() {
            Shared::from(self.to_vec())
        } else {
            self
        }
    }

    /// The elements as a `Vec`: moved out if this is the only owner of the
    /// whole buffer, copied otherwise.
    #[must_use]
    pub fn into_vec(self) -> Vec<T> {
        if self.range().is_some() {
            return self.to_vec();
        }
        Arc::try_unwrap(self.buf).unwrap_or_else(|buf| buf.to_vec())
    }
}

impl<T> Deref for Shared<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        match self.range() {
            None => &self.buf,
            Some(r) => &self.buf[r],
        }
    }
}

impl<T> From<Vec<T>> for Shared<T> {
    fn from(v: Vec<T>) -> Self {
        Shared::with_range(Arc::new(v), None)
    }
}

/// Shares the buffer.
impl<T> Clone for Shared<T> {
    fn clone(&self) -> Self {
        Shared {
            buf: Arc::clone(&self.buf),
            start: self.start,
            len: self.len,
        }
    }
}

impl<T> FromIterator<T> for Shared<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Shared::from(iter.into_iter().collect::<Vec<T>>())
    }
}

impl<T: Send> FromParallelIterator<T> for Shared<T> {
    fn from_par_iter<I: IntoParallelIterator<Item = T>>(iter: I) -> Self {
        Shared::from(iter.into_par_iter().collect::<Vec<T>>())
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_handle_is_twenty_four_bytes() {
        assert_eq!(size_of::<Shared<u64>>(), 24);
    }

    #[test]
    fn a_whole_view_follows_writes_through_to_mut() {
        let mut v = Shared::from(vec![1, 2]);
        v.to_mut().extend([3, 4, 5]);
        assert_eq!(&*v, &[1, 2, 3, 4, 5]);
        assert_eq!(&*v.slice(1..5), &[2, 3, 4, 5]);
    }

    #[test]
    fn a_view_out_to_the_end_keeps_its_range() {
        let v = Shared::from(vec![1, 2, 3, 4]);
        let tail = v.slice(2..4);
        assert_eq!(tail.range(), Some(2..4));
        assert_eq!(&*tail.slice(1..2), &[4]);
    }

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
        assert!(v.slice(0..3).range().is_none());
    }

    #[test]
    fn compact_copies_a_view_out_of_its_buffer() {
        let v = Shared::from(vec![7u64; 1 << 10]);
        let buffer = Arc::downgrade(&v.buf);
        let one = v.slice(3..4).compact();
        let whole = v.clone().compact();
        assert!(std::ptr::eq(&v[0], &whole[0]), "a whole buffer is kept");
        drop((v, whole));
        assert!(buffer.upgrade().is_none(), "the view no longer holds it");
        assert_eq!(&*one, &[7]);
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
    fn select_views_a_contiguous_run() {
        let v = Shared::from(vec![10u64, 11, 12, 13, 14]);
        let s = v.select(&[1, 2, 3]);
        assert!(std::ptr::eq(&v[1], &s[0]), "a run is a view, not a copy");
        assert_eq!(&*s, &[11, 12, 13]);
        assert_eq!(s.len(), 3);
        assert_eq!(s.to_vec(), vec![11, 12, 13]);
        assert_eq!(s.clone().into_vec(), vec![11, 12, 13]);
    }

    #[test]
    fn select_copies_other_index_lists() {
        let v = Shared::from(vec![10u64, 11, 12, 13]);
        for idx in [&[3, 2][..], &[0, 2], &[1, 1]] {
            let s = v.select(idx);
            let expected: Vec<u64> = idx.iter().map(|&i| v[i]).collect();
            assert_eq!(s, expected);
            assert!(
                s.range().is_none(),
                "{idx:?} is gathered into its own buffer"
            );
        }
    }

    #[test]
    fn select_of_nothing_is_empty() {
        let v = Shared::from(vec![1u64, 2]);
        assert!(v.select(&[]).is_empty());
    }

    #[test]
    #[should_panic(expected = "out of bounds")]
    fn select_rejects_a_run_past_the_end() {
        let _ = Shared::from(vec![1u64, 2]).select(&[1, 2]);
    }

    #[test]
    fn writing_a_selected_view_leaves_the_parent() {
        let v = Shared::from(vec![1u64, 2, 3, 4]);
        let mut s = v.select(&[2, 3]);
        s.to_mut()[0] = 99;
        assert_eq!(&*s, &[99, 4]);
        assert_eq!(&*v, &[1, 2, 3, 4]);
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
