use rand::Rng;
use std::fmt;
use thiserror::Error;

use crate::ast::spanned::Spanned;
use share::traversal::ToTraversal1;

/// Failure of the range well-formedness check.
#[derive(Error, PartialEq, Debug)]
pub enum RangeError {
    /// The triple `[start, step..end]` is not a valid strided range: `start`
    /// exceeds `end`, `step` is zero, or `end - start` is not a whole number
    /// of steps.
    #[error("Instantiated an invalid range [{0},{1}..{2}]")]
    RangeOrder(usize, usize, usize),
}

/// Represents a range of numbers.
///
/// `start` is always present. `step` and `end` are `Option` — `None`
/// means the source omitted them (e.g. bare `N` → `Range { start, None, None }`).
/// For `CRange = Range<usize>`, use the accessor methods `start()`, `step()`,
/// `end()` which fill in defaults (`step=1`, `end=start+1`).
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Range<N> {
    /// Lower bound, always present and always included in the range.
    pub start: Spanned<N>,
    /// Stride between successive elements; `None` means the source wrote no
    /// stride and the default `1` applies.
    pub step: Option<Spanned<N>>,
    /// Exclusive upper bound; `None` means the source wrote a bare bound and
    /// the range denotes the single value `start`.
    pub end: Option<Spanned<N>>,
}

/// Implementations of this trait can modify ranges
pub trait RangeTraversal<N>: Sized {
    /// Rewrite every `Range<N>` occurring inside `self`, short-circuiting on
    /// the first error the rewrite function reports.
    ///
    /// # Errors
    /// Propagates whatever error `f` returns for some nested range.
    fn range_traverse<E>(
        self,
        f: &mut dyn FnMut(Range<N>) -> Result<Range<N>, E>,
    ) -> Result<Self, E>;
}

impl<N: Clone> ToTraversal1<N> for Range<N> {
    type Output<Z> = Range<Z>;
    fn traverse1<Z: Clone, E>(self, f: &mut dyn FnMut(N) -> Result<Z, E>) -> Result<Range<Z>, E> {
        Ok(Range {
            start: Spanned::new(f(self.start.node)?, self.start.span),
            step: self
                .step
                .map(|s| f(s.node).map(|node| Spanned::new(node, s.span)))
                .transpose()?,
            end: self
                .end
                .map(|s| f(s.node).map(|node| Spanned::new(node, s.span)))
                .transpose()?,
        })
    }
}

/// Concrete sized range of numbers
pub type CRange = Range<usize>;

impl Default for CRange {
    fn default() -> Self {
        Range::from_num(0, 1, 1).expect("default range is valid")
    }
}

impl CRange {
    /// Raw start value
    pub fn start(&self) -> usize {
        self.start.node
    }
    /// Raw step value (defaults to 1 if `None`)
    pub fn step(&self) -> usize {
        self.step.as_ref().map(|s| s.node).unwrap_or(1)
    }
    /// Raw end value (defaults to `start + 1` if `None`)
    pub fn end(&self) -> usize {
        self.end
            .as_ref()
            .map(|s| s.node)
            .unwrap_or(self.start() + 1)
    }

    /// Construct a concrete range from raw values, wrapping in `Spanned::dummy`.
    pub fn from_raw(start: usize, step: usize, end: usize) -> Self {
        Range {
            start: Spanned::dummy(start),
            step: Some(Spanned::dummy(step)),
            end: Some(Spanned::dummy(end)),
        }
    }

    /// Create a range from a start, step and end numbers, checking their order
    ///
    /// # Errors
    /// Returns `RangeError::RangeOrder` if `start > end`, `step == 0`, or
    /// `end - start` is not an exact multiple of `step`.
    pub fn from_num(start: usize, step: usize, end: usize) -> Result<Self, RangeError> {
        if (start <= end)
            && (step > 0)
            && end
                .checked_sub(start)
                .map(|d| d.is_multiple_of(step))
                .unwrap_or(false)
        {
            Ok(Range::from_raw(start, step, end))
        } else {
            Err(RangeError::RangeOrder(start, step, end))
        }
    }

    /// Re-check that this range satisfies the `from_num` well-formedness
    /// invariant. Ranges built by `from_raw` or by the parser bypass the
    /// check, so passes that rely on the invariant call this first.
    ///
    /// # Errors
    /// Returns `RangeError::RangeOrder` if the range is not well formed.
    pub fn check(&self) -> Result<(), RangeError> {
        Range::from_num(self.start(), self.step(), self.end()).map(|_| ())
    }

    /// Create a singleton range
    pub fn singleton(start: usize) -> Self {
        Range {
            start: Spanned::dummy(start),
            step: None,
            end: None,
        }
    }

    /// Sample a uniformly random element of the range, used to pick a
    /// witness value for a range-kinded size variable.
    ///
    /// # Panics
    /// Panics if the range is empty (division by a zero length) or if
    /// `start + offset * step` overflows `usize`.
    pub fn random<R: Rng>(&self, rng: &mut R) -> usize {
        let offset = (rng.next_u32() % (self.len() as u32)) as usize;
        self.start()
            .checked_add(
                offset
                    .checked_mul(self.step())
                    .expect("random: offset * step overflow"),
            )
            .expect("random: start + offset*step overflow")
    }

    /// Function to check if a value is contained in the range
    pub fn contains(&self, value: usize) -> bool {
        if value < self.start() || value >= self.end() {
            return false;
        }
        (value - self.start()).is_multiple_of(self.step())
    }

    /// Fuse two ranges into one when `other` starts exactly one past this
    /// range's end and both share a stride; returns `None` when the two
    /// cannot be described by a single strided range.
    pub fn concat(&self, other: &CRange) -> Option<CRange> {
        if self.step() == other.step() && self.end() == other.start().checked_add(1)? {
            Some(Range::from_raw(self.start(), self.step(), other.end()))
        } else {
            None
        }
    }

    /// Whether the range denotes only the value zero.
    pub fn is_zero(&self) -> bool {
        self.start() == 0 && self.end() <= self.step()
    }

    /// Number of elements the range yields.
    pub fn len(&self) -> usize {
        (self.end() - self.start()) / self.step()
    }

    /// Whether the range yields no elements at all.
    pub fn is_empty(&self) -> bool {
        self.start() >= self.end()
    }

    /// Checked addition of two ranges. Returns `None` if any intermediate
    /// `usize` arithmetic overflows.
    pub fn checked_add(self, b: CRange) -> Option<CRange> {
        let a_max = self.end().checked_sub(self.step())?;
        let b_max = b.end().checked_sub(b.step())?;
        Some(Range::from_raw(
            self.start().checked_add(b.start())?,
            num::integer::gcd(self.step(), b.step()),
            a_max.checked_add(b_max)?.checked_add(1)?,
        ))
    }

    /// Checked subtraction of two ranges. Returns `None` if any intermediate
    /// `usize` arithmetic overflows or underflows.
    pub fn checked_sub(self, b: CRange) -> Option<CRange> {
        let b_max = b.end().checked_sub(b.step())?;
        let a_max = self.end().checked_sub(self.step())?;
        Some(Range::from_raw(
            self.start().checked_sub(b_max)?,
            num::integer::gcd(self.step(), b.step()),
            a_max.checked_sub(b.start())?.checked_add(1)?,
        ))
    }

    /// Checked multiplication of two ranges. Returns `None` if any
    /// intermediate `usize` arithmetic overflows.
    pub fn checked_mul(self, b: CRange) -> Option<CRange> {
        let a_min = self.start();
        let a_max = self.end().checked_sub(self.step())?;
        let b_min = b.start();
        let b_max = b.end().checked_sub(b.step())?;

        let p1 = a_min.checked_mul(b_min)?;
        let p2 = a_min.checked_mul(b_max)?;
        let p3 = a_max.checked_mul(b_min)?;
        let p4 = a_max.checked_mul(b_max)?;

        let new_start = p1.min(p2).min(p3).min(p4);
        let new_end = p1.max(p2).max(p3).max(p4).checked_add(1)?;

        let new_step = num::integer::gcd(
            self.step().checked_mul(b.step())?,
            num::integer::gcd(
                self.step().checked_mul(b.start())?,
                b.step().checked_mul(self.start())?,
            ),
        );

        Some(Range::from_raw(new_start, new_step, new_end))
    }

    /// Checked division of two ranges. Returns `None` if any intermediate
    /// `usize` arithmetic overflows or if the divisor range includes zero.
    pub fn checked_div(self, b: CRange) -> Option<CRange> {
        let a_min = self.start();
        let a_max = self.end().checked_sub(self.step())?;
        let b_min = b.start();
        let b_max = b.end().checked_sub(b.step())?;

        if b_min == 0 || b_max == 0 {
            return None;
        }

        let new_start = a_min / b_max;
        let new_end = (a_max / b_min).checked_add(1)?;

        Some(Range::from_raw(new_start, 1, new_end))
    }

    /// Checked remainder of two ranges. Returns `None` if any intermediate
    /// `usize` arithmetic overflows or if the divisor range includes zero.
    pub fn checked_rem(self, b: CRange) -> Option<CRange> {
        let a_min = self.start();
        let a_max = self.end().checked_sub(self.step())?;
        let b_min = b.start();
        let b_max = b.end().checked_sub(b.step())?;

        if b_min == 0 || b_max == 0 {
            return None;
        }

        let new_start = a_min % b_max;
        let new_end = (a_max % b_min).checked_add(1)?;

        Some(Range::from_raw(new_start, 1, new_end))
    }

    /// Checked exponentiation of two ranges. Returns `None` if any
    /// intermediate `usize` arithmetic overflows.
    pub fn checked_pow(self, b: CRange) -> Option<CRange> {
        let a_min = self.start();
        let a_max = self.end().checked_sub(self.step())?;
        let b_min = b.start();
        let b_max = b.end().checked_sub(b.step())?;

        let new_start = a_min.checked_pow(b_min as u32)?;
        let new_end = a_max.checked_pow(b_max as u32)?.checked_add(1)?;

        Some(Range::from_raw(new_start, 1, new_end))
    }
}

/// Owning iterator over a `CRange`. Yields `start, start+step, start+2*step, ...`
/// up to (but not including) `end`.
pub struct CRangeIter {
    current: usize,
    step: usize,
    end: usize,
}

impl Iterator for CRangeIter {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current >= self.end {
            None
        } else {
            let val = self.current;
            self.current = self.current.checked_add(self.step).unwrap_or(self.end);
            Some(val)
        }
    }
}

impl IntoIterator for CRange {
    type Item = usize;
    type IntoIter = CRangeIter;

    fn into_iter(self) -> CRangeIter {
        CRangeIter {
            current: self.start(),
            step: self.step(),
            end: self.end(),
        }
    }
}

/// `start[,step][..end]`
impl<N: fmt::Display> fmt::Display for Range<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.start.node)?;
        if let Some(step) = &self.step {
            write!(f, ",{}", step.node)?;
        }
        if let Some(end) = &self.end {
            write!(f, "..{}", end.node)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn crange_new(start: usize, end: usize) -> CRange {
        Range {
            start: Spanned::dummy(start),
            step: None,
            end: Some(Spanned::dummy(end)),
        }
    }

    #[test]
    fn range_traversal() {
        use crate::ast::Size;
        use crate::id::Tid;
        let r = Range {
            start: Spanned::dummy(Size::Var(Tid::from("N"))),
            step: Some(Spanned::dummy(Size::Lit(2))),
            end: Some(Spanned::dummy(Size::Lit(10))),
        };
        assert_eq!(
            r.traverse1(&mut |x| x.eval(&share::Ctx::singleton("N".into(), 0)))
                .unwrap(),
            Range {
                start: Spanned::dummy(0),
                step: Some(Spanned::dummy(2)),
                end: Some(Spanned::dummy(10)),
            }
        );
    }

    #[test]
    fn checked_add_basic() {
        let a = crange_new(1, 10);
        let b = crange_new(2, 20);
        let r = a.checked_add(b).unwrap();
        assert_eq!(r.start(), 3);
        assert_eq!(r.end(), 29); // (10-1) + (20-1) + 1 = 9 + 19 + 1
    }

    #[test]
    fn checked_add_overflow() {
        let a = crange_new(usize::MAX - 5, usize::MAX);
        let b = crange_new(1, 10);
        // start + b.start overflows
        assert_eq!(a.checked_add(b), None);
    }

    #[test]
    fn checked_add_end_overflow() {
        let a = crange_new(0, usize::MAX);
        let b = crange_new(0, 2);
        // (MAX - 1) + (2 - 1) + 1 overflows
        assert_eq!(a.checked_add(b), None);
    }

    #[test]
    fn checked_sub_basic() {
        let a = crange_new(10, 20);
        let b = crange_new(2, 5);
        let r = a.checked_sub(b).unwrap();
        assert_eq!(r.start(), 6); // 10 - (5-1) = 10 - 4 = 6
        assert_eq!(r.end(), 18); // (20-1) - 2 + 1 = 19 - 2 + 1
    }

    #[test]
    fn checked_sub_underflow_start() {
        let a = crange_new(1, 10);
        let b = crange_new(5, 20);
        // a.start (1) - b_max (19) underflows
        assert_eq!(a.checked_sub(b), None);
    }

    #[test]
    fn checked_sub_underflow_end() {
        let a = crange_new(0, 3);
        let b = crange_new(5, 10);
        // a_max (2) - b.start (5) underflows
        assert_eq!(a.checked_sub(b), None);
    }

    #[test]
    fn checked_mul_basic() {
        let a = crange_new(2, 5); // values 2,3,4
        let b = crange_new(3, 7); // values 3,4,5,6
        let r = a.checked_mul(b).unwrap();
        assert_eq!(r.start(), 6); // 2*3
        assert_eq!(r.end(), 25); // 4*6 + 1
    }

    #[test]
    fn checked_mul_overflow() {
        // Use values large enough that their product overflows usize.
        // sqrt(usize::MAX) ≈ 4294967296 on 64-bit, so two values > that will overflow.
        let big = (usize::MAX as f64).sqrt() as usize + 1;
        let a = crange_new(big, big + 1); // singleton {big}
        let b = crange_new(big, big + 1); // singleton {big}
        // big * big overflows
        assert_eq!(a.checked_mul(b), None);
    }

    #[test]
    fn checked_mul_step_overflow() {
        let a = CRange::from_raw(0, usize::MAX, usize::MAX);
        let b = CRange::from_raw(0, 2, 3);
        // step * b.step = MAX * 2 overflows
        assert_eq!(a.checked_mul(b), None);
    }

    #[test]
    fn checked_div_basic() {
        let a = crange_new(0, 10);
        let b = crange_new(1, 3);
        let r = a.checked_div(b).unwrap();
        assert_eq!(r.start(), 0); // 0 / 2
        assert_eq!(r.end(), 10); // 9 / 1 + 1
    }

    #[test]
    fn checked_div_by_zero() {
        let a = crange_new(0, 10);
        let b = crange_new(0, 3); // includes 0
        assert_eq!(a.checked_div(b), None);
    }

    #[test]
    fn checked_div_b_max_zero() {
        // b_max = end - step = 1 - 1 = 0 → division by zero
        let a = crange_new(10, 20);
        let b = CRange::from_raw(0, 1, 1); // b_max = 0
        assert_eq!(a.checked_div(b), None);
    }

    #[test]
    fn checked_rem_basic() {
        let a = crange_new(0, 10); // values 0..9
        let b = crange_new(1, 3); // values 1,2
        let r = a.checked_rem(b).unwrap();
        assert_eq!(r.start(), 0); // 0 % 2 = 0
        assert_eq!(r.end(), 1); // 9 % 1 + 1 = 0 + 1
    }

    #[test]
    fn checked_rem_by_zero() {
        let a = crange_new(0, 10);
        let b = crange_new(0, 3); // includes 0
        assert_eq!(a.checked_rem(b), None);
    }

    #[test]
    fn checked_pow_basic() {
        let a = crange_new(2, 4); // values 2,3
        let b = crange_new(2, 4); // values 2,3
        let r = a.checked_pow(b).unwrap();
        assert_eq!(r.start(), 4); // 2^2
        assert_eq!(r.end(), 28); // 3^3 + 1 = 27 + 1
    }

    #[test]
    fn checked_pow_overflow() {
        let a = crange_new(2, 3);
        let b = crange_new(64, 65); // 2^64 overflows usize on 64-bit
        assert_eq!(a.checked_pow(b), None);
    }

    #[test]
    fn checked_pow_end_overflow() {
        // (usize::MAX - 1)^2 overflows usize
        let big = usize::MAX - 1;
        let a = crange_new(big, big + 1); // singleton {big} — big+1 = MAX, fits
        let b = crange_new(2, 3); // singleton {2}
        // big^2 overflows
        assert_eq!(a.checked_pow(b), None);
    }

    #[test]
    fn iterator_stops_on_overflow() {
        let r = CRange::from_raw(usize::MAX - 1, 2, usize::MAX);
        // First: start=MAX-1 (< MAX), yield MAX-1, then current = (MAX-1)+2 overflows → stop
        let mut it = r.into_iter();
        assert_eq!(it.next(), Some(usize::MAX - 1));
        assert_eq!(it.next(), None);
    }
}
