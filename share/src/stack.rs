//! Growing the stack on demand in recursive passes, so their depth is bounded by the heap
//! instead of the thread's stack size (issue #252). This is rustc's `ensure_sufficient_stack`
//! pattern, on the same `stacker` crate.
//!
//! Call [`ensure_sufficient_stack`] at a point every level of a recursive walk passes through:
//! for an AST pass, the `Spanned<T>` impl or the function each child is visited with.

/// Stack left below which a guarded call continues on a new segment. Generous because debug
/// builds keep large frames between guards (a match dispatcher plus its arm and the `im` map
/// nodes it inserts into).
const RED_ZONE: usize = 1024 * 1024;

/// Size of each new segment, allocated on the heap and freed when the guarded call returns.
const SEGMENT: usize = 8 * 1024 * 1024;

/// Runs `f`, first moving to a fresh stack segment if less than [`RED_ZONE`] of the current
/// one is left.
#[inline]
pub fn ensure_sufficient_stack<R>(f: impl FnOnce() -> R) -> R {
    stacker::maybe_grow(RED_ZONE, SEGMENT, f)
}
