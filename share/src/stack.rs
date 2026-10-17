//! Growing the stack on demand in recursive passes, so their depth is bounded by the heap
//! instead of the thread's stack size (issue #252). This is rustc's `ensure_sufficient_stack`
//! pattern, on the same `stacker` crate.
//!
//! Walks that need only a node's children and bindings are iterative instead
//! (`lang::ast::ExpRef::walk`), and so is type inference. What still recurses is what builds
//! its result from context passed down the tree, lowering and the formatter: they call
//! [`ensure_sufficient_stack`], through `#[lang::stack_guard]`, in the function each child is
//! visited with.

/// Stack left below which a guarded call continues on a new segment: it must cover the deepest
/// call chain between two guarded calls. Measured by shrinking this until
/// `graph/tests/deep_nesting.rs` (`nested_blocks`) overflowed: it needs 20–24 KiB in debug
/// builds and 8–12 KiB in release builds, so this leaves at least 2.5× headroom in both.
const RED_ZONE: usize = 64 * 1024;

/// Size of each new segment, allocated on the heap and freed when the guarded call returns.
/// Many red zones deep, so a deep recursion switches segments rarely.
const SEGMENT: usize = 8 * 1024 * 1024;

/// Runs `f`, first moving to a fresh stack segment if less than [`RED_ZONE`] of the current
/// one is left.
#[inline]
pub fn ensure_sufficient_stack<R>(f: impl FnOnce() -> R) -> R {
    stacker::maybe_grow(RED_ZONE, SEGMENT, f)
}
