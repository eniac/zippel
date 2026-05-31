//! Thread-local `Node` allocator for the [`poly_list`](super::poly_list)
//! backend.
//!
//! SIMPLIFIED: Due to generalization over `F: Field`, the thread_local
//! pool cannot be generic. This implementation now always uses the
//! Box::new/Box::from_raw forwarder approach for all configurations.
//! The pool optimization has been removed to support generic fields.

use std::ptr::NonNull;

use crate::field::Field;
use crate::monomial::Monomial;

use super::poly_list::Node;

/// Allocate a `Node` via `Box::new`; hand back the raw pointer.
pub(super) fn alloc<F: Field + Copy, M: Monomial<F, W>, const W: usize>(
    coeff: F,
    mono: M,
    next: Option<NonNull<Node<F, M>>>,
) -> NonNull<Node<F, M>> {
    let b = Box::new(Node { coeff, mono, next });
    // SAFETY: `Box::into_raw` never returns null.
    unsafe { NonNull::new_unchecked(Box::into_raw(b)) }
}

/// # Safety
///
/// * `ptr` must point to a `Node` that is no longer reachable from
///   any live `Poly`.
/// * The caller must have already `take()`-d `ptr`'s `next` field
///   (or equivalently, cleared it). We do **not** chain-free to
///   avoid stack-recursive drop on long lists.
/// * `ptr` must have been obtained from an earlier `alloc` call.
pub(super) unsafe fn dealloc<F: Field + Copy, M: Monomial<F, W>, const W: usize>(
    ptr: NonNull<Node<F, M>>,
) {
    // Safety-checked by contract above: reclaim the `Box` and drop
    // it. The implicit drop walks only this one node because the
    // caller has already cleared `next`.
    unsafe {
        drop(Box::from_raw(ptr.as_ptr()));
    }
}
