#![feature(btree_extract_if)]
mod context;
mod pretty;
pub mod traversal;

pub use pretty::{Pretty, DocAllocator, DocBuilder, BoxAllocator};
pub use context::{Ctx, Set};
pub use traversal::Traversal;

/// Logarithm with "remainder"
/// ex: log2(12) = (2, 3)    [means 2^2 * 3]
///     log(-72) = (3, -9)   [means 2^3 * (-9)]
pub fn log2(u: usize) -> (usize, usize) {
    let mut exp = 0;
    let mut um = u;

    while um % 2 == 0 && um > 0 {
        exp += 1;
        um /= 2;
    }
    (exp, um)
}
