mod context;
pub mod macros;
mod pretty;
pub mod traversal;

pub use context::{Ctx, CtxValueTraversal, Set};
pub use pretty::{BoxAllocator, DocAllocator, DocBuilder, Pretty};
pub use traversal::Traversal;

/// Re-export im::ordmap iterator types for downstream crates
pub use im::ordmap::ConsumingIter as CtxConsumingIter;

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_log2_even_number() {
        assert_eq!(log2(12), (2, 3)); // 2^2 * 3 = 12
        assert_eq!(log2(8), (3, 1)); // 2^3 * 1 = 8
        assert_eq!(log2(16), (4, 1)); // 2^4 * 1 = 16
    }

    #[test]
    fn test_log2_odd_number() {
        assert_eq!(log2(7), (0, 7)); // 2^0 * 7 = 7
        assert_eq!(log2(9), (0, 9)); // 2^0 * 9 = 9
        assert_eq!(log2(1), (0, 1)); // 2^0 * 1 = 1
    }

    #[test]
    fn test_log2_zero() {
        assert_eq!(log2(0), (0, 0)); // Special case: 0
    }

    #[test]
    fn test_log2_power_of_two() {
        assert_eq!(log2(2), (1, 1)); // 2^1 * 1 = 2
        assert_eq!(log2(4), (2, 1)); // 2^2 * 1 = 4
        assert_eq!(log2(32), (5, 1)); // 2^5 * 1 = 32
        assert_eq!(log2(64), (6, 1)); // 2^6 * 1 = 64
    }

    #[test]
    fn test_log2_large_number() {
        assert_eq!(log2(96), (5, 3)); // 2^5 * 3 = 96
        assert_eq!(log2(1024), (10, 1)); // 2^10 * 1 = 1024
    }
}
