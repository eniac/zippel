//! Frontend of the analyses crate: order-free polynomials, monomial-ordering
//! data, and the transitive closure.
//!
//! Nothing here depends on a monomial ordering for its *semantics*. Ordering is
//! runtime data ([`MonoOrder`]) handed to the backend when a Gröbner basis or a
//! reduction is requested.

pub mod monomial;
pub mod order;
pub mod polynomial;
pub mod trans_clos;

pub use monomial::Monomial;
pub use order::{Block, BlockKind, MonoOrder, UnsupportedMonoOrder};
pub use polynomial::Polynomial;
pub use trans_clos::TransClos;
