//! Polynomial type dispatcher.
//!
//! The concrete `Poly` (and its `PolyCursor`) is re-exported from one
//! of two backend modules, chosen at compile time by the
//! `linked_list_poly` Cargo feature:
//!
//! * **Default** — [`poly_vec`](crate::poly::poly_vec): parallel
//!   `Vec<Coeff>` + `Vec<MonoTerm>` with a `head` cursor. Matches
//!   mathicgb's flat-array shape; ADR-001 has the motivation and the
//!   staging-5101449 profile evidence (62.6 % memmove pre-fix).
//! * **`--features linked_list_poly`** — [`poly_list`](crate::poly::poly_list):
//!   singly linked list of `Node` records, closer to Singular's
//!   `spolyrec` storage. ADR-014 covers the decision to keep this
//!   second backend available for A/B comparison and future
//!   Singular-style splicing optimisations, while the flat-array
//!   backend remains the default.
//!
//! Callers everywhere write `Poly`, `&Poly`, `Vec<Poly>` — the feature
//! flag decides which struct they mean. The public method surface is
//! identical across both backends (see `poly_vec.rs` / `poly_list.rs`
//! for the per-backend implementations).

#[cfg(all(feature = "linked_list_poly_pool", not(feature = "linked_list_poly")))]
compile_error!("feature `linked_list_poly_pool` requires `linked_list_poly`");

#[cfg(not(feature = "linked_list_poly"))]
mod poly_vec;
#[cfg(not(feature = "linked_list_poly"))]
pub use poly_vec::{Poly, PolyCursor};

#[cfg(feature = "linked_list_poly")]
mod node_pool;
#[cfg(feature = "linked_list_poly")]
mod poly_list;
#[cfg(feature = "linked_list_poly")]
pub use poly_list::{Poly, PolyCursor};
