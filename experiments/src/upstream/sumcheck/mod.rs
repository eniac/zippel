//! Hyperplonk sumcheck IOP, vendored from EspressoSystems/hyperplonk
//! `main` branch (subroutines + arithmetic + transcript crates).
//! Ported to arkworks 0.6 — the imports are the only place arkworks 0.4
//! vs 0.6 differed; the algorithm code is verbatim.
//!
//! Only the items zippel sumcheck.rs::native_side actually needs are
//! vendored: the `SumCheck` trait + its `PolyIOP<F>` impl,
//! `VirtualPolynomial`, `VPAuxInfo`, and `IOPTranscript`. We skip
//! `arithmetic::univariate_polynomial`, `arithmetic::bench`, the rest
//! of `subroutines::poly_iop::*`, and `subroutines::pcs::*` since
//! sumcheck doesn't reach them.

pub mod arithmetic;
pub mod poly_iop;
pub mod transcript;
