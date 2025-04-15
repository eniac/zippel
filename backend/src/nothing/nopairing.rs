use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_ec::pairing::{MillerLoopOutput, Pairing, PairingOutput};
use std::marker::PhantomData;

pub use crate::nothing::NoField;

const NOPAIR_ERR: &str = "NoPairing is an empty pairing. It cannot be used for any operations.";

/// Sometimes we need a dummy pairing for non-pairing curves
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub struct NoPairing<G: CurveGroup>(PhantomData<G>);

impl<G: CurveGroup> Pairing for NoPairing<G> where G::BaseField : PrimeField {
    type BaseField = G::BaseField;
    type ScalarField = G::ScalarField;
    type G1 = G;
    type G1Affine = G::Affine;
    type G1Prepared = G;

    type G2 = G;
    type G2Affine = G::Affine;
    type G2Prepared = G;
    type TargetField = NoField;

    // Required methods
    fn multi_miller_loop(
        _: impl IntoIterator<Item = impl Into<Self::G1Prepared>>,
        _: impl IntoIterator<Item = impl Into<Self::G2Prepared>>,
    ) -> MillerLoopOutput<Self> {
        panic!("{}", NOPAIR_ERR);
    }

    fn final_exponentiation(
        _: MillerLoopOutput<Self>,
    ) -> Option<PairingOutput<Self>> {
        panic!("{}", NOPAIR_ERR);
    }
}
