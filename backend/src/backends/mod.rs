//! [`Backend`]: the field, groups and pairing a protocol runs over, the keys a backend
//! keeps for reused operands, and the backends Zippel ships: arkworks ([`arkworks`]),
//! arkworks scalars over dalek's Ristretto ([`hybrid`]), and the zkcrypto `ff`/`group`
//! crates ([`ff_group`]).

/// The arkworks backends.
pub mod arkworks;
/// The zkcrypto `ff`/`group` backends.
pub mod ff_group;
/// The hybrid backend: arkworks scalars over curve25519-dalek's Ristretto.
pub mod hybrid;
/// Keys: point vectors reused as operands, and what a backend keeps for them.
pub mod keys;
/// Placeholder group and pairing for field-only or pairing-free backends.
pub mod nothing;

pub use arkworks::{
    ArkBls12_381, ArkBn254, ArkCurve25519, ArkEd25519, ArkMNT4_298, ArkPallas, ArkSecp256k1,
    ArkVesta,
};
pub use ff_group::{DalekRistretto, PastaPallas};
pub use hybrid::ArkFrRistretto;
pub use keys::{Key, Keyed, NoKey};

use crate::value::points::Points;

/// First-source-group points with any data the backend keeps for them as a key
/// ([`Backend::G1Key`]).
pub type G1Points<C> = Points<G1Affine<C>, <C as Backend>::G1Key>;

/// Second-source-group points with any data the backend keeps for them as a key
/// ([`Backend::G2Key`]).
pub type G2Points<C> = Points<G2Affine<C>, <C as Backend>::G2Key>;

use crate::algebra::{Field, Group, Pairing};
use std::fmt;
use std::hash::Hash;

/// The algebra a protocol runs over: a scalar field, two source groups over it and a
/// pairing between them. A backend without a pairing sets `G2 = G1` and `P` to
/// [`NoPairing`]; one with no group at all (a field-only test backend) fills both with
/// [`NoGroup`].
pub trait Backend:
    Clone + Copy + Send + Sync + 'static + Eq + PartialEq + fmt::Display + fmt::Debug + Hash
{
    /// The scalar field; every Zippel `Scalar` value lives here.
    type F: Field;
    /// The first source group.
    type G1: Group<Scalar = Self::F>;
    /// The second source group; `G1` for a pairing-free backend.
    type G2: Group<Scalar = Self::F>;
    /// The pairing.
    type P: Pairing<G1 = Self::G1, G2 = Self::G2>;
    /// What this backend keeps for first-source-group points declared as a key
    /// (see [`crate::keys`]); [`NoKey`] for nothing.
    type G1Key: Key<G1Affine<Self>>;
    /// What this backend keeps for second-source-group points declared as a key.
    type G2Key: Key<G2Affine<Self>>;
    /// The backend the static analyses run on in place of this one: the arkworks
    /// backend with the same scalar field and the same capabilities (`Self` for an
    /// arkworks-field backend). The analyses see only the field, encoding group elements
    /// by their discrete logs, and their Gröbner-basis engines need an arkworks field.
    ///
    /// Temporary: remove this, and analyze every backend directly, once ark-gb handles an
    /// arbitrary field (<https://github.com/eniac/zippel/issues/260>).
    type Analysis: Backend<F: ark_ff::PrimeField>;
    /// Whether `P` is a real pairing; lowering rejects pairings and target-group values
    /// otherwise.
    const HAS_PAIRING: bool;
    /// Whether `G1` and `G2` are real groups; lowering rejects group values otherwise.
    const HAS_GROUP: bool = true;

    /// `Σ scalars[i]·points[i]`. The default ignores the points' key; a backend whose
    /// key speeds this up overrides it and reads [`Points::key`].
    ///
    /// # Panics
    /// Panics if the two have different lengths.
    fn msm_g1(points: &G1Points<Self>, scalars: &[Self::F]) -> Self::G1 {
        Self::G1::msm(points, scalars)
    }

    /// `Σ scalars[i]·points[i]`; see [`Backend::msm_g1`].
    ///
    /// # Panics
    /// Panics if the two have different lengths.
    fn msm_g2(points: &G2Points<Self>, scalars: &[Self::F]) -> Self::G2 {
        Self::G2::msm(points, scalars)
    }

    /// `Σ e(g1[i], g2[i])`. The default, [`plain_multi_pairing`], ignores `g2`'s key.
    ///
    /// # Panics
    /// Panics if the two have different lengths.
    fn multi_pairing(g1: &[Self::G1], g2: &G2Points<Self>) -> GT<Self> {
        plain_multi_pairing::<Self>(g1, g2)
    }
}

/// `Σ e(g1[i], g2[i])` by the backend's pairing, with no key.
///
/// # Panics
/// Panics if the two have different lengths.
pub fn plain_multi_pairing<C: Backend>(g1: &[C::G1], g2: &[G2Affine<C>]) -> GT<C> {
    let g2: Vec<C::G2> = g2.iter().map(|&p| p.into()).collect();
    <C::P as Pairing>::multi_pairing(g1, &g2)
}

/// The target group of backend `C`.
pub type GT<C> = <<C as Backend>::P as Pairing>::GT;
/// The normalized (affine) form of backend `C`'s first source group.
pub type G1Affine<C> = <<C as Backend>::G1 as Group>::Affine;
/// The normalized (affine) form of backend `C`'s second source group.
pub type G2Affine<C> = <<C as Backend>::G2 as Group>::Affine;
