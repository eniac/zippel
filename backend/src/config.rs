//! [`Backend`]: the field, groups and pairing a protocol runs over, and the backends
//! Zippel ships (all arkworks).

use std::fmt;
use std::hash::Hash;
use std::marker::PhantomData;

use ark_ec::bls12::Bls12;
use ark_ec::mnt4::MNT4;
use ark_ec::models::bn::Bn;
use ark_ff::{Fp64, MontBackend, MontConfig, PrimeField};

use crate::algebra::{Field, Group, Pairing};
use crate::ark::ArkPairing;
use crate::nothing::{NoGroup, NoPairing};

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
    /// Whether `P` is a real pairing; lowering rejects pairings and target-group values
    /// otherwise.
    const HAS_PAIRING: bool;
    /// Whether `G1` and `G2` are real groups; lowering rejects group values otherwise.
    const HAS_GROUP: bool = true;
}

/// The target group of backend `C`.
pub type GT<C> = <<C as Backend>::P as Pairing>::GT;
/// The normalized (affine) form of backend `C`'s first source group.
pub type G1Affine<C> = <<C as Backend>::G1 as Group>::Affine;
/// The normalized (affine) form of backend `C`'s second source group.
pub type G2Affine<C> = <<C as Backend>::G2 as Group>::Affine;

/// The BLS12-381 pairing-friendly backend.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkBls12_381 {}

/// `BN254` pairing-friendly backend, the curve used by most Ethereum tooling.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkBn254 {}

/// `MNT4-298` pairing-friendly backend, a cycle-friendly curve for recursion.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkMNT4_298 {}

/// Curve25519 backend; a prime-order Edwards group with no pairing available.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkCurve25519 {}

/// `secp256k1` backend; a prime-order Weierstrass group with no pairing available.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkSecp256k1 {}

/// Pallas backend, the first half of the Pasta cycle; no pairing available.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkPallas {}

/// Vesta backend, the second half of the Pasta cycle; no pairing available.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkVesta {}

/// Ed25519 backend; a prime-order Edwards group with no pairing available.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkEd25519 {}

/// Field-only backend over an arbitrary `PrimeField`, with [`NoGroup`] in the group
/// slots.
///
/// Used for tiny-modulus tests where group arithmetic is irrelevant.
#[derive(Clone, Debug, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArkFieldN<F: PrimeField>(PhantomData<F>);

/// Field-only backend over the 17-element prime field; used in small unit tests.
pub type ArkField17 = ArkFieldN<F17>;
/// Field-only backend over the 65537-element prime field; used in small unit tests.
pub type ArkField65537 = ArkFieldN<F65537>;

impl fmt::Display for ArkBls12_381 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "BLS12-381")
    }
}
impl fmt::Display for ArkBn254 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "BN254")
    }
}
impl fmt::Display for ArkMNT4_298 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "MNT4-298")
    }
}
impl fmt::Display for ArkCurve25519 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Curve25519")
    }
}
impl fmt::Display for ArkSecp256k1 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "SECP256K1")
    }
}

impl fmt::Display for ArkPallas {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Pallas")
    }
}
impl fmt::Display for ArkVesta {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Vesta")
    }
}
impl fmt::Display for ArkEd25519 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Ed25519")
    }
}
impl<F: PrimeField> fmt::Display for ArkFieldN<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Field<{}>", F::MODULUS)
    }
}

impl Backend for ArkBls12_381 {
    type F = ark_bls12_381::Fr;
    type G1 = ark_bls12_381::G1Projective;
    type G2 = ark_bls12_381::G2Projective;
    type P = ArkPairing<Bls12<ark_bls12_381::Config>>;
    const HAS_PAIRING: bool = true;
}

impl Backend for ArkBn254 {
    type F = ark_bn254::Fr;
    type G1 = ark_bn254::G1Projective;
    type G2 = ark_bn254::G2Projective;
    type P = ArkPairing<Bn<ark_bn254::Config>>;
    const HAS_PAIRING: bool = true;
}

impl Backend for ArkMNT4_298 {
    type F = ark_mnt4_298::Fr;
    type G1 = ark_mnt4_298::G1Projective;
    type G2 = ark_mnt4_298::G2Projective;
    type P = ArkPairing<MNT4<ark_mnt4_298::Config>>;
    const HAS_PAIRING: bool = true;
}

impl Backend for ArkCurve25519 {
    type F = ark_curve25519::Fr;
    type G1 = ark_curve25519::EdwardsProjective;
    type G2 = ark_curve25519::EdwardsProjective;
    type P = NoPairing<ark_curve25519::EdwardsProjective>;
    const HAS_PAIRING: bool = false;
}

impl Backend for ArkSecp256k1 {
    type F = ark_secp256k1::Fr;
    type G1 = ark_secp256k1::Projective;
    type G2 = ark_secp256k1::Projective;
    type P = NoPairing<ark_secp256k1::Projective>;
    const HAS_PAIRING: bool = false;
}

impl Backend for ArkPallas {
    type F = ark_pallas::Fr;
    type G1 = ark_pallas::Projective;
    type G2 = ark_pallas::Projective;
    type P = NoPairing<ark_pallas::Projective>;
    const HAS_PAIRING: bool = false;
}

impl Backend for ArkVesta {
    type F = ark_vesta::Fr;
    type G1 = ark_vesta::Projective;
    type G2 = ark_vesta::Projective;
    type P = NoPairing<ark_vesta::Projective>;
    const HAS_PAIRING: bool = false;
}

impl Backend for ArkEd25519 {
    type F = ark_ed25519::Fr;
    type G1 = ark_ed25519::EdwardsProjective;
    type G2 = ark_ed25519::EdwardsProjective;
    type P = NoPairing<ark_ed25519::EdwardsProjective>;
    const HAS_PAIRING: bool = false;
}

impl<F: PrimeField> Backend for ArkFieldN<F> {
    type F = F;
    type G1 = NoGroup<F>;
    type G2 = NoGroup<F>;
    type P = NoPairing<NoGroup<F>>;
    const HAS_PAIRING: bool = false;
    const HAS_GROUP: bool = false;
}

/// Montgomery parameters for the 17-element prime field (modulus 17, generator 3).
#[derive(MontConfig, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[modulus = "17"]
#[generator = "3"]
pub struct F17Config;
/// Arkworks Montgomery backend instantiated with `F17Config` over one 64-bit limb.
pub type Mont17 = MontBackend<F17Config, 1>;

/// The 17-element prime field, the smallest field used by backend unit tests.
pub type F17 = Fp64<Mont17>;

/// Montgomery parameters for the 65537-element prime field (modulus 65537,
/// generator 3).
///
/// 65536 is a power of two, so this field admits radix-2 FFT domains up to
/// size 65536, unlike `F17Config`.
#[derive(MontConfig, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[modulus = "65537"]
#[generator = "3"]
pub struct F65537Config;
/// Arkworks Montgomery backend instantiated with `F65537Config` over one 64-bit limb.
pub type Mont65537 = MontBackend<F65537Config, 1>;
/// The 65537-element prime field, used where FFT-capable test domains are needed.
pub type F65537 = Fp64<Mont65537>;
