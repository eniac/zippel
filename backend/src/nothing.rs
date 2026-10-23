//! Placeholders for what a backend lacks: [`NoGroup`], a group with no elements, fills
//! the group slots of a field-only backend and the target group of a pairing-free one;
//! [`NoPairing`] is the pairing of a pairing-free backend. Lowering rejects every
//! operation that would need them (see `Backend::HAS_GROUP`, `Backend::HAS_PAIRING`).

use crate::algebra::{Field, Group, Pairing};
use rand::Rng;
use std::convert::Infallible;
use std::fmt;
use std::marker::PhantomData;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

const NO_GROUP: &str = "the backend has no such group; lowering rejects its operations";

/// A group with no elements over `F`: a value of it cannot exist, so every method taking
/// one is unreachable, and those making one panic.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct NoGroup<F>(Infallible, PhantomData<F>);

impl<F> NoGroup<F> {
    fn absurd(&self) -> ! {
        match self.0 {}
    }
}

impl<F> fmt::Debug for NoGroup<F> {
    fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result {
        self.absurd()
    }
}

impl<F> fmt::Display for NoGroup<F> {
    fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result {
        self.absurd()
    }
}

macro_rules! absurd_op {
    ($trait:ident, $method:ident, $rhs:ty) => {
        impl<F: Field> $trait<$rhs> for NoGroup<F> {
            type Output = Self;
            fn $method(self, _: $rhs) -> Self {
                self.absurd()
            }
        }
    };
    ($trait:ident, $method:ident, $rhs:ty, assign) => {
        impl<F: Field> $trait<$rhs> for NoGroup<F> {
            fn $method(&mut self, _: $rhs) {
                self.absurd()
            }
        }
    };
}

absurd_op!(Add, add, Self);
absurd_op!(Sub, sub, Self);
absurd_op!(Mul, mul, F);
absurd_op!(AddAssign, add_assign, Self, assign);
absurd_op!(SubAssign, sub_assign, Self, assign);
absurd_op!(MulAssign, mul_assign, F, assign);

impl<F: Field> Neg for NoGroup<F> {
    type Output = Self;
    fn neg(self) -> Self {
        self.absurd()
    }
}

impl<F: Field> Group for NoGroup<F> {
    type Scalar = F;
    type Affine = Self;

    fn zero() -> Self {
        panic!("{NO_GROUP}")
    }

    fn generator() -> Self {
        panic!("{NO_GROUP}")
    }

    fn is_zero(&self) -> bool {
        self.absurd()
    }

    fn rand<R: Rng + ?Sized>(_: &mut R) -> Self {
        panic!("{NO_GROUP}")
    }

    fn add_affine(&mut self, _: &Self) {
        self.absurd()
    }

    fn normalize(&self) -> Self {
        self.absurd()
    }

    fn normalize_batch(v: &[Self]) -> Vec<Self> {
        v.to_vec()
    }

    fn batch_mul(&self, _: &[F]) -> Vec<Self> {
        self.absurd()
    }

    fn msm(bases: &[Self], _: &[F]) -> Self {
        bases
            .first()
            .map_or_else(|| panic!("{NO_GROUP}"), |g| g.absurd())
    }

    fn write_bytes(&self, _: &mut Vec<u8>) {
        self.absurd()
    }

    fn write_affine_bytes(a: &Self, _: &mut Vec<u8>) {
        a.absurd()
    }
}

/// The pairing of a pairing-free backend over group `G`: its target group has no elements.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NoPairing<G>(PhantomData<G>);

impl<G: Group> Pairing for NoPairing<G> {
    type G1 = G;
    type G2 = G;
    type GT = NoGroup<G::Scalar>;
    type G2Prepared = Infallible;

    fn prepare_g2(_: &G::Affine) -> Infallible {
        panic!("{NO_GROUP}")
    }

    fn pairing(_: &G, _: &G) -> Self::GT {
        panic!("{NO_GROUP}")
    }

    fn multi_pairing(_: &[G], _: &[G]) -> Self::GT {
        panic!("{NO_GROUP}")
    }

    fn multi_pairing_prepared(_: &[G], b: &[Infallible]) -> Self::GT {
        b.first()
            .map_or_else(|| panic!("{NO_GROUP}"), |&x| match x {})
    }
}
