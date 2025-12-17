use ark_ec::{AffineRepr, CurveConfig, CurveGroup, PrimeGroup, VariableBaseMSM};
use ark_ec::scalar_mul::ScalarMul;
use ark_ff::{AdditiveGroup, PrimeField, UniformRand, Zero};
use ark_ff::biginteger::BigInt;
use rand::Rng;
use ark_serialize::{
    CanonicalSerialize, CanonicalDeserialize, CanonicalSerializeWithFlags, CanonicalDeserializeWithFlags,
    Compress, Valid, Validate, SerializationError, Flags};
use num_bigint::BigUint;
use zeroize::Zeroize;
use std::fmt;
use std::iter::Sum;
use ark_std::io::{Read, Write};
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign,
    BitOr, BitOrAssign, BitXor, BitXorAssign, Mul, MulAssign, Neg,
    Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign};
use std::str::FromStr;
use std::marker::PhantomData;

const NOCURVE_ERR: &str = "NoCurve is an empty curve with no points. It cannot be used for any operations.";

/// Represents the empty curve with no points.
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct NoCurve<F: PrimeField>(PhantomData<F>);

impl<F: PrimeField> UniformRand for NoCurve<F> {
    fn rand<R: Rng + ?Sized>(_: &mut R) -> Self {
        panic!("{}", NOCURVE_ERR)
    }
}

impl<F: PrimeField> Zeroize for NoCurve<F> {
    fn zeroize(&mut self) {
        panic!("{}", NOCURVE_ERR)
    }
}
impl<F: PrimeField> From<NoCurve<F>> for BigUint {
    fn from(_: NoCurve<F>) -> Self {
        panic!("{}", NOCURVE_ERR)
    }
}

impl<F: PrimeField> CanonicalSerialize for NoCurve<F> {
    fn serialize_with_mode<W: Write>(&self, _: W, _: Compress) -> Result<(), SerializationError> {
        panic!("{}", NOCURVE_ERR)
    }

    fn serialized_size(&self, _: Compress) -> usize {
        panic!("{}", NOCURVE_ERR)
    }
}

impl<F: PrimeField> Valid for NoCurve<F> {
    fn check(&self) -> Result<(), SerializationError> {
        panic!("{}", NOCURVE_ERR)
    }
}

impl<F: PrimeField> CanonicalDeserialize for NoCurve<F> {
    fn deserialize_with_mode<R: Read>(_: R, _: Compress, _: Validate) -> Result<Self, SerializationError> {
        panic!("{}", NOCURVE_ERR)
    }
}

impl<F: PrimeField> CanonicalSerializeWithFlags for NoCurve<F> {
    fn serialize_with_flags<W: Write, FF: Flags>(
        &self,
        _: W,
        _: FF,
    ) -> Result<(), SerializationError> {
        panic!("{}", NOCURVE_ERR)
    }
    fn serialized_size_with_flags<FF: Flags>(&self) -> usize {
        panic!("{}", NOCURVE_ERR)
    }
}

impl<F: PrimeField> CanonicalDeserializeWithFlags for NoCurve<F> {
    fn deserialize_with_flags<R: Read, FF: Flags>(_: R)-> Result<(Self, FF), SerializationError> {
        panic!("{}", NOCURVE_ERR)
    }
}

impl<F: PrimeField> Default for NoCurve<F> {
    fn default() -> Self {
        panic!("{}", NOCURVE_ERR)
    }
}
impl<F: PrimeField> fmt::Display for NoCurve<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "NoCurve<F>")
    }
}
impl<F: PrimeField> AsMut<[u64]> for NoCurve<F> {
    fn as_mut(&mut self) -> &mut [u64] {
        panic!("{}", NOCURVE_ERR)
    }
}
impl<F: PrimeField> AsRef<[u64]> for NoCurve<F> {
    fn as_ref(&self) -> &[u64] {
        panic!("{}", NOCURVE_ERR)
    }
}

impl<F: PrimeField> From<bool> for NoCurve<F> {
    /// Converts a value of type T into NoCurve<F>.
    fn from(_: bool) -> Self {
        panic!("{}", NOCURVE_ERR)
    }
}

impl<F: PrimeField> From<u128> for NoCurve<F> {
    /// Converts a value of type T into NoCurve<F>.
    fn from(_: u128) -> Self {
        panic!("{}", NOCURVE_ERR)
    }
}
impl<F: PrimeField> From<u64> for NoCurve<F> {
    /// Converts a value of type T into NoCurve<F>.
    fn from(_: u64) -> Self {
        panic!("{}", NOCURVE_ERR)
    }
}
impl<F: PrimeField> From<u32> for NoCurve<F> {
    /// Converts a value of type T into NoCurve<F>.
    fn from(_: u32) -> Self {
        panic!("{}", NOCURVE_ERR)
    }
}
impl<F: PrimeField> From<u16> for NoCurve<F> {
    /// Converts a value of type T into NoCurve<F>.
    fn from(_: u16) -> Self {
        panic!("{}", NOCURVE_ERR)
    }
}
impl<F: PrimeField> From<u8> for NoCurve<F> {
    /// Converts a value of type T into NoCurve<F>.
    fn from(_: u8) -> Self {
        panic!("{}", NOCURVE_ERR)
    }
}

impl<F: PrimeField> From<i128> for NoCurve<F> {
    /// Converts a value of type T into NoCurve<F>.
    fn from(_: i128) -> Self {
        panic!("{}", NOCURVE_ERR)
    }
}

impl<F: PrimeField> From<i64> for NoCurve<F> {
    /// Converts a value of type T into NoCurve<F>.
    fn from(_: i64) -> Self {
        panic!("{}", NOCURVE_ERR)
    }
}

impl<F: PrimeField> From<i32> for NoCurve<F> {
    /// Converts a value of type T into NoCurve<F>.
    fn from(_: i32) -> Self {
        panic!("{}", NOCURVE_ERR)
    }
}

impl<F: PrimeField> From<i16> for NoCurve<F> {
    /// Converts a value of type T into NoCurve<F>.
    fn from(_: i16) -> Self {
        panic!("{}", NOCURVE_ERR)
    }
}

impl<F: PrimeField> From<i8> for NoCurve<F> {
    /// Converts a value of type T into NoCurve<F>.
    fn from(_: i8) -> Self {
        panic!("{}", NOCURVE_ERR)
    }
}

impl<F: PrimeField> From<BigUint> for NoCurve<F> {
    /// Converts a value of type T into NoCurve<F>.
    fn from(_: BigUint) -> Self {
        panic!("{}", NOCURVE_ERR)
    }
}

impl<F: PrimeField> FromStr for NoCurve<F> {
    type Err = ();
    fn from_str(_: &str) -> Result<Self, Self::Err> {
        panic!("{}", NOCURVE_ERR)
    }
}

impl<F: PrimeField> BitXorAssign for NoCurve<F> {
    fn bitxor_assign(&mut self, _: Self) {
        panic!("{}", NOCURVE_ERR)
    }
}

impl<'a, F: PrimeField> BitXorAssign<&'a Self> for NoCurve<F> {
    fn bitxor_assign(&mut self, _: &'a Self) {
        panic!("{}", NOCURVE_ERR)
    }
}

impl<'a, F: PrimeField> BitXor<&'a Self> for NoCurve<F> {
    type Output = Self;
    fn bitxor(self, _: &'a Self) -> Self {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<F: PrimeField> BitXor for NoCurve<F> {
    type Output = Self;
    fn bitxor(self, _: Self) -> Self {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<F: PrimeField> BitAndAssign for NoCurve<F> {
    fn bitand_assign(&mut self, _: Self) {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<F: PrimeField> BitAnd for NoCurve<F> {
    type Output = Self;
    fn bitand(self, _: Self) -> Self {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<'a, F: PrimeField> BitAndAssign<&'a Self> for NoCurve<F> {
    fn bitand_assign(&mut self, _: &'a Self) {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<'a, F: PrimeField> BitAnd<&'a Self> for NoCurve<F> {
    type Output = Self;
    fn bitand(self, _: &'a Self) -> Self {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<F: PrimeField> BitOrAssign for NoCurve<F> {
    fn bitor_assign(&mut self, _: Self) {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<F: PrimeField> BitOr for NoCurve<F> {
    type Output = Self;
    fn bitor(self, _: Self) -> Self {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<'a, F: PrimeField> BitOrAssign<&'a Self> for NoCurve<F> {
    fn bitor_assign(&mut self, _: &'a Self) {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<'a, F: PrimeField> BitOr<&'a Self> for NoCurve<F> {
    type Output = Self;
    fn bitor(self, _: &'a Self) -> Self {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<F: PrimeField> ShrAssign<u32> for NoCurve<F> {
    fn shr_assign(&mut self, _: u32) {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<F: PrimeField> Shr<u32> for NoCurve<F> {
    type Output = Self;
    fn shr(self, _: u32) -> Self {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<F: PrimeField> ShlAssign<u32> for NoCurve<F> {
    fn shl_assign(&mut self, _: u32) {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<F: PrimeField> Shl<u32> for NoCurve<F> {
    type Output = Self;
    fn shl(self, _: u32) -> Self {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<F: PrimeField> Neg for NoCurve<F> {
    type Output = Self;
    fn neg(self) -> Self {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<F: PrimeField> Add for NoCurve<F> {
    type Output = Self;
    fn add(self, _: Self) -> Self {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<F: PrimeField> AddAssign for NoCurve<F> {
    fn add_assign(&mut self, _: Self) {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<'a, F: PrimeField> AddAssign<&'a Self> for NoCurve<F> {
    fn add_assign(&mut self, _: &'a Self) {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<'a, F: PrimeField> AddAssign<&'a mut Self> for NoCurve<F> {
    fn add_assign(&mut self, _: &'a mut Self) {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<'a, F: PrimeField> SubAssign<&'a mut Self> for NoCurve<F> {
    fn sub_assign(&mut self, _: &'a mut Self) {
        panic!("{}", NOCURVE_ERR);
    }
}


impl<'a, F: PrimeField> Add<&'a Self> for NoCurve<F> {
    type Output = Self;
    fn add(self, _: &'a Self) -> Self {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<'a, F: PrimeField> Add<&'a mut Self> for NoCurve<F> {
    type Output = Self;
    fn add(self, _: &'a mut Self) -> Self {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<F: PrimeField> SubAssign for NoCurve<F> {
    fn sub_assign(&mut self, _: Self) {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<'a, F: PrimeField> SubAssign<&'a Self> for NoCurve<F> {
    fn sub_assign(&mut self, _: &'a Self) {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<'a, F: PrimeField> Sub<&'a Self> for NoCurve<F> {
    type Output = Self;
    fn sub(self, _: &'a Self) -> Self {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<F: PrimeField> Sub for NoCurve<F> {
    type Output = Self;
    fn sub(self, _: Self) -> Self {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<'a, F: PrimeField> Sub<&'a mut Self> for NoCurve<F> {
    type Output = Self;
    fn sub(self, _: &'a mut Self) -> Self {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<F: PrimeField> Mul<F> for NoCurve<F> {
    type Output = Self;
    fn mul(self, _: F) -> Self {
        panic!("{}", NOCURVE_ERR);
    }
}
impl<'a, F: PrimeField> Mul<&'a F> for NoCurve<F> {
    type Output = Self;
    fn mul(self, _: &'a F) -> Self {
        panic!("{}", NOCURVE_ERR);
    }
}
impl<'a, F: PrimeField> Mul<&'a mut F> for NoCurve<F> {
    type Output = Self;
    fn mul(self, _: &'a mut F) -> Self {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<F: PrimeField> MulAssign<F> for NoCurve<F> {
    fn mul_assign(&mut self, _: F) {
        panic!("{}", NOCURVE_ERR);
    }
}
impl<'a, F: PrimeField> MulAssign<&'a F> for NoCurve<F> {
    fn mul_assign(&mut self, _: &'a F) {
        panic!("{}", NOCURVE_ERR);
    }
}
impl<'a, F: PrimeField> MulAssign<&'a mut F> for NoCurve<F> {
    fn mul_assign(&mut self, _: &'a mut F) {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<F: PrimeField> Zero for NoCurve<F> {
    fn zero() -> Self {
        panic!("{}", NOCURVE_ERR);
    }
    fn is_zero(&self) -> bool {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<F: PrimeField> Sum<NoCurve<F>> for NoCurve<F> {
    fn sum<I: Iterator<Item = NoCurve<F>>>(_: I) -> Self {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<F: PrimeField> From<NoCurve<F>> for BigInt<1> {
    fn from(_: NoCurve<F>) -> Self {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<F: PrimeField> From<BigInt<1>> for NoCurve<F> {
    fn from(_: BigInt<1>) -> Self {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<'a, F: PrimeField> Sum<&'a NoCurve<F>> for NoCurve<F> {
    fn sum<I: Iterator<Item = &'a NoCurve<F>>>(_: I) -> Self {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<F: PrimeField> AdditiveGroup for NoCurve<F> {
    type Scalar = F;
    const ZERO: Self = NoCurve(PhantomData);
}

impl<F: PrimeField> PrimeGroup for NoCurve<F> {
    type ScalarField = F;

    fn generator() -> Self {
        panic!("{}", NOCURVE_ERR)
    }
    fn mul_bigint(&self, _: impl AsRef<[u64]>) -> Self {
        panic!("{}", NOCURVE_ERR)
    }

    // Provided method
    fn mul_bits_be(&self, _: impl Iterator<Item = bool>) -> Self {
        panic!("{}", NOCURVE_ERR)
    }
}

impl<F: PrimeField> CurveConfig for NoCurve<F> {
    type BaseField = F;
    type ScalarField = F;

    const COFACTOR: &'static [u64] = &[];
    const COFACTOR_INV: Self::ScalarField = F::ZERO;
}

impl<F: PrimeField> ScalarMul for NoCurve<F> {
    type MulBase = NoCurve<F>;
    const NEGATION_IS_CHEAP: bool = true;

    // Required method
    fn batch_convert_to_mul_base(_: &[Self]) -> Vec<Self::MulBase> {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<F: PrimeField> VariableBaseMSM for NoCurve<F> {

    type Bucket = NoCurve<F>;
    const ZERO_BUCKET: Self::Bucket = NoCurve(PhantomData);
}

impl<F: PrimeField> AffineRepr for NoCurve<F> {
    type Config = NoCurve<F>;
    type ScalarField = F;
    type BaseField = F;
    type Group = NoCurve<F>;
    const ZERO: Self = NoCurve(PhantomData);
    const GENERATOR: Self = NoCurve(PhantomData);

    // Required methods
    fn xy(&self) -> Option<(Self::BaseField, Self::BaseField)> {
        panic!("{}", NOCURVE_ERR)
    }
    fn zero() -> Self {
        panic!("{}", NOCURVE_ERR)
    }
    fn generator() -> Self {
        panic!("{}", NOCURVE_ERR)
    }
    fn from_random_bytes(_: &[u8]) -> Option<Self> {
        panic!("{}", NOCURVE_ERR)
    }
    fn mul_bigint(&self, _: impl AsRef<[u64]>) -> Self::Group {
        panic!("{}", NOCURVE_ERR)
    }
    fn clear_cofactor(&self) -> Self {
        panic!("{}", NOCURVE_ERR)
    }
    fn mul_by_cofactor_to_group(&self) -> Self::Group {
        panic!("{}", NOCURVE_ERR)
    }
    fn is_zero(&self) -> bool {
        true
    }
}

impl<F: PrimeField> CurveGroup for NoCurve<F> {
    type Config = NoCurve<F>;
    type BaseField = F;
    type Affine = NoCurve<F>;
    type FullGroup = NoCurve<F>;

    // Required method
    fn normalize_batch(_: &[Self]) -> Vec<Self::Affine> {
        panic!("{}", NOCURVE_ERR);
    }
}

impl<'a, F: PrimeField, G: CurveGroup> From<&'a G> for NoCurve<F> {
    fn from(_: &'a G) -> Self {
        panic!("{}", NOCURVE_ERR)
    }
}
