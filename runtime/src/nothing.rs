use ark_ec::{AffineRepr, CurveConfig, CurveGroup, PrimeGroup, VariableBaseMSM};
use ark_ec::scalar_mul::ScalarMul;
use ark_ff::{SqrtPrecomputation, AdditiveGroup, CyclotomicMultSubgroup, FftField, Field, LegendreSymbol, One, PrimeField, UniformRand, Zero};
use ark_ff::biginteger::BigInt;
use rand::Rng;
use ark_serialize::{
    CanonicalSerialize, CanonicalDeserialize, CanonicalSerializeWithFlags, CanonicalDeserializeWithFlags,
    Compress, Valid, Validate, SerializationError, Flags};
use num_bigint::BigUint;
use zeroize::Zeroize;
use std::fmt;
use std::iter::{Product, Sum};
use ark_std::io::{Read, Write};
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign,
    BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign, Mul, MulAssign, Neg,
    Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign};
use std::str::FromStr;

/// Represents the empty curve with no points.
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct Nothing {}

impl Nothing {
    /// Creates a new instance of `Nothing`.
    pub fn new() -> Self {
        Nothing{}
    }
}
impl UniformRand for Nothing {
    fn rand<R: Rng + ?Sized>(_: &mut R) -> Self {
        Nothing{}
    }
}

impl Zeroize for Nothing {
    fn zeroize(&mut self) {
        *self = Nothing{};
    }
}
impl From<Nothing> for BigUint {
    fn from(_: Nothing) -> Self {
        BigUint::from(0u32)
    }
}

impl CanonicalSerialize for Nothing {
    fn serialize_with_mode<W: Write>(&self, _: W, _: Compress) -> Result<(), SerializationError> {
        Ok(())
    }

    fn serialized_size(&self, _: Compress) -> usize {
        0
    }
}

impl Valid for Nothing {
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }
}

impl CanonicalDeserialize for Nothing {
    fn deserialize_with_mode<R: Read>(_: R, _: Compress, _: Validate) -> Result<Self, SerializationError> {
        Ok(Nothing{})
    }
}

impl CanonicalSerializeWithFlags for Nothing {
    fn serialize_with_flags<W: Write, FF: Flags>(
        &self,
        _: W,
        _: FF,
    ) -> Result<(), SerializationError> {
        Ok(())
    }
    fn serialized_size_with_flags<FF: Flags>(&self) -> usize {
        0
    }
}

impl CanonicalDeserializeWithFlags for Nothing {
    fn deserialize_with_flags<R: Read, FF: Flags>(_: R)-> Result<(Self, FF), SerializationError> {
        Ok((Nothing{}, FF::default()))
    }
}

impl Default for Nothing {
    fn default() -> Self {
        Nothing{}
    }
}
impl fmt::Display for Nothing {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Nothing")
    }
}
impl AsMut<[u64]> for Nothing {
    fn as_mut(&mut self) -> &mut [u64] {
        &mut []
    }
}
impl AsRef<[u64]> for Nothing {
    fn as_ref(&self) -> &[u64] {
        &[]
    }
}

impl From<bool> for Nothing {
    /// Converts a value of type T into Nothing.
    fn from(_: bool) -> Self {
        Nothing{}
    }
}

impl From<u128> for Nothing {
    /// Converts a value of type T into Nothing.
    fn from(_: u128) -> Self {
        Nothing{}
    }
}
impl From<u64> for Nothing {
    /// Converts a value of type T into Nothing.
    fn from(_: u64) -> Self {
        Nothing{}
    }
}
impl From<u32> for Nothing {
    /// Converts a value of type T into Nothing.
    fn from(_: u32) -> Self {
        Nothing{}
    }
}
impl From<u16> for Nothing {
    /// Converts a value of type T into Nothing.
    fn from(_: u16) -> Self {
        Nothing{}
    }
}
impl From<u8> for Nothing {
    /// Converts a value of type T into Nothing.
    fn from(_: u8) -> Self {
        Nothing{}
    }
}

impl From<i128> for Nothing {
    /// Converts a value of type T into Nothing.
    fn from(_: i128) -> Self {
        Nothing{}
    }
}

impl From<i64> for Nothing {
    /// Converts a value of type T into Nothing.
    fn from(_: i64) -> Self {
        Nothing{}
    }
}

impl From<i32> for Nothing {
    /// Converts a value of type T into Nothing.
    fn from(_: i32) -> Self {
        Nothing{}
    }
}

impl From<i16> for Nothing {
    /// Converts a value of type T into Nothing.
    fn from(_: i16) -> Self {
        Nothing{}
    }
}

impl From<i8> for Nothing {
    /// Converts a value of type T into Nothing.
    fn from(_: i8) -> Self {
        Nothing{}
    }
}

impl From<BigUint> for Nothing {
    /// Converts a value of type T into Nothing.
    fn from(_: BigUint) -> Self {
        Nothing{}
    }
}

impl FromStr for Nothing {
    type Err = ();
    fn from_str(_: &str) -> Result<Self, Self::Err> {
        Ok(Nothing{})
    }
}

impl BitXorAssign for Nothing {
    fn bitxor_assign(&mut self, _: Self) {
        // No operation
    }
}

impl<'a> BitXorAssign<&'a Self> for Nothing {
    fn bitxor_assign(&mut self, _: &'a Self) {
        // No operation
    }
}

impl<'a> BitXor<&'a Self> for Nothing {
    type Output = Self;
    fn bitxor(self, _: &'a Self) -> Self {
        Nothing{}
    }
}

impl BitXor for Nothing {
    type Output = Self;
    fn bitxor(self, _: Self) -> Self {
        Nothing{}
    }
}

impl BitAndAssign for Nothing {
    fn bitand_assign(&mut self, _: Self) {
        // No operation
    }
}

impl BitAnd for Nothing {
    type Output = Self;
    fn bitand(self, _: Self) -> Self {
        Nothing{}
    }
}

impl<'a> BitAndAssign<&'a Self> for Nothing {
    fn bitand_assign(&mut self, _: &'a Self) {
        // No operation
    }
}

impl<'a> BitAnd<&'a Self> for Nothing {
    type Output = Self;
    fn bitand(self, _: &'a Self) -> Self {
        Nothing{}
    }
}

impl BitOrAssign for Nothing {
    fn bitor_assign(&mut self, _: Self) {
        // No operation
    }
}

impl BitOr for Nothing {
    type Output = Self;
    fn bitor(self, _: Self) -> Self {
        Nothing{}
    }
}

impl<'a> BitOrAssign<&'a Self> for Nothing {
    fn bitor_assign(&mut self, _: &'a Self) {
        // No operation
    }
}

impl<'a> BitOr<&'a Self> for Nothing {
    type Output = Self;
    fn bitor(self, _: &'a Self) -> Self {
        Nothing{}
    }
}

impl ShrAssign<u32> for Nothing {
    fn shr_assign(&mut self, _: u32) {
        // No operation
    }
}

impl Shr<u32> for Nothing {
    type Output = Self;
    fn shr(self, _: u32) -> Self {
        Nothing{}
    }
}

impl ShlAssign<u32> for Nothing {
    fn shl_assign(&mut self, _: u32) {
        // No operation
    }
}

impl Shl<u32> for Nothing {
    type Output = Self;
    fn shl(self, _: u32) -> Self {
        Nothing{}
    }
}

impl Neg for Nothing {
    type Output = Self;
    fn neg(self) -> Self {
        Nothing{}
    }
}

impl Add for Nothing {
    type Output = Self;
    fn add(self, _: Self) -> Self {
        Nothing{}
    }
}

impl AddAssign for Nothing {
    fn add_assign(&mut self, _: Self) {
        // No operation
    }
}

impl<'a> AddAssign<&'a Self> for Nothing {
    fn add_assign(&mut self, _: &'a Self) {
        // No operation
    }
}

impl<'a> AddAssign<&'a mut Self> for Nothing {
    fn add_assign(&mut self, _: &'a mut Self) {
        // No operation
    }
}

impl<'a> SubAssign<&'a mut Self> for Nothing {
    fn sub_assign(&mut self, _: &'a mut Self) {
        // No operation
    }
}


impl<'a> Add<&'a Self> for Nothing {
    type Output = Self;
    fn add(self, _: &'a Self) -> Self {
        Nothing{}
    }
}

impl<'a> Add<&'a mut Self> for Nothing {
    type Output = Self;
    fn add(self, _: &'a mut Self) -> Self {
        Nothing{}
    }
}

impl SubAssign for Nothing {
    fn sub_assign(&mut self, _: Self) {
        // No operation
    }
}

impl<'a> SubAssign<&'a Self> for Nothing {
    fn sub_assign(&mut self, _: &'a Self) {
        // No operation
    }
}

impl<'a> Sub<&'a Self> for Nothing {
    type Output = Self;
    fn sub(self, _: &'a Self) -> Self {
        Nothing{}
    }
}

impl Sub for Nothing {
    type Output = Self;
    fn sub(self, _: Self) -> Self {
        Nothing{}
    }
}

impl<'a> Sub<&'a mut Self> for Nothing {
    type Output = Self;
    fn sub(self, _: &'a mut Self) -> Self {
        Nothing{}
    }
}

impl Mul for Nothing {
    type Output = Self;
    fn mul(self, _: Self) -> Self {
        Nothing{}
    }
}
impl<'a> Mul<&'a mut Self> for Nothing {
    type Output = Self;
    fn mul(self, _: &'a mut Self) -> Self {
        Nothing{}
    }
}
impl<'a> MulAssign<&'a mut Self> for Nothing {
    fn mul_assign(&mut self, _: &'a mut Self) {
        // No operation
    }
}
impl MulAssign for Nothing {
    fn mul_assign(&mut self, _: Self) {
        // No operation
    }
}
impl<'a> MulAssign<&'a Self> for Nothing {
    fn mul_assign(&mut self, _: &'a Self) {
        // No operation
    }
}
impl<'a> Mul<&'a Self> for Nothing {
    type Output = Self;
    fn mul(self, _: &'a Self) -> Self {
        Nothing{}
    }
}
impl Div for Nothing {
    type Output = Self;
    fn div(self, _: Self) -> Self {
        Nothing{}
    }
}

impl<'a> Div<&'a Self> for Nothing {
    type Output = Self;
    fn div(self, _: &'a Self) -> Self {
        Nothing{}
    }
}

impl<'a> Div<&'a mut Self> for Nothing {
    type Output = Self;
    fn div(self, _: &'a mut Self) -> Self {
        Nothing{}
    }
}

impl DivAssign for Nothing {
    fn div_assign(&mut self, _: Self) {
        // No operation
    }
}

impl<'a> DivAssign<&'a Self> for Nothing {
    fn div_assign(&mut self, _: &'a Self) {
        // No operation
    }
}
impl<'a> DivAssign<&'a mut Self> for Nothing {
    fn div_assign(&mut self, _: &'a mut Self) {
        // No operation
    }
}
impl One for Nothing {
    fn one() -> Self {
        Nothing{}
    }
}

impl Zero for Nothing {
    fn zero() -> Self {
        Nothing{}
    }
    fn is_zero(&self) -> bool {
        true
    }
}

impl Sum<Nothing> for Nothing {
    fn sum<I: Iterator<Item = Nothing>>(iter: I) -> Self {
        iter.fold(Nothing{}, |_, _| Nothing{})
    }
}

impl From<Nothing> for BigInt<1> {
    fn from(_: Nothing) -> Self {
        BigInt::<1>::from(0u32)
    }
}

impl From<BigInt<1>> for Nothing {
    fn from(_: BigInt<1>) -> Self {
        Nothing{}
    }
}

impl<'a> Sum<&'a Nothing> for Nothing {
    fn sum<I: Iterator<Item = &'a Nothing>>(iter: I) -> Self {
        iter.fold(Nothing{}, |_, _| Nothing{})
    }
}

impl Product<Nothing> for Nothing {
    fn product<I: Iterator<Item = Nothing>>(iter: I) -> Self {
        iter.fold(Nothing{}, |_, _| Nothing{})
    }
}

impl<'a> Product<&'a Nothing> for Nothing {
    fn product<I: Iterator<Item = &'a Nothing>>(iter: I) -> Self {
        iter.fold(Nothing{}, |_, _| Nothing{})
    }
}

impl AdditiveGroup for Nothing {
    type Scalar = Self;
    const ZERO: Self = Nothing{};
}

impl Field for Nothing {
    type BasePrimeField = Self;
    const SQRT_PRECOMP: Option<SqrtPrecomputation<Self>> = None;
    const ONE: Self = Nothing{};

    // Required methods
    fn extension_degree() -> u64 {
        0
    }
    fn to_base_prime_field_elements(
        &self,
    ) -> impl Iterator<Item = Self::BasePrimeField> {
        std::iter::once(*self)
    }
    fn from_base_prime_field_elems(
        elems: impl IntoIterator<Item = Self::BasePrimeField>,
    ) -> Option<Self> {
        let mut iter = elems.into_iter();
        if iter.size_hint().0 == 1 {
            Some(iter.next().unwrap())
        } else {
            None
        }
    }
    fn from_base_prime_field(elem: Self::BasePrimeField) -> Self {
        elem
    }
    fn from_random_bytes_with_flags<FF: Flags>(bytes: &[u8]) -> Option<(Self, FF)> {
        if bytes.is_empty() {
            Some((Nothing{}, FF::default()))
        } else {
            None
        }
    }
    fn legendre(&self) -> LegendreSymbol {
        LegendreSymbol::QuadraticNonResidue
    }
    fn square(&self) -> Self {
        Nothing{}
    }
    fn square_in_place(&mut self) -> &mut Self {
        self
    }
    fn inverse(&self) -> Option<Self> {
        Some(Nothing{})
    }
    fn inverse_in_place(&mut self) -> Option<&mut Self> {
        Some(self)
    }
    fn frobenius_map_in_place(&mut self, _: usize) {
        // No operation
    }
    fn mul_by_base_prime_field(&self, elem: &Self::BasePrimeField) -> Self {
        *elem
    }
}

impl FftField for Nothing {
    const GENERATOR: Self = Nothing{};
    const TWO_ADICITY: u32 = 0;
    const TWO_ADIC_ROOT_OF_UNITY: Self = Nothing{};
    const SMALL_SUBGROUP_BASE: Option<u32> = None;
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = None;
    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<Self> = None;
}

impl PrimeField for Nothing {
    type BigInt = BigInt<1>;
    const MODULUS: Self::BigInt = BigInt([0;1]);
    const MODULUS_BIT_SIZE: u32 = 0;
    const TRACE: Self::BigInt = BigInt([0;1]);
    const TRACE_MINUS_ONE_DIV_TWO: Self::BigInt = BigInt([0;1]);
    const MODULUS_MINUS_ONE_DIV_TWO: Self::BigInt = BigInt([0;1]);

    fn from_bigint(_: Self::BigInt) -> Option<Self> {
        Some(Nothing{})
    }

    fn into_bigint(self) -> Self::BigInt {
        BigInt([0;1])
    }
}

impl PrimeGroup for Nothing {
    type ScalarField = Nothing;

    fn generator() -> Self {
        Nothing{}
    }
    fn mul_bigint(&self, _: impl AsRef<[u64]>) -> Self {
        Nothing{}
    }

    // Provided method
    fn mul_bits_be(&self, other: impl Iterator<Item = bool>) -> Self {
        other.fold(Nothing{}, |_, _| Nothing{})
    }
}

impl CurveConfig for Nothing {
    type BaseField = Nothing;
    type ScalarField = Nothing;

    const COFACTOR: &'static [u64] = &[];
    const COFACTOR_INV: Self::ScalarField = Nothing{};
}

impl ScalarMul for Nothing {
    type MulBase = Nothing;
    const NEGATION_IS_CHEAP: bool = true;

    // Required method
    fn batch_convert_to_mul_base(bases: &[Self]) -> Vec<Self::MulBase> {
        bases.iter().map(|_| Nothing{}).collect()
    }
}

impl VariableBaseMSM for Nothing {}

impl AffineRepr for Nothing {
    type Config = Nothing;
    type ScalarField = Nothing;
    type BaseField = Nothing;
    type Group = Nothing;

    // Required methods
    fn xy(&self) -> Option<(Self::BaseField, Self::BaseField)> {
        None
    }
    fn zero() -> Self {
        Nothing{}
    }
    fn generator() -> Self {
        Nothing{}
    }
    fn from_random_bytes(_: &[u8]) -> Option<Self> {
        Some(Nothing{})
    }
    fn mul_bigint(&self, _: impl AsRef<[u64]>) -> Self::Group {
        Nothing{}
    }
    fn clear_cofactor(&self) -> Self {
        Nothing{}
    }
    fn mul_by_cofactor_to_group(&self) -> Self::Group {
        Nothing{}
    }
}

impl CurveGroup for Nothing {
    type Config = Nothing;
    type BaseField = Nothing;
    type Affine = Nothing;
    type FullGroup = Nothing;

    // Required method
    fn normalize_batch(v: &[Self]) -> Vec<Self::Affine> {
        v.iter().map(|_| Nothing{}).collect()
    }
}

impl CyclotomicMultSubgroup for Nothing {
    const INVERSE_IS_FAST: bool = false;
}


impl<'a, G: CurveGroup> From<&'a G> for Nothing {
    fn from(_: &'a G) -> Self {
        Nothing{}
    }
}


