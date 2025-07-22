use ark_ff::{SqrtPrecomputation, FftField, AdditiveGroup, CyclotomicMultSubgroup, Field, LegendreSymbol, One, PrimeField, UniformRand, Zero};
use ark_ff::biginteger::BigInt;
use num_bigint::BigUint;
use ark_serialize::{
    CanonicalSerialize, CanonicalDeserialize, CanonicalSerializeWithFlags, CanonicalDeserializeWithFlags,
    Compress, Valid, Validate, SerializationError, Flags};
use zeroize::Zeroize;
use std::fmt;
use rand::Rng;
use std::iter::{Product, Sum};
use ark_std::io::{Read, Write};
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign,
    BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign, Mul, MulAssign, Neg,
    Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign};
use std::str::FromStr;

/// Represents the empty field
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct NoField {}

const NOFIELD_ERR: &str = "NoField is an empty curve with no points. It cannot be used for any operations.";

impl AdditiveGroup for NoField {
    type Scalar = NoField;
    const ZERO: Self = NoField{};
}

impl UniformRand for NoField {
    fn rand<R: Rng + ?Sized>(_: &mut R) -> Self {
        panic!("{}", NOFIELD_ERR)
    }
}

impl Zeroize for NoField {
    fn zeroize(&mut self) {
        panic!("{}", NOFIELD_ERR)
    }
}
impl From<NoField> for BigUint {
    fn from(_: NoField) -> Self {
        panic!("{}", NOFIELD_ERR)
    }
}

impl CanonicalSerialize for NoField {
    fn serialize_with_mode<W: Write>(&self, _: W, _: Compress) -> Result<(), SerializationError> {
        panic!("{}", NOFIELD_ERR)
    }

    fn serialized_size(&self, _: Compress) -> usize {
        panic!("{}", NOFIELD_ERR)
    }
}

impl Valid for NoField {
    fn check(&self) -> Result<(), SerializationError> {
        panic!("{}", NOFIELD_ERR)
    }
}

impl CanonicalDeserialize for NoField {
    fn deserialize_with_mode<R: Read>(_: R, _: Compress, _: Validate) -> Result<Self, SerializationError> {
        panic!("{}", NOFIELD_ERR)
    }
}

impl CanonicalSerializeWithFlags for NoField {
    fn serialize_with_flags<W: Write, FF: Flags>(
        &self,
        _: W,
        _: FF,
    ) -> Result<(), SerializationError> {
        panic!("{}", NOFIELD_ERR)
    }
    fn serialized_size_with_flags<FF: Flags>(&self) -> usize {
        panic!("{}", NOFIELD_ERR)
    }
}

impl CanonicalDeserializeWithFlags for NoField {
    fn deserialize_with_flags<R: Read, FF: Flags>(_: R)-> Result<(Self, FF), SerializationError> {
        panic!("{}", NOFIELD_ERR)
    }
}

impl Default for NoField {
    fn default() -> Self {
        panic!("{}", NOFIELD_ERR)
    }
}
impl fmt::Display for NoField {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "NoField")
    }
}
impl AsMut<[u64]> for NoField {
    fn as_mut(&mut self) -> &mut [u64] {
        panic!("{}", NOFIELD_ERR)
    }
}
impl AsRef<[u64]> for NoField {
    fn as_ref(&self) -> &[u64] {
        panic!("{}", NOFIELD_ERR)
    }
}

impl From<bool> for NoField {
    /// Converts a value of type T into NoField.
    fn from(_: bool) -> Self {
        panic!("{}", NOFIELD_ERR)
    }
}

impl From<u128> for NoField {
    /// Converts a value of type T into NoField.
    fn from(_: u128) -> Self {
        panic!("{}", NOFIELD_ERR)
    }
}
impl From<u64> for NoField {
    /// Converts a value of type T into NoField.
    fn from(_: u64) -> Self {
        panic!("{}", NOFIELD_ERR)
    }
}
impl From<u32> for NoField {
    /// Converts a value of type T into NoField.
    fn from(_: u32) -> Self {
        panic!("{}", NOFIELD_ERR)
    }
}
impl From<u16> for NoField {
    /// Converts a value of type T into NoField.
    fn from(_: u16) -> Self {
        panic!("{}", NOFIELD_ERR)
    }
}
impl From<u8> for NoField {
    /// Converts a value of type T into NoField.
    fn from(_: u8) -> Self {
        panic!("{}", NOFIELD_ERR)
    }
}

impl From<i128> for NoField {
    /// Converts a value of type T into NoField.
    fn from(_: i128) -> Self {
        panic!("{}", NOFIELD_ERR)
    }
}

impl From<i64> for NoField {
    /// Converts a value of type T into NoField.
    fn from(_: i64) -> Self {
        panic!("{}", NOFIELD_ERR)
    }
}

impl From<i32> for NoField {
    /// Converts a value of type T into NoField.
    fn from(_: i32) -> Self {
        panic!("{}", NOFIELD_ERR)
    }
}

impl From<i16> for NoField {
    /// Converts a value of type T into NoField.
    fn from(_: i16) -> Self {
        panic!("{}", NOFIELD_ERR)
    }
}

impl From<i8> for NoField {
    /// Converts a value of type T into NoField.
    fn from(_: i8) -> Self {
        panic!("{}", NOFIELD_ERR)
    }
}

impl From<BigUint> for NoField {
    /// Converts a value of type T into NoField.
    fn from(_: BigUint) -> Self {
        panic!("{}", NOFIELD_ERR)
    }
}

impl FromStr for NoField {
    type Err = ();
    fn from_str(_: &str) -> Result<Self, Self::Err> {
        panic!("{}", NOFIELD_ERR)
    }
}

impl BitXorAssign for NoField {
    fn bitxor_assign(&mut self, _: Self) {
        panic!("{}", NOFIELD_ERR)
    }
}

impl<'a> BitXorAssign<&'a Self> for NoField {
    fn bitxor_assign(&mut self, _: &'a Self) {
        panic!("{}", NOFIELD_ERR)
    }
}

impl<'a> BitXor<&'a Self> for NoField {
    type Output = Self;
    fn bitxor(self, _: &'a Self) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl BitXor for NoField {
    type Output = Self;
    fn bitxor(self, _: Self) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl BitAndAssign for NoField {
    fn bitand_assign(&mut self, _: Self) {
        panic!("{}", NOFIELD_ERR);
    }
}

impl BitAnd for NoField {
    type Output = Self;
    fn bitand(self, _: Self) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl<'a> BitAndAssign<&'a Self> for NoField {
    fn bitand_assign(&mut self, _: &'a Self) {
        panic!("{}", NOFIELD_ERR);
    }
}

impl<'a> BitAnd<&'a Self> for NoField {
    type Output = Self;
    fn bitand(self, _: &'a Self) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl BitOrAssign for NoField {
    fn bitor_assign(&mut self, _: Self) {
        panic!("{}", NOFIELD_ERR);
    }
}

impl BitOr for NoField {
    type Output = Self;
    fn bitor(self, _: Self) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl<'a> BitOrAssign<&'a Self> for NoField {
    fn bitor_assign(&mut self, _: &'a Self) {
        panic!("{}", NOFIELD_ERR);
    }
}

impl<'a> BitOr<&'a Self> for NoField {
    type Output = Self;
    fn bitor(self, _: &'a Self) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl ShrAssign<u32> for NoField {
    fn shr_assign(&mut self, _: u32) {
        panic!("{}", NOFIELD_ERR);
    }
}

impl Shr<u32> for NoField {
    type Output = Self;
    fn shr(self, _: u32) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl ShlAssign<u32> for NoField {
    fn shl_assign(&mut self, _: u32) {
        panic!("{}", NOFIELD_ERR);
    }
}

impl Shl<u32> for NoField {
    type Output = Self;
    fn shl(self, _: u32) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl Neg for NoField {
    type Output = Self;
    fn neg(self) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl Add for NoField {
    type Output = Self;
    fn add(self, _: Self) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl AddAssign for NoField {
    fn add_assign(&mut self, _: Self) {
        panic!("{}", NOFIELD_ERR);
    }
}

impl<'a> AddAssign<&'a Self> for NoField {
    fn add_assign(&mut self, _: &'a Self) {
        panic!("{}", NOFIELD_ERR);
    }
}

impl<'a> AddAssign<&'a mut Self> for NoField {
    fn add_assign(&mut self, _: &'a mut Self) {
        panic!("{}", NOFIELD_ERR);
    }
}

impl<'a> SubAssign<&'a mut Self> for NoField {
    fn sub_assign(&mut self, _: &'a mut Self) {
        panic!("{}", NOFIELD_ERR);
    }
}


impl<'a> Add<&'a Self> for NoField {
    type Output = Self;
    fn add(self, _: &'a Self) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl<'a> Add<&'a mut Self> for NoField {
    type Output = Self;
    fn add(self, _: &'a mut Self) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl SubAssign for NoField {
    fn sub_assign(&mut self, _: Self) {
        panic!("{}", NOFIELD_ERR);
    }
}

impl<'a> SubAssign<&'a Self> for NoField {
    fn sub_assign(&mut self, _: &'a Self) {
        panic!("{}", NOFIELD_ERR);
    }
}

impl<'a> Sub<&'a Self> for NoField {
    type Output = Self;
    fn sub(self, _: &'a Self) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl Sub for NoField {
    type Output = Self;
    fn sub(self, _: Self) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl<'a> Sub<&'a mut Self> for NoField {
    type Output = Self;
    fn sub(self, _: &'a mut Self) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl Mul for NoField {
    type Output = Self;
    fn mul(self, _: Self) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}
impl<'a> Mul<&'a mut Self> for NoField {
    type Output = Self;
    fn mul(self, _: &'a mut Self) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}
impl<'a> MulAssign<&'a mut Self> for NoField {
    fn mul_assign(&mut self, _: &'a mut Self) {
        panic!("{}", NOFIELD_ERR);
    }
}

impl MulAssign for NoField {
    fn mul_assign(&mut self, _: Self) {
        panic!("{}", NOFIELD_ERR);
    }
}
impl<'a> MulAssign<&'a Self> for NoField {
    fn mul_assign(&mut self, _: &'a Self) {
        panic!("{}", NOFIELD_ERR);
    }
}
impl<'a> Mul<&'a Self> for NoField {
    type Output = Self;
    fn mul(self, _: &'a Self) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}
impl Div for NoField {
    type Output = Self;
    fn div(self, _: Self) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl<'a> Div<&'a Self> for NoField {
    type Output = Self;
    fn div(self, _: &'a Self) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl<'a> Div<&'a mut Self> for NoField {
    type Output = Self;
    fn div(self, _: &'a mut Self) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl DivAssign for NoField {
    fn div_assign(&mut self, _: Self) {
        panic!("{}", NOFIELD_ERR);
    }
}

impl<'a> DivAssign<&'a Self> for NoField {
    fn div_assign(&mut self, _: &'a Self) {
        panic!("{}", NOFIELD_ERR);
    }
}
impl<'a> DivAssign<&'a mut Self> for NoField {
    fn div_assign(&mut self, _: &'a mut Self) {
        panic!("{}", NOFIELD_ERR);
    }
}
impl One for NoField {
    fn one() -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl Zero for NoField {
    fn zero() -> Self {
        panic!("{}", NOFIELD_ERR);
    }
    fn is_zero(&self) -> bool {
        true
    }
}

impl Sum<NoField> for NoField {
    fn sum<I: Iterator<Item = NoField>>(_: I) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl From<NoField> for BigInt<1> {
    fn from(_: NoField) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl From<BigInt<1>> for NoField {
    fn from(_: BigInt<1>) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl<'a> Sum<&'a NoField> for NoField {
    fn sum<I: Iterator<Item = &'a NoField>>(_: I) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl Product<NoField> for NoField {
    fn product<I: Iterator<Item = NoField>>(_: I) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl<'a> Product<&'a NoField> for NoField {
    fn product<I: Iterator<Item = &'a NoField>>(_: I) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
}

impl Field for NoField {
    type BasePrimeField = Self;
    const SQRT_PRECOMP: Option<SqrtPrecomputation<Self>> = None;
    const ONE: Self = NoField{};
    // const NEG_ONE: Self = NoField{};

    // Required methods
    fn extension_degree() -> u64 {
        panic!("{}", NOFIELD_ERR)
    }
    fn to_base_prime_field_elements(
        &self,
    ) -> impl Iterator<Item = Self::BasePrimeField> {
        std::iter::empty()
    }
    fn from_base_prime_field_elems(
        _: impl IntoIterator<Item = Self::BasePrimeField>,
    ) -> Option<Self> {
        panic!("{}", NOFIELD_ERR);
    }
    fn from_base_prime_field(_: Self::BasePrimeField) -> Self {
        panic!("{}", NOFIELD_ERR);
    }
    fn from_random_bytes_with_flags<FF: Flags>(_: &[u8]) -> Option<(Self, FF)> {
        panic!("{}", NOFIELD_ERR);
    }
    fn legendre(&self) -> LegendreSymbol {
        panic!("{}", NOFIELD_ERR)
    }
    fn square(&self) -> Self {
        panic!("{}", NOFIELD_ERR)
    }
    fn square_in_place(&mut self) -> &mut Self {
        panic!("{}", NOFIELD_ERR)
    }
    fn inverse(&self) -> Option<Self> {
        panic!("{}", NOFIELD_ERR)
    }
    fn inverse_in_place(&mut self) -> Option<&mut Self> {
        panic!("{}", NOFIELD_ERR)
    }
    fn frobenius_map_in_place(&mut self, _: usize) {
        panic!("{}", NOFIELD_ERR)
    }
    fn mul_by_base_prime_field(&self, _: &Self::BasePrimeField) -> Self {
        panic!("{}", NOFIELD_ERR)
    }
}

impl FftField for NoField {
    const GENERATOR: Self = NoField{};
    const TWO_ADICITY: u32 = 0;
    const TWO_ADIC_ROOT_OF_UNITY: Self = NoField{};
    const SMALL_SUBGROUP_BASE: Option<u32> = None;
    const SMALL_SUBGROUP_BASE_ADICITY: Option<u32> = None;
    const LARGE_SUBGROUP_ROOT_OF_UNITY: Option<Self> = None;
}

impl PrimeField for NoField {
    type BigInt = BigInt<1>;
    const MODULUS: Self::BigInt = BigInt([0;1]);
    const MODULUS_BIT_SIZE: u32 = 0;
    const TRACE: Self::BigInt = BigInt([0;1]);
    const TRACE_MINUS_ONE_DIV_TWO: Self::BigInt = BigInt([0;1]);
    const MODULUS_MINUS_ONE_DIV_TWO: Self::BigInt = BigInt([0;1]);

    fn from_bigint(_: Self::BigInt) -> Option<Self> {
        panic!("{}", NOFIELD_ERR);
    }

    fn into_bigint(self) -> Self::BigInt {
        panic!("{}", NOFIELD_ERR);
    }
}
impl CyclotomicMultSubgroup for NoField {
    const INVERSE_IS_FAST: bool = false;
}

