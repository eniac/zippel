//! The algebra a backend supplies: a prime [`Field`], [`Group`]s over it, and an optional
//! [`Pairing`]. Every runtime value and polynomial is generic over these traits alone, so a
//! backend is any library that implements them (see `ark` for arkworks).

use rand::Rng;
use rayon::prelude::*;
use std::cmp::Ordering;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::iter::{Product, Sum};
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

/// A division (or inversion, or interpolation at repeated points) by zero.
#[derive(thiserror::Error, Debug, Clone, Copy, PartialEq, Eq)]
#[error("Division by zero")]
pub struct DivisionByZero;

/// A prime field: the scalars of a backend.
pub trait Field:
    Copy
    + Send
    + Sync
    + 'static
    + Eq
    + Hash
    + Debug
    + Display
    + From<u64>
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Neg<Output = Self>
    + for<'a> Add<&'a Self, Output = Self>
    + for<'a> Sub<&'a Self, Output = Self>
    + for<'a> Mul<&'a Self, Output = Self>
    + AddAssign
    + SubAssign
    + MulAssign
    + for<'a> AddAssign<&'a Self>
    + for<'a> SubAssign<&'a Self>
    + for<'a> MulAssign<&'a Self>
    + Sum
    + Product
    + for<'a> Sum<&'a Self>
    + for<'a> Product<&'a Self>
{
    /// The number of bits of the modulus.
    const MODULUS_BITS: u32;
    /// `log2` of the largest power-of-two FFT domain: the field has a primitive
    /// `2^TWO_ADICITY`-th root of unity.
    const TWO_ADICITY: u32;

    /// The additive identity.
    fn zero() -> Self;
    /// The multiplicative identity.
    fn one() -> Self;
    /// `i` as a field element.
    fn from_usize(i: usize) -> Self {
        Self::from(i as u64)
    }
    /// Whether this is zero.
    fn is_zero(&self) -> bool;
    /// Whether this is one.
    fn is_one(&self) -> bool {
        *self == Self::one()
    }
    /// The multiplicative inverse; `None` for zero.
    fn inverse(&self) -> Option<Self>;
    /// `self^e`.
    fn pow(&self, mut e: u64) -> Self {
        let (mut base, mut acc) = (*self, Self::one());
        while e > 0 {
            if e & 1 == 1 {
                acc *= base;
            }
            base *= base;
            e >>= 1;
        }
        acc
    }
    /// A uniformly random element.
    fn rand<R: Rng + ?Sized>(rng: &mut R) -> Self;
    /// `bytes`, read as a little-endian integer, reduced modulo the field's prime.
    fn from_le_bytes_mod_order(bytes: &[u8]) -> Self;
    /// Appends the canonical encoding (the transcript's, see `values::serialize_value`).
    fn write_bytes(&self, out: &mut Vec<u8>);
    /// Compares canonical integer representatives, a total order.
    fn cmp_canonical(&self, other: &Self) -> Ordering;
    /// A primitive `2^log_n`-th root of unity; `None` above [`Self::TWO_ADICITY`].
    fn two_adic_root(log_n: u32) -> Option<Self>;

    /// The FFT of `a` (coefficients to evaluations at the powers of a primitive
    /// `a.len()`-th root of unity), in place.
    ///
    /// # Panics
    /// Panics unless `a.len()` is a power of two at most `2^TWO_ADICITY`.
    fn fft(a: &mut Vec<Self>) {
        radix2(a, false);
    }

    /// The inverse FFT of `a` (evaluations to coefficients), in place.
    ///
    /// # Panics
    /// Panics under the same conditions as [`Self::fft`].
    fn ifft(a: &mut Vec<Self>) {
        radix2(a, true);
    }
}

/// An iterative radix-2 FFT over [`Field::two_adic_root`]; the inverse transform scales by
/// `1 / n`.
pub(crate) fn radix2<F: Field>(a: &mut [F], inverse: bool) {
    let n = a.len();
    assert!(
        n.is_power_of_two(),
        "an FFT domain has a power-of-two size, not {n}"
    );
    let log_n = n.trailing_zeros();
    let root = F::two_adic_root(log_n)
        .unwrap_or_else(|| panic!("the field has no FFT domain of size 2^{log_n}"));
    let root = if inverse {
        root.inverse().expect("a root of unity is non-zero")
    } else {
        root
    };
    for i in 0..n {
        let j = i.reverse_bits() >> (usize::BITS - log_n.max(1));
        if n > 1 && i < j {
            a.swap(i, j);
        }
    }
    let mut len = 2;
    while len <= n {
        let w_len = root.pow((n / len) as u64);
        let twiddles: Vec<F> = std::iter::successors(Some(F::one()), |w| Some(*w * w_len))
            .take(len / 2)
            .collect();
        a.par_chunks_mut(len).for_each(|chunk| {
            let (lo, hi) = chunk.split_at_mut(len / 2);
            for ((x, y), w) in lo.iter_mut().zip(hi.iter_mut()).zip(&twiddles) {
                let t = *y * w;
                *y = *x - t;
                *x += t;
            }
        });
        len <<= 1;
    }
    if inverse {
        let n_inv = F::from(n as u64)
            .inverse()
            .expect("n is non-zero in the field");
        a.par_iter_mut().for_each(|x| *x *= n_inv);
    }
}

/// A prime-order group, written additively, over the scalar field [`Group::Scalar`].
pub trait Group:
    Copy
    + Send
    + Sync
    + 'static
    + Eq
    + Debug
    + Display
    + Add<Output = Self>
    + Sub<Output = Self>
    + Neg<Output = Self>
    + AddAssign
    + SubAssign
    + Mul<Self::Scalar, Output = Self>
    + MulAssign<Self::Scalar>
{
    /// The scalar field.
    type Scalar: Field;
    /// The normalized form an MSM consumes (affine coordinates), and the one equality and
    /// hashing go through; `Self` for a group with a single form.
    type Affine: Copy + Send + Sync + 'static + Eq + Hash + Debug + Into<Self>;

    /// The identity.
    fn zero() -> Self;
    /// The fixed generator.
    fn generator() -> Self;
    /// Whether this is the identity.
    fn is_zero(&self) -> bool;
    /// A uniformly random element.
    fn rand<R: Rng + ?Sized>(rng: &mut R) -> Self;
    /// `self + a`, in place.
    fn add_affine(&mut self, a: &Self::Affine);
    /// The normalized form.
    fn normalize(&self) -> Self::Affine;
    /// The normalized forms, at once (one inversion for affine coordinates).
    fn normalize_batch(v: &[Self]) -> Vec<Self::Affine>;
    /// `self * s` for each `s` in `scalars`, normalized.
    fn batch_mul(&self, scalars: &[Self::Scalar]) -> Vec<Self::Affine>;
    /// The multi-scalar multiplication `Σ scalars[i] * bases[i]`.
    ///
    /// # Panics
    /// Panics if the two have different lengths.
    fn msm(bases: &[Self::Affine], scalars: &[Self::Scalar]) -> Self;
    /// Appends the canonical (compressed) encoding: the same for every form of a point.
    fn write_bytes(&self, out: &mut Vec<u8>);
    /// Appends the canonical encoding of a normalized point, equal to its group element's.
    fn write_affine_bytes(a: &Self::Affine, out: &mut Vec<u8>);
}

/// A bilinear map `e: G1 × G2 → GT`.
pub trait Pairing: Send + Sync + 'static {
    /// The first source group.
    type G1: Group;
    /// The second source group.
    type G2: Group<Scalar = <Self::G1 as Group>::Scalar>;
    /// The target group.
    type GT: Group<Scalar = <Self::G1 as Group>::Scalar, Affine = Self::GT> + Hash;
    /// A second-source point prepared for pairing (as a verifier key keeps it).
    type G2Prepared: Clone + Send + Sync + Debug;

    /// `g` prepared for pairing.
    fn prepare_g2(g: &<Self::G2 as Group>::Affine) -> Self::G2Prepared;
    /// `e(a, b)`.
    fn pairing(a: &Self::G1, b: &Self::G2) -> Self::GT;
    /// `Σ e(a[i], b[i])`.
    ///
    /// # Panics
    /// Panics if the two have different lengths.
    fn multi_pairing(a: &[Self::G1], b: &[Self::G2]) -> Self::GT;
    /// `Σ e(a[i], b[i])`, with the second side prepared.
    ///
    /// # Panics
    /// Panics if the two have different lengths.
    fn multi_pairing_prepared(a: &[Self::G1], b: &[Self::G2Prepared]) -> Self::GT;

    /// `e(a[i], b[i])` for each `i`.
    fn pairings(a: &[Self::G1], b: &[Self::G2]) -> Vec<Self::GT> {
        a.par_iter()
            .zip(b.par_iter())
            .map(|(a, b)| Self::pairing(a, b))
            .collect()
    }
}

/// Elementwise `b[i] += a[i]`, over the shorter length.
pub fn vec_add<F: Field>(a: &[F], b: &mut [F]) {
    b.par_iter_mut()
        .zip(a.par_iter())
        .for_each(|(b, a)| *b += a);
}

/// Elementwise `b[i] = a[i] - b[i]`, over the shorter length.
pub fn vec_sub<F: Field>(a: &[F], b: &mut [F]) {
    b.par_iter_mut()
        .zip(a.par_iter())
        .for_each(|(b, a)| *b = *a - *b);
}

/// Elementwise `b[i] *= a[i]`, over the shorter length.
pub fn vec_mul<F: Field>(a: &[F], b: &mut [F]) {
    b.par_iter_mut()
        .zip(a.par_iter())
        .for_each(|(b, a)| *b *= a);
}

/// Elementwise negation.
pub fn vec_neg<F: Field>(a: &mut [F]) {
    a.par_iter_mut().for_each(|x| *x = -*x);
}

/// Elementwise `a[i]^e`.
pub fn vec_pow<F: Field>(a: &mut [F], e: u64) {
    a.par_iter_mut().for_each(|x| *x = x.pow(e));
}

/// The inner product.
pub fn vec_dot<F: Field>(a: &[F], b: &[F]) -> F {
    a.par_iter()
        .zip(b.par_iter())
        .map(|(a, b)| *a * b)
        .reduce(F::zero, |x, y| x + y)
}

/// Inverts every entry in place with one field inversion (Montgomery's trick).
///
/// # Errors
/// [`DivisionByZero`] if an entry is zero; `a` is then unchanged.
pub fn batch_inverse<F: Field>(a: &mut [F]) -> Result<(), DivisionByZero> {
    const CHUNK: usize = 1 << 10;
    if a.par_iter().any(Field::is_zero) {
        return Err(DivisionByZero);
    }
    a.par_chunks_mut(CHUNK).for_each(|chunk| {
        let mut prefix = Vec::with_capacity(chunk.len());
        let mut acc = F::one();
        for x in chunk.iter() {
            prefix.push(acc);
            acc *= x;
        }
        let mut inv = acc.inverse().expect("a product of non-zero entries");
        for (x, before) in chunk.iter_mut().zip(prefix).rev() {
            let next = inv * *x;
            *x = inv * before;
            inv = next;
        }
    });
    Ok(())
}

/// Elementwise `b[i] = a[i] / b[i]`, over the shorter length.
///
/// # Errors
/// [`DivisionByZero`] if an entry of `b` is zero; `b` is then unchanged.
pub fn vec_div<F: Field>(a: &[F], b: &mut [F]) -> Result<(), DivisionByZero> {
    batch_inverse(b)?;
    vec_mul(a, b);
    Ok(())
}

/// `n` uniformly random elements.
pub fn vec_rand<F: Field, R: Rng + ?Sized>(rng: &mut R, n: usize) -> Vec<F> {
    (0..n).map(|_| F::rand(rng)).collect()
}
