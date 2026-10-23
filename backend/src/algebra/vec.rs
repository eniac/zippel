//! Elementwise vector arithmetic over a [`Field`], in parallel.

use super::{DivisionByZero, Field};
use rand::Rng;
use rayon::prelude::*;

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
