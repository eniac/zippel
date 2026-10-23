//! Univariate polynomials by their coefficients: dense (every coefficient, lowest degree
//! first) or sparse (the non-zero `(degree, coefficient)` terms). Both encodings are
//! canonical, so structural equality is equality of polynomials within an encoding.

use crate::Field;
use rayon::prelude::*;

/// A univariate polynomial by all its coefficients, lowest degree first, with no trailing
/// zero: the zero polynomial has no coefficients.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct DenseUni<F> {
    coeffs: Vec<F>,
}

impl<F> Default for DenseUni<F> {
    fn default() -> Self {
        Self { coeffs: Vec::new() }
    }
}

/// A univariate polynomial by its non-zero terms, `(degree, coefficient)` in increasing
/// degree, each degree once.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct SparseUni<F> {
    terms: Vec<(usize, F)>,
}

impl<F> Default for SparseUni<F> {
    fn default() -> Self {
        Self { terms: Vec::new() }
    }
}

/// Coefficients above this many evaluate as parallel chunks.
const PARALLEL_EVALUATE: usize = 1 << 12;

/// Products with a factor of at most this many coefficients multiply term by term; above
/// it, through an FFT.
const SCHOOLBOOK_MUL: usize = 32;

impl<F: Field> DenseUni<F> {
    /// The polynomial with these coefficients, lowest degree first.
    pub fn new(mut coeffs: Vec<F>) -> Self {
        while coeffs.last().is_some_and(|c| c.is_zero()) {
            coeffs.pop();
        }
        Self { coeffs }
    }

    /// The coefficients, lowest degree first, without trailing zeros.
    pub fn coeffs(&self) -> &[F] {
        &self.coeffs
    }

    /// The coefficients, lowest degree first, without trailing zeros.
    pub fn into_coeffs(self) -> Vec<F> {
        self.coeffs
    }

    /// Whether this is the zero polynomial.
    pub fn is_zero(&self) -> bool {
        self.coeffs.is_empty()
    }

    /// The degree; 0 for the zero polynomial.
    pub fn degree(&self) -> usize {
        self.coeffs.len().saturating_sub(1)
    }

    /// The value at `x`, by Horner's rule (in parallel chunks for a long polynomial).
    pub fn evaluate(&self, x: &F) -> F {
        let horner = |coeffs: &[F]| coeffs.iter().rfold(F::zero(), |acc, c| acc * x + c);
        if self.coeffs.len() <= PARALLEL_EVALUATE {
            return horner(&self.coeffs);
        }
        let chunk = self.coeffs.len().div_ceil(rayon::current_num_threads());
        self.coeffs
            .par_chunks(chunk)
            .enumerate()
            .map(|(i, part)| horner(part) * x.pow((i * chunk) as u64))
            .sum()
    }

    /// The sum.
    pub fn add(&self, other: &Self) -> Self {
        let (long, short) = if self.coeffs.len() >= other.coeffs.len() {
            (self, other)
        } else {
            (other, self)
        };
        let mut coeffs = long.coeffs.clone();
        coeffs
            .par_iter_mut()
            .zip(short.coeffs.par_iter())
            .for_each(|(a, b)| *a += b);
        Self::new(coeffs)
    }

    /// The product: by FFT when both factors are long and the field has a domain for
    /// the product, else term by term.
    pub fn mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::default();
        }
        let len = self.coeffs.len() + other.coeffs.len() - 1;
        let domain = len.next_power_of_two();
        if self.coeffs.len().min(other.coeffs.len()) <= SCHOOLBOOK_MUL
            || domain.trailing_zeros() > F::TWO_ADICITY
        {
            return self.schoolbook_mul(other);
        }
        let padded = |coeffs: &[F]| {
            let mut v = coeffs.to_vec();
            v.resize(domain, F::zero());
            F::fft(&mut v);
            v
        };
        let mut a = padded(&self.coeffs);
        let b = padded(&other.coeffs);
        a.par_iter_mut()
            .zip(b.par_iter())
            .for_each(|(x, y)| *x *= y);
        F::ifft(&mut a);
        a.truncate(len);
        Self::new(a)
    }

    fn schoolbook_mul(&self, other: &Self) -> Self {
        let mut coeffs = vec![F::zero(); self.coeffs.len() + other.coeffs.len() - 1];
        for (i, a) in self.coeffs.iter().enumerate() {
            for (j, b) in other.coeffs.iter().enumerate() {
                coeffs[i + j] += *a * b;
            }
        }
        Self::new(coeffs)
    }

    /// The quotient and remainder of division by `divisor`; `None` if it is zero.
    ///
    /// Long division visits only the divisor's non-zero coefficients, so dividing by a
    /// sparse polynomial such as `x^n - 1` is linear. A divisor with many non-zero
    /// coefficients and a long quotient divides by Newton iteration instead (`O(n log n)`
    /// with FFT multiplication), when the field has the FFT domains it needs.
    pub fn div_rem(&self, divisor: &Self) -> Option<(Self, Self)> {
        let lead_inv = divisor.coeffs.last()?.inverse()?;
        let d = divisor.degree();
        if self.coeffs.len() <= d {
            return Some((Self::default(), self.clone()));
        }
        let terms: Vec<(usize, F)> = divisor.coeffs[..d]
            .iter()
            .enumerate()
            .filter(|(_, c)| !c.is_zero())
            .map(|(i, c)| (i, *c))
            .collect();
        let quotient_len = self.coeffs.len() - d;
        let fft_len = (self.coeffs.len() + quotient_len).next_power_of_two();
        if terms.len() >= NEWTON_DIV
            && quotient_len >= NEWTON_DIV
            && fft_len.trailing_zeros() <= F::TWO_ADICITY
        {
            return Some(self.newton_div_rem(divisor, quotient_len));
        }
        let mut rem = self.coeffs.clone();
        let mut quotient = vec![F::zero(); quotient_len];
        for k in (0..quotient_len).rev() {
            let q = rem[k + d] * lead_inv;
            quotient[k] = q;
            for &(i, c) in &terms {
                rem[k + i] -= q * c;
            }
        }
        rem.truncate(d);
        Some((Self::new(quotient), Self::new(rem)))
    }

    /// Division by Newton iteration ("Modern Computer Algebra", algorithm 9.5): with
    /// `rev` reversing coefficients, `rev(q) = rev(self) · rev(divisor)^-1 mod x^k` for
    /// the quotient's length `k`, and the remainder is `self - q · divisor`.
    fn newton_div_rem(&self, divisor: &Self, k: usize) -> (Self, Self) {
        let reversed = |coeffs: &[F], len: usize| -> Vec<F> {
            coeffs.iter().rev().take(len).copied().collect()
        };
        let inv = Self::new(inverse_mod_xk(&reversed(&divisor.coeffs, k), k));
        let mut rev_q = Self::new(reversed(&self.coeffs, k)).mul(&inv).coeffs;
        rev_q.resize(k, F::zero());
        rev_q.reverse();
        let quotient = Self::new(rev_q);
        let rem = self.add(&quotient.mul(divisor).neg());
        (quotient, rem)
    }

    fn neg(&self) -> Self {
        Self {
            coeffs: self.coeffs.iter().map(|c| -*c).collect(),
        }
    }
}

/// Divisors with at least this many non-zero coefficients, and quotients at least this long,
/// divide by Newton iteration.
const NEWTON_DIV: usize = 256;

/// `f^-1 mod x^k`, by Newton iteration `g ← g · (2 - f·g) mod x^2l`; `f[0]` is non-zero.
fn inverse_mod_xk<F: Field>(f: &[F], k: usize) -> Vec<F> {
    let truncated = |p: DenseUni<F>, len: usize| {
        let mut c = p.coeffs;
        c.resize(len, F::zero());
        c
    };
    let mut g = vec![
        f[0].inverse()
            .expect("a divisor's leading coefficient is non-zero"),
    ];
    let mut l = 1;
    while l < k {
        l = (2 * l).min(k);
        let g_poly = DenseUni::new(g);
        let fg = truncated(DenseUni::new(f[..f.len().min(l)].to_vec()).mul(&g_poly), l);
        let mut two_minus_fg: Vec<F> = fg.into_iter().map(|c| -c).collect();
        two_minus_fg[0] += F::one() + F::one();
        g = truncated(g_poly.mul(&DenseUni::new(two_minus_fg)), l);
    }
    g
}

impl<F: Field> SparseUni<F> {
    /// The polynomial with these terms, in any order; terms of one degree add up.
    pub fn new(mut terms: Vec<(usize, F)>) -> Self {
        terms.sort_unstable_by_key(|&(d, _)| d);
        let mut merged: Vec<(usize, F)> = Vec::with_capacity(terms.len());
        for (d, c) in terms {
            match merged.last_mut() {
                Some((last, sum)) if *last == d => *sum += c,
                _ => merged.push((d, c)),
            }
        }
        merged.retain(|(_, c)| !c.is_zero());
        Self { terms: merged }
    }

    /// The non-zero terms, in increasing degree.
    pub fn terms(&self) -> &[(usize, F)] {
        &self.terms
    }

    /// Whether this is the zero polynomial.
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// The degree; 0 for the zero polynomial.
    pub fn degree(&self) -> usize {
        self.terms.last().map_or(0, |&(d, _)| d)
    }

    /// The value at `x`.
    pub fn evaluate(&self, x: &F) -> F {
        self.terms.iter().map(|&(d, c)| c * x.pow(d as u64)).sum()
    }

    /// The sum.
    pub fn add(&self, other: &Self) -> Self {
        Self::new(self.terms.iter().chain(&other.terms).copied().collect())
    }

    /// The same polynomial, dense.
    pub fn to_dense(&self) -> DenseUni<F> {
        let mut coeffs = vec![F::zero(); self.terms.last().map_or(0, |&(d, _)| d + 1)];
        for &(d, c) in &self.terms {
            coeffs[d] = c;
        }
        DenseUni { coeffs }
    }
}
