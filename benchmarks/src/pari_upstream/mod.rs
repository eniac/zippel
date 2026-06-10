//! PARI SNARK — code vendored from alireza-shirzad/garuda-pari `pari` +
//! `shared-utils` crates (commit 3db79ad). Pinned in-tree against the
//! workspace arkworks-0.6 git pin so we don't need to coexist with
//! garuda-pari's separate arkworks-0.5 + crypto-primitives source set.
//!
//! Only the items pari + transcript actually use are inlined; benchmark
//! glue (`shared-utils::bench::BenchResult`) and the Solidity emitter
//! (`pari/src/solidity.rs`, which pulls tiny-keccak) are dropped.

use ark_ec::pairing::Pairing;
use ark_ff::{BigInteger, Field, PrimeField};
use ark_std::marker::PhantomData;

pub mod data_structures;
pub mod generator;
pub mod prover;
pub mod transcript;
pub mod utils;
pub mod verifier;

#[cfg(test)]
mod test;

/// The SNARK of [Pari](https://eprint.iacr.org/2024/1245.pdf).
pub struct Pari<E: Pairing> {
    _p: PhantomData<E>,
}

impl<E: Pairing> Pari<E> {
    pub const SNARK_NAME: &'static [u8; 4] = b"Pari";
}

/// Re-export so vendored sub-modules can write `use super::to_bytes;`.
#[macro_export]
macro_rules! to_bytes {
    ($x:expr) => {{
        let mut buf = ark_std::vec![];
        ark_serialize::CanonicalSerialize::serialize_compressed($x, &mut buf).map(|_| buf)
    }};
}

// ---------------------------------------------------------------------------
// Vendored from shared-utils/src/lib.rs — the two helpers pari actually uses
// (`msm_bigint_wnaf` from prover, `batch_inversion_and_mul` from verifier).
// ---------------------------------------------------------------------------

use ark_ec::VariableBaseMSM;

pub fn msm_bigint_wnaf<V: VariableBaseMSM>(
    bases: &[V::MulBase],
    scalars: &[<V::ScalarField as PrimeField>::BigInt],
) -> V {
    const C: usize = 2;
    let digits_count = const { (V::ScalarField::MODULUS_BIT_SIZE as usize).div_ceil(C) };
    let radix: u64 = 1 << C;
    let scalar_digits = scalars
        .iter()
        .flat_map(|s| make_digits::<C>(s, digits_count, radix))
        .collect::<Vec<_>>();
    let zero = V::zero();
    let mut window_sums = (0..digits_count).map(|i| {
        let mut buckets = [zero; 1 << C];
        for (digits, base) in scalar_digits.chunks(digits_count).zip(bases) {
            use ark_std::cmp::Ordering;
            let scalar = digits[i];
            match 0.cmp(&scalar) {
                Ordering::Less => buckets[(scalar - 1) as usize] += base,
                Ordering::Greater => buckets[(-scalar - 1) as usize] -= base,
                Ordering::Equal => (),
            }
        }

        let mut running_sum = V::zero();
        let mut res = V::zero();
        buckets.into_iter().rev().for_each(|b| {
            running_sum += &b;
            res += &running_sum;
        });
        res
    });

    let lowest = window_sums.next().unwrap();
    lowest
        + &window_sums.rev().fold(zero, |mut total, sum_i| {
            total += sum_i;
            for _ in 0..C {
                total.double_in_place();
            }
            total
        })
}

#[inline]
fn make_digits<const W: usize>(
    a: &impl BigInteger,
    digits_count: usize,
    radix: u64,
) -> impl Iterator<Item = i64> + '_ {
    let scalar = a.as_ref();
    let window_mask: u64 = radix - 1;

    let mut carry = 0u64;
    (0..digits_count).map(move |i| {
        let bit_offset = i * W;
        let u64_idx = bit_offset / 64;
        let bit_idx = bit_offset % 64;
        let scalar_at_idx = scalar[u64_idx];
        let bit_buf = if bit_idx < 64 - W || u64_idx == scalar.len() - 1 {
            scalar_at_idx >> bit_idx
        } else {
            let scalar_at_idx_next = scalar[1 + u64_idx];
            (scalar_at_idx >> bit_idx) | (scalar_at_idx_next << (64 - bit_idx))
        };

        let coef = carry + (bit_buf & window_mask);
        carry = (coef + radix / 2) >> W;
        let mut digit = (coef as i64) - (carry << W) as i64;
        if i == digits_count - 1 {
            digit += (carry << W) as i64;
        }
        digit
    })
}

/// Given a vector of field elements {v_i}, compute the vector {coeff * v_i^(-1)}.
pub fn batch_inversion_and_mul<F: Field>(v: &mut [F], coeff: &F) {
    let mut prod = Vec::with_capacity(v.len());
    let mut tmp = F::one();
    for f in v.iter().filter(|f| !f.is_zero()) {
        tmp *= f;
        prod.push(tmp);
    }

    tmp = tmp.inverse().unwrap();
    tmp *= coeff;

    for (f, s) in v
        .iter_mut()
        .rev()
        .filter(|f| !f.is_zero())
        .zip(prod.into_iter().rev().skip(1).chain(Some(F::one())))
    {
        let new_tmp = tmp * *f;
        *f = tmp * &s;
        tmp = new_tmp;
    }
}
