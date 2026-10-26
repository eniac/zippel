//! An iterative radix-2 FFT over any [`Field`] with a power-of-two domain.

use super::Field;
use rayon::prelude::*;

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
