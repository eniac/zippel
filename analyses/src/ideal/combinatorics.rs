//! Var-slot enumeration helpers for polynomial / MLE values.
//!
//! These define the canonical order in which the slots of a polynomial-typed
//! Var are laid out (via `Var::with_index(i)`). They are NOT monomial / term
//! orderings — the `GrevLexTerm` and `ElimMono<E>` orderings in
//! `monomial.rs` are untouched.
//!
//!   * VPoly<N, M> → C(N+M, M) slots, one per multi-index k with |k| ≤ M.
//!   * Mle<N>      → 2^N slots, one per hypercube point b ∈ {0,1}^N.
//!   * Uni(n)      → n slots (coefficient vector).
//!   * Vec(_, n)   → n slots.

use ark_ff::{Field, One};

use crate::frontend::Polynomial;
use backend::ArkConfig;

/// All multi-indices `(k_1, …, k_n)` with `sum(k_i) ≤ m`, in graded-lex order
/// (by total degree, then lex within the same degree).
pub fn multi_indices(n: usize, m: usize) -> Vec<Vec<usize>> {
    fn go(n: usize, budget: usize, acc: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
        if n == 0 {
            out.push(acc.clone());
            return;
        }
        for k in 0..=budget {
            acc.push(k);
            go(n - 1, budget - k, acc, out);
            acc.pop();
        }
    }
    let mut all = Vec::new();
    let mut scratch = Vec::with_capacity(n);
    go(n, m, &mut scratch, &mut all);
    // Sort by (total degree, lex) to get a stable graded-lex enumeration.
    all.sort_by(|a, b| {
        let da: usize = a.iter().sum();
        let db: usize = b.iter().sum();
        da.cmp(&db).then_with(|| a.cmp(b))
    });
    all
}

/// All boolean multi-indices `b ∈ {0,1}^n` in lex order (matches how
/// `Op::Mle(v)` unpacks a length-`2^N` vector).
pub fn hypercube(n: usize) -> Vec<Vec<usize>> {
    (0..(1usize << n))
        .map(|i| (0..n).map(|j| (i >> j) & 1).collect())
        .collect()
}

/// Compute row `i` of the DFT matrix applied to `coeffs`:
///    `Σ_j ω^{i·j} · coeffs[j]`.
///
/// Used by the `Op::Ifft` / `Op::Fft` arms to express the relation
/// between coefficient form and evaluation-at-roots-of-unity form as a
/// set of N linear polynomial equations. The caller is responsible for
/// providing `ω` such that `ω^N = 1` and `ω` has order exactly `N`
/// (typically `C::F::get_root_of_unity(N)`).
pub fn dft_row<C: ArkConfig>(
    coeffs: &[Polynomial<C::F>],
    omega: C::F,
    i: usize,
) -> Polynomial<C::F> {
    let w_step = omega.pow([i as u64]);
    let mut wij = C::F::one();
    let mut acc = Polynomial::<C::F>::zero();
    for c in coeffs.iter() {
        let scalar = Polynomial::<C::F>::lit(&wij);
        acc += c * &scalar;
        wij *= w_step;
    }
    acc
}

/// Compute the Lagrange interpolation basis coefficients for `n` distinct
/// points `x_0, ..., x_{n-1}`. Returns a matrix `L[i][k]` where
/// `L[i][k]` is the coefficient of `X^k` in the Lagrange basis polynomial
/// `L_i(X) = Π_{j≠i} (X - x_j) / (x_i - x_j)`.
pub fn lagrange_basis<F: Field>(xs: &[F]) -> Vec<Vec<F>> {
    let mut basis: Vec<Vec<F>> = Vec::with_capacity(xs.len());

    for (i, xi) in xs.iter().copied().enumerate() {
        let mut denom = F::one();
        for (j, xj) in xs.iter().copied().enumerate() {
            if j != i {
                denom *= xi - xj;
            }
        }
        let denom_inv = denom.inverse().unwrap();

        let mut poly: Vec<F> = vec![F::one()];
        for (j, xj) in xs.iter().copied().enumerate() {
            if j == i {
                continue;
            }
            let neg_xj = -xj;
            let mut new_poly = vec![F::zero(); poly.len() + 1];
            for (k, &c) in poly.iter().enumerate() {
                new_poly[k] += c * neg_xj;
                new_poly[k + 1] += c;
            }
            poly = new_poly;
        }

        for c in &mut poly {
            *c *= denom_inv;
        }

        basis.push(poly);
    }

    basis
}

#[cfg(test)]
mod tests {
    use ark_ff::{One, Zero};

    use backend::ATyp;

    use super::*;

    /// Inverse of the enumeration: position of multi-index / hypercube point `k`
    /// in the canonical slot order for the given type.
    pub fn index_of(typ: &ATyp, k: &[usize]) -> usize {
        match typ {
            ATyp::VPoly(n, m) => multi_indices(*n, *m)
                .iter()
                .position(|kk| kk.as_slice() == k)
                .expect("multi-index out of range for VPoly"),
            ATyp::Mle(n) => {
                debug_assert_eq!(k.len(), *n);
                let mut acc = 0usize;
                for (j, bj) in k.iter().enumerate() {
                    debug_assert!(*bj <= 1);
                    acc |= (bj & 1) << j;
                }
                acc
            }
            _ => 0,
        }
    }

    // -----------------------------------------------------------------
    // Polynomial / MLE enumeration helpers
    // -----------------------------------------------------------------

    #[test]
    fn test_multi_indices_univariate() {
        // Uni degree 3 → 1-variable VPoly with total degree ≤ 3.
        let got = multi_indices(1, 3);
        assert_eq!(got, vec![vec![0], vec![1], vec![2], vec![3]]);
    }

    #[test]
    fn test_multi_indices_two_vars_deg2() {
        // VPoly<2, 2>: all k with k_1 + k_2 ≤ 2, in graded-lex order.
        let got = multi_indices(2, 2);
        assert_eq!(
            got,
            vec![
                vec![0, 0], // deg 0
                vec![0, 1],
                vec![1, 0], // deg 1 (lex)
                vec![0, 2],
                vec![1, 1],
                vec![2, 0], // deg 2 (lex)
            ]
        );
    }

    #[test]
    fn test_hypercube_enumeration() {
        let got = hypercube(3);
        // lex: bit 0 is inner-most, so b = [b0, b1, b2] read little-endian.
        assert_eq!(got[0], vec![0, 0, 0]);
        assert_eq!(got[1], vec![1, 0, 0]);
        assert_eq!(got[2], vec![0, 1, 0]);
        assert_eq!(got[7], vec![1, 1, 1]);
    }

    fn binomial(n: usize, k: usize) -> usize {
        let k = k.min(n - k);
        (0..k).fold(1, |acc, i| acc * (n - i) / (i + 1))
    }

    #[test]
    fn test_binomial_helper_sanity() {
        // Pin well-known values so a bug in the helper doesn't mask bugs
        // in physical_len.
        assert_eq!(binomial(0, 0), 1);
        assert_eq!(binomial(5, 0), 1);
        assert_eq!(binomial(5, 5), 1);
        assert_eq!(binomial(5, 2), 10);
        assert_eq!(binomial(6, 3), 20);
        assert_eq!(binomial(10, 4), 210);
    }

    #[test]
    fn test_physical_len_vpoly_matches_binomial() {
        // VPoly(n, m) has C(n + m, n) coefficient slots.
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=5)?;
            let m: usize = u.int_in_range(0..=5)?;
            let sum = n + m;
            let expected = binomial(sum, n);
            assert_eq!(
                ATyp::VPoly(n, m).physical_len(),
                expected,
                "physical_len(VPoly({n}, {m})) should be C({sum}, {n}) = {expected}",
            );
            Ok(())
        });
    }

    #[test]
    fn test_physical_len_mle_is_power_of_two() {
        // Mle(n) is the multilinear extension over {0,1}^n, so 2^n slots.
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(0..=5)?;
            assert_eq!(
                ATyp::Mle(n).physical_len(),
                1usize << n,
                "physical_len(Mle({n})) should be 2^{n}",
            );
            Ok(())
        });
    }

    #[test]
    fn test_physical_len_uni_is_m_plus_one() {
        // Phase-14 convention: Uni(m) has m+1 coefficient slots.
        arbtest::arbtest(|u| {
            let m: usize = u.int_in_range(0..=15)?;
            assert_eq!(
                ATyp::Uni(m).physical_len(),
                m + 1,
                "physical_len(Uni({m})) should be {} (m + 1)",
                m + 1,
            );
            Ok(())
        });
    }

    #[test]
    fn test_physical_len_vec_is_length() {
        // Vec(t, n) is a base case: exactly n slots regardless of inner type.
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(0..=16)?;
            let disc: u8 = u.int_in_range(0..=3)?;
            let inner = match disc {
                0 => ATyp::scalar(),
                1 => ATyp::unit(),
                2 => ATyp::g1(),
                _ => ATyp::g2(),
            };
            let typ = ATyp::vec(&inner, n);
            assert_eq!(
                typ.physical_len(),
                n,
                "physical_len(Vec(_, {n})) should be {n}"
            );
            Ok(())
        });
    }

    #[test]
    fn test_physical_len_base_is_one() {
        // Every scalar-shaped base type occupies exactly one Var slot.
        // Enumerated explicitly — the set of ABase variants is finite and fixed.
        for typ in [
            ATyp::scalar(),
            ATyp::unit(),
            ATyp::g1(),
            ATyp::g2(),
            ATyp::gt(),
            ATyp::fin(lang::typ::range::CRange::default()),
        ] {
            assert_eq!(typ.physical_len(), 1, "physical_len({typ:?}) should be 1");
        }
    }

    #[test]
    fn test_multi_indices_len_matches_physical_len() {
        // multi_indices(n, m).len() == physical_len(VPoly(n, m)) is definitional.
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=4)?;
            let m: usize = u.int_in_range(0..=4)?;
            assert_eq!(
                multi_indices(n, m).len(),
                ATyp::VPoly(n, m).physical_len(),
                "multi_indices({n}, {m}).len() should equal physical_len(VPoly({n}, {m}))",
            );
            Ok(())
        });
    }

    #[test]
    fn test_hypercube_len_is_power_of_two() {
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(0..=5)?;
            assert_eq!(
                hypercube(n).len(),
                1usize << n,
                "hypercube({n}).len() should be 2^{n}",
            );
            Ok(())
        });
    }

    #[test]
    fn test_index_of_mle_roundtrip_grid() {
        // For an arbitrary position i in 0..2^n the hypercube entry at i
        // must map back to i via index_of.
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=4)?;
            let cube = hypercube(n);
            if cube.is_empty() {
                return Ok(());
            }
            let i: usize = u.int_in_range(0..=(cube.len() - 1))?;
            let b = &cube[i];
            assert_eq!(
                index_of(&ATyp::Mle(n), b),
                i,
                "Mle({n}): position {i} -> {b:?} did not round-trip",
            );
            Ok(())
        });
    }

    #[test]
    fn test_index_of_vpoly_position_roundtrip() {
        // For an arbitrary position i in 0..physical_len the multi-index at
        // that position must map back to i via index_of.
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=4)?;
            let m: usize = u.int_in_range(0..=4)?;
            let mis = multi_indices(n, m);
            if mis.is_empty() {
                return Ok(());
            }
            let i: usize = u.int_in_range(0..=(mis.len() - 1))?;
            let k = &mis[i];
            assert_eq!(
                index_of(&ATyp::VPoly(n, m), k),
                i,
                "VPoly({n}, {m}): position {i} -> {k:?} did not round-trip",
            );
            Ok(())
        });
    }

    #[test]
    fn test_multi_indices_graded_lex_ordering() {
        // multi_indices is graded-lex: ascending by total degree, ties
        // broken by lex on the index vector. Check all consecutive pairs
        // for arbitrary (n, m).
        arbtest::arbtest(|u| {
            let n: usize = u.int_in_range(1..=4)?;
            let m: usize = u.int_in_range(0..=4)?;
            let mis = multi_indices(n, m);
            for w in mis.windows(2) {
                let a = &w[0];
                let b = &w[1];
                let da: usize = a.iter().sum();
                let db: usize = b.iter().sum();
                let ok = da < db || (da == db && a < b);
                assert!(
                    ok,
                    "multi_indices({n}, {m}) violates graded-lex at pair {a:?} -> {b:?} \
                     (sums {da} vs {db})",
                );
            }
            Ok(())
        });
    }

    #[test]
    fn test_lagrange_basis_2_points() {
        use ark_bls12_381::Fr;

        let xs: Vec<Fr> = [0u64, 1].iter().map(|&x| Fr::from(x)).collect();
        let lag = lagrange_basis(&xs);

        assert_eq!(lag.len(), 2);
        assert_eq!(lag[0][0], Fr::one());
        assert_eq!(lag[0][1], -Fr::one());
        assert_eq!(lag[1][0], Fr::zero());
        assert_eq!(lag[1][1], Fr::one());
    }

    #[test]
    fn test_lagrange_basis_3_points() {
        use ark_bls12_381::Fr;

        let xs: Vec<Fr> = [1u64, 2, 3].iter().map(|&x| Fr::from(x)).collect();
        let lag = lagrange_basis(&xs);

        assert_eq!(lag.len(), 3, "3 points → 3 basis polynomials");
        for l in &lag {
            assert_eq!(l.len(), 3, "each L_i has degree ≤ 2 → 3 coefficients");
        }

        let two_inv = Fr::from(2u64).inverse().unwrap();
        assert_eq!(lag[0][0], Fr::from(3u64));
        assert_eq!(lag[0][1], Fr::from(5u64) * (-two_inv));
        assert_eq!(lag[0][2], two_inv);

        for (i, basis_poly) in lag.iter().enumerate() {
            for (j, x) in xs.iter().copied().enumerate() {
                let mut val = Fr::zero();
                let mut xpow = Fr::one();
                for coeff in basis_poly {
                    val += *coeff * xpow;
                    xpow *= x;
                }
                if i == j {
                    assert_eq!(val, Fr::one(), "L_{}({}) should be 1", i, j + 1);
                } else {
                    assert_eq!(val, Fr::zero(), "L_{}({}) should be 0", i, j + 1);
                }
            }
        }
    }
}
