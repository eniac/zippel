//! A total order on [`PolyVariant`], consistent with its derived structural equality: the
//! same encoding with the same contents is equal; different encodings of one polynomial are
//! not.

use ark_ff::PrimeField;
use std::cmp::Ordering;

use super::PolyVariant;

impl<F: PrimeField> PartialOrd for PolyVariant<F> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Lexicographic order of field-element sequences, by canonical integer.
fn cmp_field_seq<'a, F: PrimeField + 'a>(
    a: impl Iterator<Item = &'a F>,
    b: impl Iterator<Item = &'a F>,
) -> Ordering {
    a.map(|x| x.into_bigint()).cmp(b.map(|x| x.into_bigint()))
}

impl<F: PrimeField> Ord for PolyVariant<F> {
    /// Univariates < dense MLEs < sparse multivariates < sparse MLEs; within
    /// an encoding, by size and then contents. Consistent with `Eq`: a dense
    /// and a sparse univariate with the same coefficients order dense first.
    fn cmp(&self, other: &Self) -> Ordering {
        use PolyVariant::{DenseMle, DenseUni, SparseMle, SparseMultivariate, SparseUni};
        let rank = |p: &Self| match p {
            DenseUni(_) | SparseUni(_) => 0,
            DenseMle(_) => 1,
            SparseMultivariate(_) => 2,
            SparseMle { .. } => 3,
        };
        rank(self)
            .cmp(&rank(other))
            .then_with(|| match (self, other) {
                (DenseUni(_) | SparseUni(_), DenseUni(_) | SparseUni(_)) => {
                    let (a, b) = (self.to_coeffs().unwrap(), other.to_coeffs().unwrap());
                    a.len()
                        .cmp(&b.len())
                        .then_with(|| cmp_field_seq(a.iter(), b.iter()))
                        .then_with(|| {
                            matches!(self, SparseUni(_)).cmp(&matches!(other, SparseUni(_)))
                        })
                }
                (DenseMle(a), DenseMle(b)) => a
                    .num_vars
                    .cmp(&b.num_vars)
                    .then_with(|| cmp_field_seq(a.evaluations.iter(), b.evaluations.iter())),
                (SparseMultivariate(a), SparseMultivariate(b)) => a
                    .num_vars
                    .cmp(&b.num_vars)
                    .then_with(|| a.terms.len().cmp(&b.terms.len()))
                    .then_with(|| {
                        a.terms
                            .iter()
                            .map(|(c, t)| (c.into_bigint(), t))
                            .cmp(b.terms.iter().map(|(c, t)| (c.into_bigint(), t)))
                    }),
                (
                    SparseMle {
                        num_vars: n1,
                        evals: e1,
                    },
                    SparseMle {
                        num_vars: n2,
                        evals: e2,
                    },
                ) => n1.cmp(n2).then_with(|| {
                    e1.iter()
                        .map(|(i, v)| (*i, v.into_bigint()))
                        .cmp(e2.iter().map(|(i, v)| (*i, v.into_bigint())))
                }),
                _ => unreachable!("equal ranks are the same encoding"),
            })
    }
}
