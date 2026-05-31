//! Shared Cyclic-n / Katsura-n polynomial generators.
//!
//! Used by the Criterion bench (`benches/groebner.rs`) and the
//! correctness regression suite (`tests/groebner_correctness.rs`,
//! `tests/groebner_sage.rs`).

#![allow(dead_code)]

use std::sync::Arc;

use ark_bls12_381::Fr;
use ark_ff::One;
use ark_gb::monomial::Monomial;
use ark_gb::poly::Poly;
use ark_gb::ring::Ring;

// ---------------------------------------------------------------------------
// Bench sizes
// ---------------------------------------------------------------------------

pub const KATSURA_GREVLEX_SIZES: &[usize] = &[3, 4, 5];
pub const KATSURA_ELIM_SIZES: &[usize] = &[3, 4, 5];
pub const CYCLIC_SIZES: &[usize] = &[4, 5];

// ---------------------------------------------------------------------------
// Ring constructors.
// ---------------------------------------------------------------------------

pub fn grevlex_ring(nvars: usize) -> Arc<Ring<Fr>> {
    Arc::new(Ring::<Fr>::new(nvars as u32).expect("nvars within ark-gb limits"))
}

/// "Elimination ring" — same Ring<Fr>, but polys will use OddElimTerm.
pub fn elim_ring(nvars: usize) -> Arc<Ring<Fr>> {
    Arc::new(Ring::<Fr>::new(nvars as u32).expect("nvars within ark-gb limits"))
}

// ---------------------------------------------------------------------------
// Monomial + polynomial helpers, M-parametric.
// ---------------------------------------------------------------------------

fn unit_mono<M: Monomial<Fr>>(ring: &Ring<Fr>) -> M {
    M::one(ring)
}

fn var_mono<M: Monomial<Fr>>(ring: &Ring<Fr>, i: usize) -> M {
    let nvars = ring.nvars() as usize;
    let mut e = vec![0u32; nvars];
    e[i] = 1;
    M::from_exponents(ring, &e).unwrap()
}

pub fn var_poly<M: Monomial<Fr>>(ring: &Ring<Fr>, i: usize) -> Poly<Fr, M> {
    Poly::from_terms(ring, vec![(Fr::one(), var_mono::<M>(ring, i))])
}

pub fn one_poly<M: Monomial<Fr>>(ring: &Ring<Fr>) -> Poly<Fr, M> {
    Poly::from_terms(ring, vec![(Fr::one(), unit_mono::<M>(ring))])
}

pub fn product_poly<M: Monomial<Fr>, I>(ring: &Ring<Fr>, factors: I) -> Poly<Fr, M>
where
    I: IntoIterator<Item = Poly<Fr, M>>,
{
    let mut acc = one_poly::<M>(ring);
    for f in factors {
        acc = acc.mul(&f, ring);
    }
    acc
}

// ---------------------------------------------------------------------------
// Cyclic-n
// ---------------------------------------------------------------------------

pub fn cyclic_polys<M: Monomial<Fr>>(ring: &Ring<Fr>) -> Vec<Poly<Fr, M>> {
    let n = ring.nvars() as usize;
    assert!(n >= 1);

    let mut polys = Vec::with_capacity(n);
    for j in 0..n.saturating_sub(1) {
        let mut t = Poly::<Fr, M>::zero();
        for i in 0..n {
            let factors = (0..=j).map(|k| var_poly::<M>(ring, (i + k) % n));
            let prod = product_poly(ring, factors);
            t = t.add(&prod, ring);
        }
        polys.push(t);
    }
    let full = product_poly::<M, _>(ring, (0..n).map(|i| var_poly::<M>(ring, i)));
    polys.push(full.sub(&one_poly::<M>(ring), ring));
    polys
}

// ---------------------------------------------------------------------------
// Katsura-n
// ---------------------------------------------------------------------------

pub fn katsura_polys<M: Monomial<Fr>>(ring: &Ring<Fr>) -> Vec<Poly<Fr, M>> {
    let n_arg = ring.nvars() as usize;
    assert!(n_arg >= 1);
    let n = (n_arg - 1) as isize;

    let kat_var = |i: isize| -> Option<Poly<Fr, M>> {
        let ai = i.unsigned_abs();
        if (ai as isize) <= n {
            Some(var_poly::<M>(ring, ai))
        } else {
            None
        }
    };

    let mut polys = Vec::with_capacity(n_arg);

    let mut lin = Poly::<Fr, M>::zero();
    for i in -n..=n {
        if let Some(v) = kat_var(i) {
            lin = lin.add(&v, ring);
        }
    }
    lin = lin.sub(&one_poly::<M>(ring), ring);
    polys.push(lin);

    for i in 0..n {
        let mut q = Poly::<Fr, M>::zero();
        for j in -n..=n {
            if let (Some(a), Some(b)) = (kat_var(j), kat_var(i - j)) {
                let prod = a.mul(&b, ring);
                q = q.add(&prod, ring);
            }
        }
        if let Some(v) = kat_var(i) {
            q = q.sub(&v, ring);
        }
        polys.push(q);
    }
    polys
}

// ---------------------------------------------------------------------------
// Convenience
// ---------------------------------------------------------------------------

pub fn cyclic_input<M: Monomial<Fr>>(n: usize, ring: &Arc<Ring<Fr>>) -> Vec<Poly<Fr, M>> {
    assert_eq!(ring.nvars() as usize, n);
    cyclic_polys::<M>(ring)
}

pub fn katsura_input<M: Monomial<Fr>>(n: usize, ring: &Arc<Ring<Fr>>) -> Vec<Poly<Fr, M>> {
    assert_eq!(ring.nvars() as usize, n);
    katsura_polys::<M>(ring)
}
