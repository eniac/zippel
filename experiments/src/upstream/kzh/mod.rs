//! KZH-k multilinear polynomial commitment, ported from irondict
//! (`subroutines/src/pcs/kzhk`, github.com/alireza-shirzad/irondict @ bf2369d)
//! to arkworks 0.6. The scheme is Figure 12 of KZH-Fold (eprint 2025/144);
//! the benchmarks run it at k = 2.
//!
//! Ported: SRS generation, dense commit, dense open at an arbitrary point
//! (`open_dense_non_bool_inner`) and the non-zk verifier, plus the
//! `arithmetic` helpers they call (`build_eq_x_r_vec`, `fix_last_variables`).
//! Left out: sparse polynomials, Boolean-point preprocessing (aux), the zk
//! variant and batching; none is on the dense single-opening path.
//!
//! Changes from upstream:
//!   - The verifier returns `Ok(false)` when a check fails. Upstream only
//!     `debug_assert!`s the pairing product, `assert_eq!`s the C_{k-1} check
//!     and computes the evaluation check without using it, then returns
//!     `Ok(true)`. The same checks are computed either way.
//!   - `msm_wrapper_g1` calls arkworks' MSM in the caller's rayon pool.
//!     Upstream builds a fresh pool of up to 64 threads per MSM, which would
//!     ignore the benchmark's thread count.
//!   - `ndarray` tensors are flat vectors in the same (C) order.

use ark_ec::{
    AffineRepr, CurveGroup, VariableBaseMSM, pairing::Pairing, scalar_mul::BatchMulPreprocessing,
};
use ark_ff::{Field, One, PrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{UniformRand, rand::Rng};
use rayon::prelude::*;

/// Universal parameters: `h_tensors[t]` is H_{t+1} of Figure 12, flattened in
/// C order over the dimensions `t..k`; `v_mat[j][i] = µ_{i,j} · V`.
#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Debug)]
pub struct UniversalParams<E: Pairing> {
    pub dimensions: Vec<usize>,
    pub h_tensors: Vec<Vec<E::G1Affine>>,
    pub v_mat: Vec<Vec<E::G2Affine>>,
    pub v: E::G2Affine,
    pub g: E::G1Affine,
}

pub struct ProverParam<E: Pairing> {
    pub dimensions: Vec<usize>,
    pub h_tensors: Vec<Vec<E::G1Affine>>,
}

pub struct VerifierParam<E: Pairing> {
    pub dimensions: Vec<usize>,
    /// H_k, the last tensor (a vector of length 2^{d_{k-1}}).
    pub h_tensor: Vec<E::G1Affine>,
    pub minus_v: E::G2Affine,
    pub v_mat: Vec<Vec<E::G2Prepared>>,
}

#[derive(Clone, Debug)]
pub struct OpeningProof<E: Pairing> {
    /// D_1, ..., D_{k-1}.
    pub d: Vec<Vec<E::G1Affine>>,
    /// T_k: evaluations of the partially evaluated polynomial.
    pub f: Vec<E::ScalarField>,
}

impl<E: Pairing> UniversalParams<E> {
    /// Upstream `KZHKUniversalParams::gen_srs_for_testing` (non-zk).
    pub fn gen_srs_for_testing<R: Rng>(rng: &mut R, k: usize, num_vars: usize) -> Self {
        // ----- Dimensions: split num_vars across k -----
        let d = num_vars / k;
        let remainder_d = num_vars % k;
        let mut dimensions = vec![d; k];
        for dim in dimensions.iter_mut().take(remainder_d) {
            *dim += 1;
        }

        // ----- Public generators -----
        let g = E::G1::rand(rng);
        let _h = E::G1::rand(rng); // hiding generator; kept so the rng stream matches upstream
        let v = E::G2::rand(rng);

        // ----- Trapdoors mu_mat: mu_mat[j].len() = 2^{d_j} -----
        let mu_mat: Vec<Vec<E::ScalarField>> = (0..k)
            .map(|j| {
                (0..(1usize << dimensions[j]))
                    .map(|_| E::ScalarField::rand(rng))
                    .collect()
            })
            .collect();

        // ---------- H_t tensors ----------
        let mut h_tensors = Vec::with_capacity(k);
        for t in 0..k {
            let shape: Vec<usize> = dimensions[t..].iter().map(|&dj| 1usize << dj).collect();
            let len: usize = shape.iter().product();

            // exps[r_t, ..., r_{k-1}] = ∏_{j=t}^{k-1} mu_mat[j][r_j], C order.
            let mut exps = vec![E::ScalarField::one(); len];
            let mut axis_stride = 1usize;
            for a in (0..shape.len()).rev() {
                let size_a = shape[a];
                let block = size_a * axis_stride;
                let mu_j = &mu_mat[t + a];
                exps.par_chunks_mut(block).for_each(|chunk| {
                    for (r, mu) in mu_j.iter().enumerate().take(size_a) {
                        for e in &mut chunk[r * axis_stride..(r + 1) * axis_stride] {
                            *e *= mu;
                        }
                    }
                });
                axis_stride *= size_a;
            }

            let table_g = BatchMulPreprocessing::new(g, len);
            h_tensors.push(table_g.batch_mul(&exps));
        }

        // ---------- v_mat ----------
        let v_mat = (0..k)
            .into_par_iter()
            .map(|j| {
                let table_v = BatchMulPreprocessing::new(v, 1usize << dimensions[j]);
                table_v.batch_mul(&mu_mat[j])
            })
            .collect();

        Self {
            dimensions,
            h_tensors,
            v_mat,
            v: v.into_affine(),
            g: g.into_affine(),
        }
    }

    pub fn trim(&self) -> (ProverParam<E>, VerifierParam<E>) {
        let k = self.dimensions.len();
        (
            ProverParam {
                dimensions: self.dimensions.clone(),
                h_tensors: self.h_tensors.clone(),
            },
            VerifierParam {
                dimensions: self.dimensions.clone(),
                h_tensor: self.h_tensors[k - 1].clone(),
                minus_v: (-self.v.into_group()).into_affine(),
                v_mat: self
                    .v_mat
                    .iter()
                    .map(|row| row.iter().copied().map(E::G2Prepared::from).collect())
                    .collect(),
            },
        )
    }
}

fn msm_wrapper_g1<E: Pairing>(bases: &[E::G1Affine], scalars: &[E::ScalarField]) -> E::G1 {
    assert_eq!(bases.len(), scalars.len());
    if bases.len() == 1 {
        return bases[0].mul_bigint(scalars[0].into_bigint());
    }
    E::G1::msm_unchecked(bases, scalars)
}

/// Upstream `commit_dense_inner`: C = <T, H_1>.
pub fn commit<E: Pairing>(pp: &ProverParam<E>, evals: &[E::ScalarField]) -> E::G1Affine {
    msm_wrapper_g1::<E>(&pp.h_tensors[0], evals).into_affine()
}

/// Upstream `open_dense_non_bool_inner`.
pub fn open<E: Pairing>(
    pp: &ProverParam<E>,
    evals: &[E::ScalarField],
    point: &[E::ScalarField],
) -> (OpeningProof<E>, E::ScalarField) {
    let k = pp.dimensions.len();
    let decomposed_point = decompose_point(&pp.dimensions, point);
    let mut partial = evals.to_vec();
    let mut d = Vec::with_capacity(k - 1);
    for (j, point_part) in decomposed_point.iter().take(k - 1).enumerate() {
        let num_chunks = 1usize << pp.dimensions[j];
        assert_eq!(partial.len() % num_chunks, 0);
        let chunk_len = partial.len() / num_chunks;
        let h_slice = &pp.h_tensors[j + 1];
        let dj: Vec<E::G1Affine> = (0..num_chunks)
            .into_par_iter()
            .map(|i| {
                let off = i * chunk_len;
                msm_wrapper_g1::<E>(h_slice, &partial[off..off + chunk_len]).into_affine()
            })
            .collect();
        d.push(dj);
        partial = fix_last_variables(&partial, point_part);
    }
    let eval = fix_last_variables(&partial, &decomposed_point[k - 1])[0];
    (OpeningProof { d, f: partial }, eval)
}

/// Upstream `verify_non_zk`, returning the checks' outcome.
pub fn verify<E: Pairing>(
    vp: &VerifierParam<E>,
    commitment: &E::G1Affine,
    point: &[E::ScalarField],
    value: &E::ScalarField,
    proof: &OpeningProof<E>,
) -> bool {
    let k = vp.dimensions.len();
    let mut cj = *commitment;
    let decomposed_point = decompose_point(&vp.dimensions, point);
    let mut ok = true;

    for (j, point_part) in decomposed_point.iter().take(k - 1).enumerate() {
        let mut g1_terms = Vec::with_capacity(1 + proof.d[j].len());
        let mut g2_terms = Vec::with_capacity(1 + vp.v_mat[j].len());
        g1_terms.push(E::G1Prepared::from(cj));
        g2_terms.push(E::G2Prepared::from(vp.minus_v));
        g1_terms.extend(proof.d[j].iter().copied().map(E::G1Prepared::from));
        g2_terms.extend(vp.v_mat[j].iter().cloned());
        ok &= E::multi_pairing(g1_terms, g2_terms).is_zero();

        let eq_poly = build_eq_x_r_vec(point_part);
        cj = msm_wrapper_g1::<E>(&proof.d[j], &eq_poly).into_affine();
    }
    // Checking C_{k-1} = <T_k, H_k>
    ok &= cj == E::G1::msm(&vp.h_tensor, &proof.f).unwrap().into_affine();
    // Evaluation check <T_k, x_k> = y
    ok &= fix_last_variables(&proof.f, &decomposed_point[k - 1])[0] == *value;
    ok
}

fn decompose_point<F: Clone>(dimensions: &[usize], point: &[F]) -> Vec<Vec<F>> {
    let mut decomposed = Vec::new();
    let mut start = 0;
    for &dim in dimensions {
        decomposed.push(point[start..start + dim].to_vec());
        start += dim;
    }
    decomposed
}

/// `arithmetic::build_eq_x_r_vec`: eq(x, r) over x ∈ {0,1}^n, r[0] the low bit.
pub fn build_eq_x_r_vec<F: PrimeField>(r: &[F]) -> Vec<F> {
    assert!(!r.is_empty(), "r length is 0");
    let mut buf = vec![F::one() - r[r.len() - 1], r[r.len() - 1]];
    for &ri in r.iter().rev().skip(1) {
        let mut res = vec![F::zero(); buf.len() << 1];
        res.par_iter_mut().enumerate().for_each(|(i, val)| {
            let bi = buf[i >> 1];
            let tmp = ri * bi;
            *val = if i & 1 == 0 { bi - tmp } else { tmp };
        });
        buf = res;
    }
    buf
}

/// `arithmetic::fix_last_variables` on an evaluation vector: binds the last
/// `partial_point.len()` variables (partial_point[0] the lowest of them).
pub fn fix_last_variables<F: Field>(evals: &[F], partial_point: &[F]) -> Vec<F> {
    let nv = evals.len().trailing_zeros() as usize;
    let nu = partial_point.len();
    assert!(nu <= nv, "invalid size of partial point");
    let mu = nv - nu;

    if partial_point.iter().all(|x| x.is_zero() || x.is_one()) {
        let mut target = 0usize;
        for (i, bit) in partial_point.iter().enumerate() {
            if bit.is_one() {
                target |= 1 << i;
            }
        }
        let size = 1usize << mu;
        return evals[target * size..(target + 1) * size].to_vec();
    }

    let mut current = evals.to_vec();
    for (i, point) in partial_point.iter().rev().enumerate() {
        current = fix_last_variable_helper(&current, nv - i, point);
    }
    current.truncate(1 << mu);
    current
}

fn fix_last_variable_helper<F: Field>(data: &[F], nv: usize, point: &F) -> Vec<F> {
    let half_len = 1usize << (nv - 1);
    let mut res = vec![F::zero(); half_len];
    res.par_iter_mut().enumerate().for_each(|(i, x)| {
        *x = data[i] + (data[i + half_len] - data[i]) * point;
    });
    res
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::{Bls12_381, Fr};
    use ark_std::rand::{SeedableRng, rngs::StdRng};

    /// Upstream `test_single_helper` for dense polynomials at k = 2, 3.
    #[test]
    fn dense_roundtrip() {
        let mut rng = StdRng::seed_from_u64(1);
        for (k, nv) in [(2, 6), (2, 7), (3, 7)] {
            let srs = UniversalParams::<Bls12_381>::gen_srs_for_testing(&mut rng, k, nv);
            let (pp, vp) = srs.trim();
            let evals: Vec<Fr> = (0..1 << nv).map(|_| Fr::rand(&mut rng)).collect();
            let point: Vec<Fr> = (0..nv).map(|_| Fr::rand(&mut rng)).collect();
            let com = commit(&pp, &evals);
            let (proof, value) = open(&pp, &evals, &point);
            assert!(verify(&vp, &com, &point, &value, &proof));
            assert!(!verify(&vp, &com, &point, &(value + Fr::one()), &proof));
            let mut bad = proof.clone();
            bad.d[0][0] = (bad.d[0][0].into_group() + srs.g).into_affine();
            assert!(!verify(&vp, &com, &point, &value, &bad));
        }
    }
}
