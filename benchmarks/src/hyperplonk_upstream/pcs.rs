//! `subroutines::pcs::multilinear_kzg` (mod.rs, srs.rs, util.rs, batching.rs):
//! multilinear KZG (PST13) with the sumcheck-based batch opening.
//!
//! The `PolynomialCommitmentScheme` trait is dropped (HyperPlonk only ever
//! instantiates it with this scheme); the functions are free functions with
//! upstream's bodies. arkworks 0.4's `FixedBase` window tables are replaced
//! by 0.6's `ScalarMul::batch_mul`, which is the same fixed-base method.

use super::PolyIOPErrors;
use crate::sumcheck_upstream::arithmetic::{
    VPAuxInfo, VirtualPolynomial, build_eq_x_r_vec, eq_eval, evaluate_opt,
};
use crate::sumcheck_upstream::poly_iop::structs::IOPProof;
use crate::sumcheck_upstream::poly_iop::{PolyIOP, SumCheck};
use crate::sumcheck_upstream::transcript::IOPTranscript;
use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::scalar_mul::{ScalarMul, variable_base::VariableBaseMSM};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, One, PrimeField, Zero};
use ark_poly::{DenseMultilinearExtension, MultilinearExtension};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{UniformRand, log2, rand::Rng};
use std::{collections::BTreeMap, iter, marker::PhantomData, ops::Deref, sync::Arc};

type Poly<F> = Arc<DenseMultilinearExtension<F>>;

/// A commitment: one G1 element.
#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Copy, Debug, PartialEq, Eq)]
pub struct Commitment<E: Pairing>(pub E::G1Affine);

/// One level of the prover key: `eq(t[i..], b)·g` for every `b`.
#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Debug)]
pub struct Evaluations<C: AffineRepr> {
    /// The level's bases.
    pub evals: Vec<C>,
}

/// Universal SRS.
#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Debug)]
pub struct MultilinearUniversalParams<E: Pairing> {
    /// Prover key at full size.
    pub prover_param: MultilinearProverParam<E>,
    /// `t_i·h` for every variable.
    pub h_mask: Vec<E::G2Affine>,
}

/// Prover key: `powers_of_g[i]` has `2^(num_vars - i)` bases, and the last
/// level is `[g]`.
#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Debug)]
pub struct MultilinearProverParam<E: Pairing> {
    /// Number of variables supported.
    pub num_vars: usize,
    /// Lagrange-basis levels.
    pub powers_of_g: Vec<Evaluations<E::G1Affine>>,
    /// G1 generator.
    pub g: E::G1Affine,
    /// G2 generator.
    pub h: E::G2Affine,
}

/// Verifier key.
#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Debug)]
pub struct MultilinearVerifierParam<E: Pairing> {
    /// Number of variables supported.
    pub num_vars: usize,
    /// G1 generator.
    pub g: E::G1Affine,
    /// G2 generator.
    pub h: E::G2Affine,
    /// `t_i·h` for every variable.
    pub h_mask: Vec<E::G2Affine>,
}

/// Single-point opening proof: one quotient commitment per variable.
#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Debug, PartialEq, Eq)]
pub struct MultilinearKzgProof<E: Pairing> {
    /// Quotient commitments, first variable first.
    pub proofs: Vec<E::G1Affine>,
}

/// Batch opening proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BatchProof<E: Pairing> {
    /// Sumcheck reducing every claim to one point.
    pub sum_check_proof: IOPProof<E::ScalarField>,
    /// The claimed evaluations, in insertion order.
    pub f_i_eval_at_point_i: Vec<E::ScalarField>,
    /// Opening of the merged polynomial at the sumcheck point.
    pub g_prime_proof: MultilinearKzgProof<E>,
}

fn err(msg: &str) -> PolyIOPErrors {
    PolyIOPErrors::InvalidParameters(msg.to_string())
}

// ---------------------------------------------------------------------------
// srs.rs / util.rs
// ---------------------------------------------------------------------------

fn eq_extension<F: PrimeField>(t: &[F]) -> Vec<DenseMultilinearExtension<F>> {
    let dim = t.len();
    let mut result = Vec::new();
    for (i, &ti) in t.iter().enumerate().take(dim) {
        let mut poly = Vec::with_capacity(1 << dim);
        for x in 0..(1 << dim) {
            let xi = if x >> i & 1 == 1 { F::one() } else { F::zero() };
            let ti_xi = ti * xi;
            poly.push(ti_xi + ti_xi - xi - ti + F::one());
        }
        result.push(DenseMultilinearExtension::from_evaluations_vec(dim, poly));
    }
    result
}

fn remove_dummy_variable<F: Field>(poly: &[F], pad: usize) -> Vec<F> {
    if pad == 0 {
        return poly.to_vec();
    }
    let nv = log2(poly.len()) as usize - pad;
    (0..(1 << nv)).map(|x| poly[x << pad]).collect()
}

impl<E: Pairing> MultilinearUniversalParams<E> {
    /// `gen_srs_for_testing`: sample the trapdoor `t` and expand it.
    ///
    /// # Panics
    /// Panics if `num_vars` is zero.
    pub fn gen_srs_for_testing<R: Rng>(rng: &mut R, num_vars: usize) -> Self {
        assert!(num_vars > 0, "constant polynomial not supported");
        let g = E::G1::rand(rng);
        let h = E::G2::rand(rng);
        let t: Vec<_> = (0..num_vars).map(|_| E::ScalarField::rand(rng)).collect();

        let mut eq = eq_extension(&t);
        let mut eq_arr = std::collections::VecDeque::new();
        let mut base = eq.pop().unwrap().evaluations;
        for i in (0..num_vars).rev() {
            eq_arr.push_front(remove_dummy_variable(&base, i));
            if i != 0 {
                let mul = eq.pop().unwrap().evaluations;
                base = base.into_iter().zip(mul).map(|(a, b)| a * b).collect();
            }
        }

        let mut pp_powers = Vec::new();
        for i in 0..num_vars {
            let eq = eq_arr.pop_front().unwrap();
            pp_powers.extend((0..(1 << (num_vars - i))).map(|x| eq[x]));
        }
        let pp_g = g.batch_mul(&pp_powers);

        let mut powers_of_g = Vec::new();
        let mut start = 0;
        for i in 0..num_vars {
            let size = 1 << (num_vars - i);
            powers_of_g.push(Evaluations {
                evals: pp_g[start..start + size].to_vec(),
            });
            start += size;
        }
        powers_of_g.push(Evaluations {
            evals: vec![g.into_affine()],
        });

        let h_mask = h.batch_mul(&t);
        Self {
            prover_param: MultilinearProverParam {
                num_vars,
                g: g.into_affine(),
                h: h.into_affine(),
                powers_of_g,
            },
            h_mask,
        }
    }

    /// `trim`: keys for `supported_num_vars` variables.
    ///
    /// # Panics
    /// Panics if the SRS is too small.
    pub fn trim(
        &self,
        supported_num_vars: usize,
    ) -> (MultilinearProverParam<E>, MultilinearVerifierParam<E>) {
        assert!(supported_num_vars <= self.prover_param.num_vars);
        let to_reduce = self.prover_param.num_vars - supported_num_vars;
        let ck = MultilinearProverParam {
            powers_of_g: self.prover_param.powers_of_g[to_reduce..].to_vec(),
            g: self.prover_param.g,
            h: self.prover_param.h,
            num_vars: supported_num_vars,
        };
        let vk = MultilinearVerifierParam {
            num_vars: supported_num_vars,
            g: self.prover_param.g,
            h: self.prover_param.h,
            h_mask: self.h_mask[to_reduce..].to_vec(),
        };
        (ck, vk)
    }
}

// ---------------------------------------------------------------------------
// mod.rs
// ---------------------------------------------------------------------------

/// `commit`: one MSM against the full-size level.
///
/// # Errors
/// Fails if the polynomial has more variables than the key.
pub fn commit<E: Pairing>(
    prover_param: &MultilinearProverParam<E>,
    poly: &Poly<E::ScalarField>,
) -> Result<Commitment<E>, PolyIOPErrors> {
    if prover_param.num_vars < poly.num_vars {
        return Err(err("MlE length exceeds param limit"));
    }
    let ignored = prover_param.num_vars - poly.num_vars;
    let scalars: Vec<_> = poly.to_evaluations();
    let commitment =
        E::G1::msm_unchecked(&prover_param.powers_of_g[ignored].evals, scalars.as_slice())
            .into_affine();
    Ok(Commitment(commitment))
}

/// `open_internal`.
///
/// # Errors
/// Fails on a size mismatch.
pub fn open<E: Pairing>(
    prover_param: &MultilinearProverParam<E>,
    polynomial: &DenseMultilinearExtension<E::ScalarField>,
    point: &[E::ScalarField],
) -> Result<(MultilinearKzgProof<E>, E::ScalarField), PolyIOPErrors> {
    if polynomial.num_vars() > prover_param.num_vars {
        return Err(err("Polynomial num_vars exceed the limit"));
    }
    if polynomial.num_vars() != point.len() {
        return Err(err("Polynomial num_vars does not match point len"));
    }

    let nv = polynomial.num_vars();
    let ignored = prover_param.num_vars - nv + 1;
    let mut f = polynomial.to_evaluations();

    let mut proofs = Vec::new();

    for (i, (&point_at_k, gi)) in point
        .iter()
        .zip(prover_param.powers_of_g[ignored..ignored + nv].iter())
        .enumerate()
    {
        let k = nv - 1 - i;
        let cur_dim = 1 << k;
        let mut q = vec![E::ScalarField::zero(); cur_dim];
        let mut r = vec![E::ScalarField::zero(); cur_dim];

        for b in 0..(1 << k) {
            q[b] = f[(b << 1) + 1] - f[b << 1];
            r[b] = f[b << 1] + (q[b] * point_at_k);
        }
        f = r;

        proofs.push(E::G1::msm_unchecked(&gi.evals, &q).into_affine());
    }
    let eval = evaluate_opt(polynomial, point);
    Ok((MultilinearKzgProof { proofs }, eval))
}

/// `verify_internal`: one multi-pairing.
///
/// # Errors
/// Fails if the point is longer than the key supports.
pub fn verify<E: Pairing>(
    verifier_param: &MultilinearVerifierParam<E>,
    commitment: &Commitment<E>,
    point: &[E::ScalarField],
    value: &E::ScalarField,
    proof: &MultilinearKzgProof<E>,
) -> Result<bool, PolyIOPErrors> {
    let num_var = point.len();
    if num_var > verifier_param.num_vars {
        return Err(err("point length exceeds param limit"));
    }

    let h_mul: Vec<E::G2Affine> = verifier_param.h.into_group().batch_mul(point);

    let ignored = verifier_param.num_vars - num_var;
    let h_vec: Vec<_> = (0..num_var)
        .map(|i| verifier_param.h_mask[ignored + i].into_group() - h_mul[i])
        .collect();
    let h_vec: Vec<E::G2Affine> = E::G2::normalize_batch(&h_vec);

    let mut pairings: Vec<_> = proof
        .proofs
        .iter()
        .map(|&x| E::G1Prepared::from(x))
        .zip(h_vec.into_iter().take(num_var).map(E::G2Prepared::from))
        .collect();

    pairings.push((
        E::G1Prepared::from((verifier_param.g * *value - commitment.0.into_group()).into_affine()),
        E::G2Prepared::from(verifier_param.h),
    ));

    let ps = pairings.iter().map(|(p, _)| p.clone());
    let hs = pairings.iter().map(|(_, h)| h.clone());

    Ok(E::multi_pairing(ps, hs) == PairingOutput(E::TargetField::one()))
}

// ---------------------------------------------------------------------------
// batching.rs
// ---------------------------------------------------------------------------

/// `multi_open_internal`: reduce every `(poly_i, point_i)` claim to one
/// opening of a merged polynomial via a degree-2 sumcheck.
///
/// # Errors
/// Fails if the sumcheck or the final opening fails.
pub fn multi_open<E: Pairing>(
    prover_param: &MultilinearProverParam<E>,
    polynomials: &[Poly<E::ScalarField>],
    points: &[Vec<E::ScalarField>],
    evals: &[E::ScalarField],
    transcript: &mut IOPTranscript<E::ScalarField>,
) -> Result<BatchProof<E>, PolyIOPErrors> {
    for eval_point in points {
        transcript.append_serializable_element(b"eval_point", eval_point)?;
    }
    for eval in evals {
        transcript.append_field_element(b"eval", eval)?;
    }

    let num_var = polynomials[0].num_vars;
    let k = polynomials.len();
    let ell = log2(k) as usize;

    let t = transcript.get_and_append_challenge_vectors(b"t", ell)?;

    let eq_t_i_list = build_eq_x_r_vec(t.as_ref())?;

    let point_indices = points
        .iter()
        .fold(BTreeMap::<_, _>::new(), |mut indices, point| {
            let idx = indices.len();
            indices.entry(point).or_insert(idx);
            indices
        });
    let deduped_points =
        BTreeMap::from_iter(point_indices.iter().map(|(point, idx)| (*idx, *point)))
            .into_values()
            .collect::<Vec<_>>();
    let merged_tilde_gs = polynomials
        .iter()
        .zip(points.iter())
        .zip(eq_t_i_list.iter())
        .fold(
            iter::repeat_with(DenseMultilinearExtension::zero)
                .map(Arc::new)
                .take(point_indices.len())
                .collect::<Vec<_>>(),
            |mut merged_tilde_gs, ((poly, point), coeff)| {
                *Arc::make_mut(&mut merged_tilde_gs[point_indices[point]]) +=
                    (*coeff, poly.deref());
                merged_tilde_gs
            },
        );

    let tilde_eqs: Vec<_> = deduped_points
        .iter()
        .map(|point| {
            let eq_b_zi = build_eq_x_r_vec(point).unwrap();
            Arc::new(DenseMultilinearExtension::from_evaluations_vec(
                num_var, eq_b_zi,
            ))
        })
        .collect();

    let mut sum_check_vp = VirtualPolynomial::new(num_var);
    for (merged_tilde_g, tilde_eq) in merged_tilde_gs.iter().zip(tilde_eqs) {
        sum_check_vp.add_mle_list([merged_tilde_g.clone(), tilde_eq], E::ScalarField::one())?;
    }

    let proof =
        <PolyIOP<E::ScalarField> as SumCheck<E::ScalarField>>::prove(&sum_check_vp, transcript)?;

    let a2 = &proof.point[..num_var];

    let mut g_prime = Arc::new(DenseMultilinearExtension::zero());
    for (merged_tilde_g, point) in merged_tilde_gs.iter().zip(deduped_points.iter()) {
        let eq_i_a2 = eq_eval(a2, point)?;
        *Arc::make_mut(&mut g_prime) += (eq_i_a2, merged_tilde_g.deref());
    }

    let (g_prime_proof, _g_prime_eval) = open(prover_param, &g_prime, a2)?;

    Ok(BatchProof {
        sum_check_proof: proof,
        f_i_eval_at_point_i: evals.to_vec(),
        g_prime_proof,
    })
}

/// `batch_verify_internal`.
///
/// # Errors
/// Fails if the sumcheck is malformed.
pub fn batch_verify<E: Pairing>(
    verifier_param: &MultilinearVerifierParam<E>,
    f_i_commitments: &[Commitment<E>],
    points: &[Vec<E::ScalarField>],
    proof: &BatchProof<E>,
    transcript: &mut IOPTranscript<E::ScalarField>,
) -> Result<bool, PolyIOPErrors> {
    for eval_point in points {
        transcript.append_serializable_element(b"eval_point", eval_point)?;
    }
    for eval in &proof.f_i_eval_at_point_i {
        transcript.append_field_element(b"eval", eval)?;
    }

    let k = f_i_commitments.len();
    let ell = log2(k) as usize;
    let num_var = proof.sum_check_proof.point.len();

    let t = transcript.get_and_append_challenge_vectors(b"t", ell)?;

    let a2 = &proof.sum_check_proof.point[..num_var];

    let eq_t_list = build_eq_x_r_vec(t.as_ref())?;

    let mut scalars = vec![];
    let mut bases = vec![];

    for (i, point) in points.iter().enumerate() {
        let eq_i_a2 = eq_eval(a2, point)?;
        scalars.push(eq_i_a2 * eq_t_list[i]);
        bases.push(f_i_commitments[i].0);
    }
    let g_prime_commit = E::G1::msm_unchecked(&bases, &scalars);

    let mut sum = E::ScalarField::zero();
    for (i, &e) in eq_t_list.iter().enumerate().take(k) {
        sum += e * proof.f_i_eval_at_point_i[i];
    }
    let aux_info = VPAuxInfo {
        max_degree: 2,
        num_variables: num_var,
        phantom: PhantomData,
    };
    let subclaim = <PolyIOP<E::ScalarField> as SumCheck<E::ScalarField>>::verify(
        sum,
        &proof.sum_check_proof,
        &aux_info,
        transcript,
    )?;
    let tilde_g_eval = subclaim.expected_evaluation;

    verify(
        verifier_param,
        &Commitment(g_prime_commit.into_affine()),
        a2,
        &tilde_g_eval,
        &proof.g_prime_proof,
    )
}
