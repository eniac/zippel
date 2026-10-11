//! `subroutines::poly_iop::{zero_check, prod_check, perm_check}`.
//!
//! The `ZeroCheck` / `ProductCheck` / `PermutationCheck` traits on `PolyIOP`
//! are flattened into free functions with upstream's bodies; the sumcheck
//! they sit on is `crate::sumcheck_upstream`.

use super::PolyIOPErrors;
use super::pcs::{self, Commitment, MultilinearProverParam};
use crate::sumcheck_upstream::arithmetic::{
    VPAuxInfo, VirtualPolynomial, eq_eval, get_index, identity_permutation_mles,
};
use crate::sumcheck_upstream::poly_iop::structs::IOPProof;
use crate::sumcheck_upstream::poly_iop::{PolyIOP, SumCheck};
use crate::sumcheck_upstream::transcript::IOPTranscript;
use ark_ec::pairing::Pairing;
use ark_ff::{One, PrimeField, Zero, batch_inversion};
use ark_poly::DenseMultilinearExtension;
use std::sync::Arc;

type Poly<F> = Arc<DenseMultilinearExtension<F>>;

// ---------------------------------------------------------------------------
// zero_check/mod.rs
// ---------------------------------------------------------------------------

/// `ZeroCheckSubClaim`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ZeroCheckSubClaim<F: PrimeField> {
    /// The sumcheck point.
    pub point: Vec<F>,
    /// Expected value of the checked polynomial at `point`.
    pub expected_evaluation: F,
    /// The zerocheck's `r`.
    pub init_challenge: Vec<F>,
}

/// `ZeroCheck::prove`: sumcheck on `f(x)·eq(x, r)`.
///
/// # Errors
/// Propagates sumcheck and transcript errors.
pub fn zero_check_prove<F: PrimeField>(
    poly: &VirtualPolynomial<F>,
    transcript: &mut IOPTranscript<F>,
) -> Result<IOPProof<F>, PolyIOPErrors> {
    let length = poly.aux_info.num_variables;
    let r = transcript.get_and_append_challenge_vectors(b"0check r", length)?;
    let f_hat = poly.build_f_hat(r.as_ref())?;
    <PolyIOP<F> as SumCheck<F>>::prove(&f_hat, transcript)
}

/// `ZeroCheck::verify`.
///
/// # Errors
/// Fails if the first round does not sum to zero or the sumcheck fails.
pub fn zero_check_verify<F: PrimeField>(
    proof: &IOPProof<F>,
    fx_aux_info: &VPAuxInfo<F>,
    transcript: &mut IOPTranscript<F>,
) -> Result<ZeroCheckSubClaim<F>, PolyIOPErrors> {
    if proof.proofs[0].evaluations[0] + proof.proofs[0].evaluations[1] != F::zero() {
        return Err(PolyIOPErrors::InvalidProof(
            "zero check: sum is not zero".to_string(),
        ));
    }

    let length = fx_aux_info.num_variables;
    let r = transcript.get_and_append_challenge_vectors(b"0check r", length)?;

    let mut hat_fx_aux_info = fx_aux_info.clone();
    hat_fx_aux_info.max_degree += 1;
    let sum_subclaim =
        <PolyIOP<F> as SumCheck<F>>::verify(F::zero(), proof, &hat_fx_aux_info, transcript)?;

    let eq_x_r_eval = eq_eval(&sum_subclaim.point, &r)?;
    let expected_evaluation = sum_subclaim.expected_evaluation / eq_x_r_eval;

    Ok(ZeroCheckSubClaim {
        point: sum_subclaim.point,
        expected_evaluation,
        init_challenge: r,
    })
}

// ---------------------------------------------------------------------------
// prod_check/{mod,util}.rs
// ---------------------------------------------------------------------------

/// `ProductCheckProof`.
#[derive(Clone, Debug, PartialEq)]
pub struct ProductCheckProof<E: Pairing> {
    /// Zerocheck on `Q(x)`.
    pub zero_check_proof: IOPProof<E::ScalarField>,
    /// Commitment to `prod(x)`.
    pub prod_x_comm: Commitment<E>,
    /// Commitment to `frac(x)`.
    pub frac_comm: Commitment<E>,
}

/// `ProductCheckSubClaim`.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ProductCheckSubClaim<F: PrimeField> {
    /// The zerocheck's subclaim.
    pub zero_check_sub_claim: ZeroCheckSubClaim<F>,
    /// `prod(1, ..., 1, 0) = 1`.
    pub final_query: (Vec<F>, F),
    /// The product check's `alpha`.
    pub alpha: F,
}

fn compute_frac_poly<F: PrimeField>(
    fxs: &[Poly<F>],
    gxs: &[Poly<F>],
) -> Result<Poly<F>, PolyIOPErrors> {
    let mut f_evals = vec![F::one(); 1 << fxs[0].num_vars];
    for fx in fxs {
        for (f_eval, fi) in f_evals.iter_mut().zip(fx.iter()) {
            *f_eval *= fi;
        }
    }
    let mut g_evals = vec![F::one(); 1 << gxs[0].num_vars];
    for gx in gxs {
        for (g_eval, gi) in g_evals.iter_mut().zip(gx.iter()) {
            *g_eval *= gi;
        }
    }
    batch_inversion(&mut g_evals[..]);

    for (f_eval, g_eval) in f_evals.iter_mut().zip(g_evals.iter()) {
        if *g_eval == F::zero() {
            return Err(PolyIOPErrors::InvalidParameters(
                "gxs has zero entries in the boolean hypercube".to_string(),
            ));
        }
        *f_eval *= g_eval;
    }

    Ok(Arc::new(DenseMultilinearExtension::from_evaluations_vec(
        fxs[0].num_vars,
        f_evals,
    )))
}

fn compute_product_poly<F: PrimeField>(frac_poly: &Poly<F>) -> Result<Poly<F>, PolyIOPErrors> {
    let num_vars = frac_poly.num_vars;
    let frac_evals = &frac_poly.evaluations;

    let mut prod_x_evals = vec![];
    for x in 0..(1 << num_vars) - 1 {
        let (x_zero_index, x_one_index, sign) = get_index(x, num_vars);
        if !sign {
            prod_x_evals.push(frac_evals[x_zero_index] * frac_evals[x_one_index]);
        } else {
            if x_zero_index >= prod_x_evals.len() || x_one_index >= prod_x_evals.len() {
                return Err(PolyIOPErrors::ShouldNotArrive);
            }
            prod_x_evals.push(prod_x_evals[x_zero_index] * prod_x_evals[x_one_index]);
        }
    }

    prod_x_evals.push(F::zero());

    Ok(Arc::new(DenseMultilinearExtension::from_evaluations_vec(
        num_vars,
        prod_x_evals,
    )))
}

fn prove_zero_check<F: PrimeField>(
    fxs: &[Poly<F>],
    gxs: &[Poly<F>],
    frac_poly: &Poly<F>,
    prod_x: &Poly<F>,
    alpha: &F,
    transcript: &mut IOPTranscript<F>,
) -> Result<IOPProof<F>, PolyIOPErrors> {
    let num_vars = frac_poly.num_vars;

    let mut p1_evals = vec![F::zero(); 1 << num_vars];
    let mut p2_evals = vec![F::zero(); 1 << num_vars];
    for x in 0..1 << num_vars {
        let (x0, x1, sign) = get_index(x, num_vars);
        if !sign {
            p1_evals[x] = frac_poly.evaluations[x0];
            p2_evals[x] = frac_poly.evaluations[x1];
        } else {
            p1_evals[x] = prod_x.evaluations[x0];
            p2_evals[x] = prod_x.evaluations[x1];
        }
    }
    let p1 = Arc::new(DenseMultilinearExtension::from_evaluations_vec(
        num_vars, p1_evals,
    ));
    let p2 = Arc::new(DenseMultilinearExtension::from_evaluations_vec(
        num_vars, p2_evals,
    ));

    // compute Q(x)
    // prod(x)
    let mut q_x = VirtualPolynomial::new_from_mle(prod_x, F::one());

    //   prod(x)
    // - p1(x) * p2(x)
    q_x.add_mle_list([p1, p2], -F::one())?;

    //   prod(x)
    // - p1(x) * p2(x)
    // + alpha * frac(x) * g1(x) * ... * gk(x)
    let mut mle_list = gxs.to_vec();
    mle_list.push(frac_poly.clone());
    q_x.add_mle_list(mle_list, *alpha)?;

    //   prod(x)
    // - p1(x) * p2(x)
    // + alpha * frac(x) * g1(x) * ... * gk(x)
    // - alpha * f1(x) * ... * fk(x)]
    q_x.add_mle_list(fxs.to_vec(), -*alpha)?;

    zero_check_prove(&q_x, transcript)
}

/// `ProductCheck::prove`. Returns the proof, `prod(x)` and `frac(x)`.
///
/// # Errors
/// Fails on mismatched inputs or a zero denominator.
#[allow(clippy::type_complexity)]
pub fn prod_check_prove<E: Pairing>(
    pcs_param: &MultilinearProverParam<E>,
    fxs: &[Poly<E::ScalarField>],
    gxs: &[Poly<E::ScalarField>],
    transcript: &mut IOPTranscript<E::ScalarField>,
) -> Result<
    (
        ProductCheckProof<E>,
        Poly<E::ScalarField>,
        Poly<E::ScalarField>,
    ),
    PolyIOPErrors,
> {
    if fxs.is_empty() {
        return Err(PolyIOPErrors::InvalidParameters("fxs is empty".to_string()));
    }
    if fxs.len() != gxs.len() {
        return Err(PolyIOPErrors::InvalidParameters(
            "fxs and gxs have different number of polynomials".to_string(),
        ));
    }
    for poly in fxs.iter().chain(gxs.iter()) {
        if poly.num_vars != fxs[0].num_vars {
            return Err(PolyIOPErrors::InvalidParameters(
                "fx and gx have different number of variables".to_string(),
            ));
        }
    }

    // compute the fractional polynomial frac_p s.t.
    // frac_p(x) = f1(x) * ... * fk(x) / (g1(x) * ... * gk(x))
    let frac_poly = compute_frac_poly(fxs, gxs)?;
    // compute the product polynomial
    let prod_x = compute_product_poly(&frac_poly)?;

    // generate challenge
    let frac_comm = pcs::commit(pcs_param, &frac_poly)?;
    let prod_x_comm = pcs::commit(pcs_param, &prod_x)?;
    transcript.append_serializable_element(b"frac(x)", &frac_comm)?;
    transcript.append_serializable_element(b"prod(x)", &prod_x_comm)?;
    let alpha = transcript.get_and_append_challenge(b"alpha")?;

    // build the zero-check proof
    let zero_check_proof = prove_zero_check(fxs, gxs, &frac_poly, &prod_x, &alpha, transcript)?;

    Ok((
        ProductCheckProof {
            zero_check_proof,
            prod_x_comm,
            frac_comm,
        },
        prod_x,
        frac_poly,
    ))
}

/// `ProductCheck::verify`.
///
/// # Errors
/// Fails if the zerocheck fails.
pub fn prod_check_verify<E: Pairing>(
    proof: &ProductCheckProof<E>,
    aux_info: &VPAuxInfo<E::ScalarField>,
    transcript: &mut IOPTranscript<E::ScalarField>,
) -> Result<ProductCheckSubClaim<E::ScalarField>, PolyIOPErrors> {
    // update transcript and generate challenge
    transcript.append_serializable_element(b"frac(x)", &proof.frac_comm)?;
    transcript.append_serializable_element(b"prod(x)", &proof.prod_x_comm)?;
    let alpha = transcript.get_and_append_challenge(b"alpha")?;

    // invoke the zero check on the iop_proof
    // the virtual poly info for Q(x)
    let zero_check_sub_claim = zero_check_verify(&proof.zero_check_proof, aux_info, transcript)?;

    // the final query is on prod_x
    let mut final_query = vec![E::ScalarField::one(); aux_info.num_variables];
    // the point has to be reversed because Arkworks uses big-endian.
    final_query[0] = E::ScalarField::zero();
    let final_eval = E::ScalarField::one();

    Ok(ProductCheckSubClaim {
        zero_check_sub_claim,
        final_query: (final_query, final_eval),
        alpha,
    })
}

// ---------------------------------------------------------------------------
// perm_check/{mod,util}.rs
// ---------------------------------------------------------------------------

/// `PermutationCheckSubClaim`.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct PermutationCheckSubClaim<F: PrimeField> {
    /// The product check's subclaim.
    pub product_check_sub_claim: ProductCheckSubClaim<F>,
    /// `(beta, gamma)`.
    pub challenges: (F, F),
}

#[allow(clippy::type_complexity)]
fn computer_nums_and_denoms<F: PrimeField>(
    beta: &F,
    gamma: &F,
    fxs: &[Poly<F>],
    gxs: &[Poly<F>],
    perms: &[Poly<F>],
) -> (Vec<Poly<F>>, Vec<Poly<F>>) {
    let num_vars = fxs[0].num_vars;
    let mut numerators = vec![];
    let mut denominators = vec![];
    let s_ids = identity_permutation_mles::<F>(num_vars, fxs.len());
    for l in 0..fxs.len() {
        let mut numerator_evals = vec![];
        let mut denominator_evals = vec![];

        for (&f_ev, (&g_ev, (&s_id_ev, &perm_ev))) in fxs[l]
            .iter()
            .zip(gxs[l].iter().zip(s_ids[l].iter().zip(perms[l].iter())))
        {
            let numerator = f_ev + *beta * s_id_ev + gamma;
            let denominator = g_ev + *beta * perm_ev + gamma;

            numerator_evals.push(numerator);
            denominator_evals.push(denominator);
        }
        numerators.push(Arc::new(DenseMultilinearExtension::from_evaluations_vec(
            num_vars,
            numerator_evals,
        )));
        denominators.push(Arc::new(DenseMultilinearExtension::from_evaluations_vec(
            num_vars,
            denominator_evals,
        )));
    }

    (numerators, denominators)
}

/// `PermutationCheck::prove`. Returns the proof, `prod(x)` and `frac(x)`.
///
/// # Errors
/// Fails on mismatched inputs.
#[allow(clippy::type_complexity)]
pub fn perm_check_prove<E: Pairing>(
    pcs_param: &MultilinearProverParam<E>,
    fxs: &[Poly<E::ScalarField>],
    gxs: &[Poly<E::ScalarField>],
    perms: &[Poly<E::ScalarField>],
    transcript: &mut IOPTranscript<E::ScalarField>,
) -> Result<
    (
        ProductCheckProof<E>,
        Poly<E::ScalarField>,
        Poly<E::ScalarField>,
    ),
    PolyIOPErrors,
> {
    if fxs.is_empty() {
        return Err(PolyIOPErrors::InvalidParameters("fxs is empty".to_string()));
    }
    if (fxs.len() != gxs.len()) || (fxs.len() != perms.len()) {
        return Err(PolyIOPErrors::InvalidProof(
            "fxs, gxs and perms have different lengths".to_string(),
        ));
    }

    let num_vars = fxs[0].num_vars;
    for ((fx, gx), perm) in fxs.iter().zip(gxs.iter()).zip(perms.iter()) {
        if (fx.num_vars != num_vars) || (gx.num_vars != num_vars) || (perm.num_vars != num_vars) {
            return Err(PolyIOPErrors::InvalidParameters(
                "number of variables unmatched".to_string(),
            ));
        }
    }

    // generate challenge `beta` and `gamma` from current transcript
    let beta = transcript.get_and_append_challenge(b"beta")?;
    let gamma = transcript.get_and_append_challenge(b"gamma")?;
    let (numerators, denominators) = computer_nums_and_denoms(&beta, &gamma, fxs, gxs, perms);

    // invoke product check on numerator and denominator
    prod_check_prove(pcs_param, &numerators, &denominators, transcript)
}

/// `PermutationCheck::verify`.
///
/// # Errors
/// Fails if the product check fails.
pub fn perm_check_verify<E: Pairing>(
    proof: &ProductCheckProof<E>,
    aux_info: &VPAuxInfo<E::ScalarField>,
    transcript: &mut IOPTranscript<E::ScalarField>,
) -> Result<PermutationCheckSubClaim<E::ScalarField>, PolyIOPErrors> {
    let beta = transcript.get_and_append_challenge(b"beta")?;
    let gamma = transcript.get_and_append_challenge(b"gamma")?;

    // invoke the zero check on the iop_proof
    let product_check_sub_claim = prod_check_verify(proof, aux_info, transcript)?;

    Ok(PermutationCheckSubClaim {
        product_check_sub_claim,
        challenges: (beta, gamma),
    })
}
