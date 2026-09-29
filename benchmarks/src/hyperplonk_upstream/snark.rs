//! `hyperplonk::{snark, structs, utils, custom_gate, mock}`: the HyperPlonk
//! SNARK over multilinear KZG.
//!
//! `HyperPlonkSNARK` on `PolyIOP` becomes free functions `preprocess`,
//! `prove` and `verify` with upstream's bodies. `SelectorColumn` and
//! `WitnessColumn` are plain `Vec<F>`s, and `MockCircuit::new` takes the rng
//! instead of calling `test_rng()`.

use super::PolyIOPErrors;
use super::pcs::{
    self, BatchProof, Commitment, MultilinearProverParam, MultilinearUniversalParams,
    MultilinearVerifierParam,
};
use super::piop::{
    ProductCheckProof, perm_check_prove, perm_check_verify, zero_check_prove, zero_check_verify,
};
use crate::sumcheck_upstream::arithmetic::{
    VPAuxInfo, VirtualPolynomial, evaluate_opt, gen_eval_point, identity_permutation,
};
use crate::sumcheck_upstream::poly_iop::structs::IOPProof;
use crate::sumcheck_upstream::transcript::IOPTranscript;
use ark_ec::pairing::Pairing;
use ark_ff::{One, PrimeField, Zero};
use ark_poly::DenseMultilinearExtension;
use ark_std::{log2, rand::Rng};
use rayon::prelude::*;
use std::{marker::PhantomData, sync::Arc};

type Poly<F> = Arc<DenseMultilinearExtension<F>>;

// ---------------------------------------------------------------------------
// custom_gate.rs
// ---------------------------------------------------------------------------

/// A gate as a sum of `(coeff, selector, witnesses)` monomials.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CustomizedGates {
    /// The monomials.
    pub gates: Vec<(i64, Option<usize>, Vec<usize>)>,
}

impl CustomizedGates {
    /// `q_L w_1 + q_R w_2 + q_O w_3 + q_M w_1 w_2 + q_C = 0`.
    #[must_use]
    pub fn vanilla_plonk_gate() -> Self {
        Self {
            gates: vec![
                (1, Some(0), vec![0]),
                (1, Some(1), vec![1]),
                (1, Some(2), vec![2]),
                (1, Some(3), vec![0, 1]),
                (1, Some(4), vec![]),
            ],
        }
    }

    /// Largest monomial degree, counting the selector.
    #[must_use]
    pub fn degree(&self) -> usize {
        let mut res = 0;
        for x in &self.gates {
            res = res.max(x.2.len() + usize::from(x.1.is_some()));
        }
        res
    }

    /// Number of selector columns.
    #[must_use]
    pub fn num_selector_columns(&self) -> usize {
        self.gates.iter().filter(|(_, q, _)| q.is_some()).count()
    }

    /// Number of witness columns.
    #[must_use]
    pub fn num_witness_columns(&self) -> usize {
        let mut res = 0;
        for (_coeff, _q, ws) in &self.gates {
            if let Some(&p) = ws.last()
                && res < p
            {
                res = p;
            }
        }
        res + 1
    }
}

fn coeff_to_field<F: PrimeField>(coeff: i64) -> F {
    if coeff < 0 {
        -F::from(coeff.unsigned_abs())
    } else {
        F::from(coeff.unsigned_abs())
    }
}

// ---------------------------------------------------------------------------
// structs.rs
// ---------------------------------------------------------------------------

/// `HyperPlonkParams`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HyperPlonkParams {
    /// Number of gates (a power of two).
    pub num_constraints: usize,
    /// Number of public inputs (a power of two).
    pub num_pub_input: usize,
    /// The gate.
    pub gate_func: CustomizedGates,
}

impl HyperPlonkParams {
    /// `log2(num_constraints)`.
    #[must_use]
    pub fn num_variables(&self) -> usize {
        log2(self.num_constraints) as usize
    }

    /// Number of selector columns.
    #[must_use]
    pub fn num_selector_columns(&self) -> usize {
        self.gate_func.num_selector_columns()
    }

    /// Number of witness columns.
    #[must_use]
    pub fn num_witness_columns(&self) -> usize {
        self.gate_func.num_witness_columns()
    }

    /// Evaluate the identity-permutation oracle `sum_i 2^i point_i`.
    ///
    /// # Errors
    /// Fails if the point has the wrong length.
    pub fn eval_id_oracle<F: PrimeField>(&self, point: &[F]) -> Result<F, PolyIOPErrors> {
        let len = self.num_variables() + (log2(self.num_witness_columns()) as usize);
        if point.len() != len {
            return Err(PolyIOPErrors::InvalidParameters(
                "ID oracle point length".to_string(),
            ));
        }

        let mut res = F::zero();
        let mut base = F::one();
        for &v in point {
            res += base * v;
            base += base;
        }
        Ok(res)
    }
}

/// `HyperPlonkIndex`: the circuit.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HyperPlonkIndex<F: PrimeField> {
    /// Sizes and gate.
    pub params: HyperPlonkParams,
    /// Wiring permutation over all witness cells.
    pub permutation: Vec<F>,
    /// Selector columns.
    pub selectors: Vec<Vec<F>>,
}

/// `HyperPlonkProvingKey`.
#[derive(Clone, Debug)]
pub struct HyperPlonkProvingKey<E: Pairing> {
    /// Sizes and gate.
    pub params: HyperPlonkParams,
    /// Permutation oracles, one per witness column.
    pub permutation_oracles: Vec<Poly<E::ScalarField>>,
    /// Selector oracles.
    pub selector_oracles: Vec<Poly<E::ScalarField>>,
    /// Selector commitments.
    pub selector_commitments: Vec<Commitment<E>>,
    /// Permutation commitments.
    pub permutation_commitments: Vec<Commitment<E>>,
    /// PCS prover key.
    pub pcs_param: MultilinearProverParam<E>,
}

/// `HyperPlonkVerifyingKey`.
#[derive(Clone, Debug)]
pub struct HyperPlonkVerifyingKey<E: Pairing> {
    /// Sizes and gate.
    pub params: HyperPlonkParams,
    /// PCS verifier key.
    pub pcs_param: MultilinearVerifierParam<E>,
    /// Selector commitments.
    pub selector_commitments: Vec<Commitment<E>>,
    /// Permutation commitments.
    pub perm_commitments: Vec<Commitment<E>>,
}

/// `HyperPlonkProof`.
#[derive(Clone, Debug, PartialEq)]
pub struct HyperPlonkProof<E: Pairing> {
    /// Witness commitments.
    pub witness_commits: Vec<Commitment<E>>,
    /// The deferred batch opening.
    pub batch_openings: BatchProof<E>,
    /// Gate-identity zerocheck.
    pub zero_check_proof: IOPProof<E::ScalarField>,
    /// Copy-constraint permutation check.
    pub perm_check_proof: ProductCheckProof<E>,
}

// ---------------------------------------------------------------------------
// mock.rs
// ---------------------------------------------------------------------------

/// `MockCircuit`: random satisfying assignment, identity wiring.
pub struct MockCircuit<F: PrimeField> {
    /// Public inputs (a prefix of the first witness column).
    pub public_inputs: Vec<F>,
    /// Witness columns.
    pub witnesses: Vec<Vec<F>>,
    /// The circuit.
    pub index: HyperPlonkIndex<F>,
}

impl<F: PrimeField> MockCircuit<F> {
    /// `MockCircuit::new`, with the rng passed in.
    #[must_use]
    pub fn new<R: Rng>(num_constraints: usize, gate: &CustomizedGates, rng: &mut R) -> Self {
        let nv = log2(num_constraints);
        let num_selectors = gate.num_selector_columns();
        let num_witnesses = gate.num_witness_columns();
        let log_n_wires = log2(num_witnesses);
        let merged_nv = nv + log_n_wires;

        let mut selectors: Vec<Vec<F>> = vec![Vec::new(); num_selectors];
        let mut witnesses: Vec<Vec<F>> = vec![Vec::new(); num_witnesses];

        for _cs_counter in 0..num_constraints {
            let mut cur_selectors: Vec<F> =
                (0..(num_selectors - 1)).map(|_| F::rand(rng)).collect();
            let cur_witness: Vec<F> = (0..num_witnesses).map(|_| F::rand(rng)).collect();
            let mut last_selector = F::zero();
            for (index, (coeff, q, wit)) in gate.gates.iter().enumerate() {
                if index == num_selectors - 1 {
                    let mut cur_monomial = coeff_to_field::<F>(*coeff);
                    for wit_index in wit {
                        cur_monomial *= cur_witness[*wit_index];
                    }
                    last_selector /= -cur_monomial;
                } else {
                    let mut cur_monomial = coeff_to_field::<F>(*coeff);
                    cur_monomial = match q {
                        Some(p) => cur_monomial * cur_selectors[*p],
                        None => cur_monomial,
                    };
                    for wit_index in wit {
                        cur_monomial *= cur_witness[*wit_index];
                    }
                    last_selector += cur_monomial;
                }
            }
            cur_selectors.push(last_selector);
            for i in 0..num_selectors {
                selectors[i].push(cur_selectors[i]);
            }
            for i in 0..num_witnesses {
                witnesses[i].push(cur_witness[i]);
            }
        }
        let pub_input_len = 4.min(num_constraints);
        let public_inputs = witnesses[0][0..pub_input_len].to_vec();

        let params = HyperPlonkParams {
            num_constraints,
            num_pub_input: public_inputs.len(),
            gate_func: gate.clone(),
        };

        let permutation = identity_permutation(merged_nv as usize, 1);
        let index = HyperPlonkIndex {
            params,
            permutation,
            selectors,
        };

        Self {
            public_inputs,
            witnesses,
            index,
        }
    }
}

// ---------------------------------------------------------------------------
// utils.rs
// ---------------------------------------------------------------------------

struct PcsAccumulator<F: PrimeField, E: Pairing<ScalarField = F>> {
    num_var: usize,
    polynomials: Vec<Poly<F>>,
    commitments: Vec<Commitment<E>>,
    points: Vec<Vec<F>>,
    evals: Vec<F>,
}

impl<F: PrimeField, E: Pairing<ScalarField = F>> PcsAccumulator<F, E> {
    const fn new(num_var: usize) -> Self {
        Self {
            num_var,
            polynomials: vec![],
            commitments: vec![],
            points: vec![],
            evals: vec![],
        }
    }

    fn insert_poly_and_points(&mut self, poly: &Poly<F>, commit: &Commitment<E>, point: &[F]) {
        assert!(poly.num_vars == point.len());
        assert!(poly.num_vars == self.num_var);

        let eval = evaluate_opt(poly, point);

        self.evals.push(eval);
        self.polynomials.push(poly.clone());
        self.points.push(point.to_vec());
        self.commitments.push(*commit);
    }

    fn multi_open(
        &self,
        prover_param: &MultilinearProverParam<E>,
        transcript: &mut IOPTranscript<F>,
    ) -> Result<BatchProof<E>, PolyIOPErrors> {
        pcs::multi_open(
            prover_param,
            &self.polynomials,
            &self.points,
            &self.evals,
            transcript,
        )
    }
}

fn prover_sanity_check<F: PrimeField>(
    params: &HyperPlonkParams,
    pub_input: &[F],
    witnesses: &[Vec<F>],
) -> Result<(), PolyIOPErrors> {
    let bad = |m: &str| Err(PolyIOPErrors::InvalidProver(m.to_string()));
    if pub_input.len() > params.num_constraints {
        return bad("Public input length is greater than num constraints");
    }
    if pub_input.len() != params.num_pub_input {
        return bad("Public input length is not correct");
    }
    if !pub_input.len().is_power_of_two() {
        return bad("Public input length is not power of two");
    }
    for w in witnesses {
        if w.len() != params.num_constraints {
            return bad("witness length is not correct");
        }
    }
    for (&pi, &w) in pub_input
        .iter()
        .zip(witnesses[0].iter().take(pub_input.len()))
    {
        if pi != w {
            return bad("public input does not match witness[0]");
        }
    }
    Ok(())
}

fn build_f<F: PrimeField>(
    gates: &CustomizedGates,
    num_vars: usize,
    selector_mles: &[Poly<F>],
    witness_mles: &[Poly<F>],
) -> Result<VirtualPolynomial<F>, PolyIOPErrors> {
    for mle in selector_mles.iter().chain(witness_mles) {
        if mle.num_vars != num_vars {
            return Err(PolyIOPErrors::InvalidParameters(
                "column has a different number of vars".to_string(),
            ));
        }
    }

    let mut res = VirtualPolynomial::<F>::new(num_vars);

    for (coeff, selector, witnesses) in &gates.gates {
        let coeff_fr = coeff_to_field::<F>(*coeff);
        let mut mle_list = vec![];
        if let Some(s) = *selector {
            mle_list.push(selector_mles[s].clone());
        }
        for &witness in witnesses {
            mle_list.push(witness_mles[witness].clone());
        }
        res.add_mle_list(mle_list, coeff_fr)?;
    }

    Ok(res)
}

fn eval_f<F: PrimeField>(gates: &CustomizedGates, selector_evals: &[F], witness_evals: &[F]) -> F {
    let mut res = F::zero();
    for (coeff, selector, witnesses) in &gates.gates {
        let mut cur_value = coeff_to_field::<F>(*coeff);
        cur_value *= match selector {
            Some(s) => selector_evals[*s],
            None => F::one(),
        };
        for &witness in witnesses {
            cur_value *= witness_evals[witness];
        }
        res += cur_value;
    }
    res
}

#[allow(clippy::too_many_arguments)]
fn eval_perm_gate<F: PrimeField>(
    prod_evals: &[F],
    frac_evals: &[F],
    witness_perm_evals: &[F],
    id_evals: &[F],
    perm_evals: &[F],
    alpha: F,
    beta: F,
    gamma: F,
    x1: F,
) -> F {
    let p1_eval = frac_evals[1] + x1 * (prod_evals[1] - frac_evals[1]);
    let p2_eval = frac_evals[2] + x1 * (prod_evals[2] - frac_evals[2]);
    let mut f_prod_eval = F::one();
    for (&w_eval, &id_eval) in witness_perm_evals.iter().zip(id_evals.iter()) {
        f_prod_eval *= w_eval + beta * id_eval + gamma;
    }
    let mut g_prod_eval = F::one();
    for (&w_eval, &p_eval) in witness_perm_evals.iter().zip(perm_evals.iter()) {
        g_prod_eval *= w_eval + beta * p_eval + gamma;
    }
    prod_evals[0] - p1_eval * p2_eval + alpha * (frac_evals[0] * g_prod_eval - f_prod_eval)
}

// ---------------------------------------------------------------------------
// snark.rs
// ---------------------------------------------------------------------------

/// `HyperPlonkSNARK::preprocess`: trim the SRS and commit to the selector and
/// permutation oracles.
///
/// # Errors
/// Fails if a commitment fails.
pub fn preprocess<E: Pairing>(
    index: &HyperPlonkIndex<E::ScalarField>,
    pcs_srs: &MultilinearUniversalParams<E>,
) -> Result<(HyperPlonkProvingKey<E>, HyperPlonkVerifyingKey<E>), PolyIOPErrors> {
    let num_vars = index.params.num_variables();
    let supported_ml_degree = num_vars;

    // extract PCS prover and verifier keys from SRS
    let (pcs_prover_param, pcs_verifier_param) = pcs_srs.trim(supported_ml_degree);

    // build permutation oracles
    let mut permutation_oracles = vec![];
    let mut perm_comms = vec![];
    let chunk_size = 1 << num_vars;
    for i in 0..index.params.num_witness_columns() {
        let perm_oracle = Arc::new(DenseMultilinearExtension::from_evaluations_slice(
            num_vars,
            &index.permutation[i * chunk_size..(i + 1) * chunk_size],
        ));
        let perm_comm = pcs::commit(&pcs_prover_param, &perm_oracle)?;
        permutation_oracles.push(perm_oracle);
        perm_comms.push(perm_comm);
    }

    // build selector oracles and commit to it
    let selector_oracles: Vec<Poly<E::ScalarField>> = index
        .selectors
        .iter()
        .map(|s| {
            Arc::new(DenseMultilinearExtension::from_evaluations_slice(
                num_vars, s,
            ))
        })
        .collect();

    let selector_commitments = selector_oracles
        .par_iter()
        .map(|poly| pcs::commit(&pcs_prover_param, poly))
        .collect::<Result<Vec<_>, _>>()?;

    Ok((
        HyperPlonkProvingKey {
            params: index.params.clone(),
            permutation_oracles,
            selector_oracles,
            selector_commitments: selector_commitments.clone(),
            permutation_commitments: perm_comms.clone(),
            pcs_param: pcs_prover_param,
        },
        HyperPlonkVerifyingKey {
            params: index.params.clone(),
            pcs_param: pcs_verifier_param,
            selector_commitments,
            perm_commitments: perm_comms,
        },
    ))
}

/// `HyperPlonkSNARK::prove`. The transcript is passed in (upstream creates
/// `IOPTranscript::new(b"hyperplonk")` inside) so tests can replay it.
///
/// # Errors
/// Fails on a malformed witness or a failing sub-protocol.
pub fn prove<E: Pairing>(
    pk: &HyperPlonkProvingKey<E>,
    pub_input: &[E::ScalarField],
    witnesses: &[Vec<E::ScalarField>],
    transcript: &mut IOPTranscript<E::ScalarField>,
) -> Result<HyperPlonkProof<E>, PolyIOPErrors> {
    prover_sanity_check(&pk.params, pub_input, witnesses)?;

    // witness assignment of length 2^n
    let num_vars = pk.params.num_variables();

    // online public input of length 2^\ell
    let ell = log2(pk.params.num_pub_input) as usize;

    // We use accumulators to store the polynomials and their eval points.
    // They are batch opened at a later stage.
    let mut pcs_acc = PcsAccumulator::<E::ScalarField, E>::new(num_vars);

    // =======================================================================
    // 1. Commit Witness polynomials `w_i(x)` and append commitment to
    // transcript
    // =======================================================================
    let witness_polys: Vec<Poly<E::ScalarField>> = witnesses
        .iter()
        .map(|w| {
            Arc::new(DenseMultilinearExtension::from_evaluations_slice(
                num_vars, w,
            ))
        })
        .collect();

    let witness_commits = witness_polys
        .par_iter()
        .map(|x| pcs::commit(&pk.pcs_param, x).unwrap())
        .collect::<Vec<_>>();
    for w_com in &witness_commits {
        transcript.append_serializable_element(b"w", w_com)?;
    }

    // =======================================================================
    // 2 Run ZeroCheck on
    //
    //     `f(q_0(x),...q_l(x), w_0(x),...w_d(x))`
    //
    // where `f` is the constraint polynomial i.e.,
    //
    //     f(q_l, q_r, q_m, q_o, w_a, w_b, w_c)
    //     = q_l w_a(x) + q_r w_b(x) + q_m w_a(x)w_b(x) - q_o w_c(x)
    //
    // in vanilla plonk, and obtain a ZeroCheckSubClaim
    // =======================================================================
    let fx = build_f(
        &pk.params.gate_func,
        pk.params.num_variables(),
        &pk.selector_oracles,
        &witness_polys,
    )?;

    let zero_check_proof = zero_check_prove(&fx, transcript)?;

    // =======================================================================
    // 3. Run permutation check on `\{w_i(x)\}` and `permutation_oracle`, and
    // obtain a PermCheckSubClaim.
    // =======================================================================
    let (perm_check_proof, prod_x, frac_poly) = perm_check_prove(
        &pk.pcs_param,
        &witness_polys,
        &witness_polys,
        &pk.permutation_oracles,
        transcript,
    )?;
    let perm_check_point = &perm_check_proof.zero_check_proof.point;

    // =======================================================================
    // 4. Generate evaluations and corresponding proofs
    // =======================================================================

    // (perm_check_point[2..n], 0)
    let perm_check_point_0 = [
        &[E::ScalarField::zero()],
        &perm_check_point[0..num_vars - 1],
    ]
    .concat();
    // (perm_check_point[2..n], 1)
    let perm_check_point_1 =
        [&[E::ScalarField::one()], &perm_check_point[0..num_vars - 1]].concat();
    // (1, ..., 1, 0)
    let prod_final_query_point = [
        vec![E::ScalarField::zero()],
        vec![E::ScalarField::one(); num_vars - 1],
    ]
    .concat();

    // prod(x)'s points
    pcs_acc.insert_poly_and_points(&prod_x, &perm_check_proof.prod_x_comm, perm_check_point);
    pcs_acc.insert_poly_and_points(&prod_x, &perm_check_proof.prod_x_comm, &perm_check_point_0);
    pcs_acc.insert_poly_and_points(&prod_x, &perm_check_proof.prod_x_comm, &perm_check_point_1);
    pcs_acc.insert_poly_and_points(
        &prod_x,
        &perm_check_proof.prod_x_comm,
        &prod_final_query_point,
    );

    // frac(x)'s points
    pcs_acc.insert_poly_and_points(&frac_poly, &perm_check_proof.frac_comm, perm_check_point);
    pcs_acc.insert_poly_and_points(&frac_poly, &perm_check_proof.frac_comm, &perm_check_point_0);
    pcs_acc.insert_poly_and_points(&frac_poly, &perm_check_proof.frac_comm, &perm_check_point_1);

    // perms(x)'s points
    for (perm, pcom) in pk
        .permutation_oracles
        .iter()
        .zip(pk.permutation_commitments.iter())
    {
        pcs_acc.insert_poly_and_points(perm, pcom, perm_check_point);
    }

    // witnesses' points
    for (wpoly, wcom) in witness_polys.iter().zip(witness_commits.iter()) {
        pcs_acc.insert_poly_and_points(wpoly, wcom, perm_check_point);
    }
    for (wpoly, wcom) in witness_polys.iter().zip(witness_commits.iter()) {
        pcs_acc.insert_poly_and_points(wpoly, wcom, &zero_check_proof.point);
    }

    //   - 4.3.2. (deferred) selector_poly(zero_check_point)
    pk.selector_oracles
        .iter()
        .zip(pk.selector_commitments.iter())
        .for_each(|(poly, com)| pcs_acc.insert_poly_and_points(poly, com, &zero_check_proof.point));

    // - 4.4. public input consistency checks
    //   - pi_poly(r_pi) where r_pi is sampled from transcript
    let r_pi = transcript.get_and_append_challenge_vectors(b"r_pi", ell)?;
    // padded with zeros
    let r_pi_padded = [r_pi, vec![E::ScalarField::zero(); num_vars - ell]].concat();
    // Evaluate witness_poly[0] at r_pi||0s which is equal to public_input evaluated
    // at r_pi. Assumes that public_input is a power of 2
    pcs_acc.insert_poly_and_points(&witness_polys[0], &witness_commits[0], &r_pi_padded);

    // =======================================================================
    // 5. deferred batch opening
    // =======================================================================
    let batch_openings = pcs_acc.multi_open(&pk.pcs_param, transcript)?;

    Ok(HyperPlonkProof {
        witness_commits,
        batch_openings,
        zero_check_proof,
        perm_check_proof,
    })
}

/// `HyperPlonkSNARK::verify`, with the transcript passed in as in [`prove`].
///
/// # Errors
/// Fails on a malformed proof; a well-formed but invalid proof returns
/// `Ok(false)` from the final pairing check or an `Err` from an earlier one,
/// as upstream does.
#[allow(clippy::too_many_lines)]
pub fn verify<E: Pairing>(
    vk: &HyperPlonkVerifyingKey<E>,
    pub_input: &[E::ScalarField],
    proof: &HyperPlonkProof<E>,
    transcript: &mut IOPTranscript<E::ScalarField>,
) -> Result<bool, PolyIOPErrors> {
    let num_selectors = vk.params.num_selector_columns();
    let num_witnesses = vk.params.num_witness_columns();
    let num_vars = vk.params.num_variables();

    //  online public input of length 2^\ell
    let ell = log2(vk.params.num_pub_input) as usize;

    // =======================================================================
    // 0. sanity checks
    // =======================================================================
    // public input length
    if pub_input.len() != vk.params.num_pub_input {
        return Err(PolyIOPErrors::InvalidProver(
            "Public input length is not correct".to_string(),
        ));
    }

    // Extract evaluations from openings
    let prod_evals = &proof.batch_openings.f_i_eval_at_point_i[0..4];
    let frac_evals = &proof.batch_openings.f_i_eval_at_point_i[4..7];
    let perm_evals = &proof.batch_openings.f_i_eval_at_point_i[7..7 + num_witnesses];
    let witness_perm_evals =
        &proof.batch_openings.f_i_eval_at_point_i[7 + num_witnesses..7 + 2 * num_witnesses];
    let witness_gate_evals =
        &proof.batch_openings.f_i_eval_at_point_i[7 + 2 * num_witnesses..7 + 3 * num_witnesses];
    let selector_evals = &proof.batch_openings.f_i_eval_at_point_i
        [7 + 3 * num_witnesses..7 + 3 * num_witnesses + num_selectors];
    let pi_eval = proof.batch_openings.f_i_eval_at_point_i.last().unwrap();

    // =======================================================================
    // 1. Verify zero_check_proof on `f(q_0(x),...q_l(x), w_0(x),...w_d(x))`
    // =======================================================================
    // Zero check and perm check have different AuxInfo
    let zero_check_aux_info = VPAuxInfo::<E::ScalarField> {
        max_degree: vk.params.gate_func.degree(),
        num_variables: num_vars,
        phantom: PhantomData,
    };
    // push witness to transcript
    for w_com in &proof.witness_commits {
        transcript.append_serializable_element(b"w", w_com)?;
    }

    let zero_check_sub_claim =
        zero_check_verify(&proof.zero_check_proof, &zero_check_aux_info, transcript)?;

    let zero_check_point = zero_check_sub_claim.point;

    // check zero check subclaim
    let f_eval = eval_f(&vk.params.gate_func, selector_evals, witness_gate_evals);
    if f_eval != zero_check_sub_claim.expected_evaluation {
        return Err(PolyIOPErrors::InvalidProof(
            "zero check evaluation failed".to_string(),
        ));
    }

    // =======================================================================
    // 2. Verify perm_check_proof on `\{w_i(x)\}` and `permutation_oracle`
    // =======================================================================
    // Zero check and perm check have different AuxInfo
    let perm_check_aux_info = VPAuxInfo::<E::ScalarField> {
        // Prod(x) has a max degree of witnesses.len() + 1
        max_degree: proof.witness_commits.len() + 1,
        num_variables: num_vars,
        phantom: PhantomData,
    };
    let perm_check_sub_claim =
        perm_check_verify(&proof.perm_check_proof, &perm_check_aux_info, transcript)?;

    let perm_check_point = perm_check_sub_claim
        .product_check_sub_claim
        .zero_check_sub_claim
        .point;

    let alpha = perm_check_sub_claim.product_check_sub_claim.alpha;
    let (beta, gamma) = perm_check_sub_claim.challenges;

    let mut id_evals = vec![];
    for i in 0..num_witnesses {
        let ith_point = gen_eval_point(i, log2(num_witnesses) as usize, &perm_check_point[..]);
        id_evals.push(vk.params.eval_id_oracle(&ith_point[..])?);
    }

    // check evaluation subclaim
    let perm_gate_eval = eval_perm_gate(
        prod_evals,
        frac_evals,
        witness_perm_evals,
        &id_evals[..],
        perm_evals,
        alpha,
        beta,
        gamma,
        *perm_check_point.last().unwrap(),
    );
    if perm_gate_eval
        != perm_check_sub_claim
            .product_check_sub_claim
            .zero_check_sub_claim
            .expected_evaluation
    {
        return Err(PolyIOPErrors::InvalidVerifier(
            "evaluation failed".to_string(),
        ));
    }

    // =======================================================================
    // 3. Verify the opening against the commitment
    // =======================================================================
    // generate evaluation points and commitments
    let mut comms = vec![];
    let mut points = vec![];

    let perm_check_point_0 = [
        &[E::ScalarField::zero()],
        &perm_check_point[0..num_vars - 1],
    ]
    .concat();
    let perm_check_point_1 =
        [&[E::ScalarField::one()], &perm_check_point[0..num_vars - 1]].concat();
    let prod_final_query_point = [
        vec![E::ScalarField::zero()],
        vec![E::ScalarField::one(); num_vars - 1],
    ]
    .concat();

    // prod(x)'s points
    comms.push(proof.perm_check_proof.prod_x_comm);
    comms.push(proof.perm_check_proof.prod_x_comm);
    comms.push(proof.perm_check_proof.prod_x_comm);
    comms.push(proof.perm_check_proof.prod_x_comm);
    points.push(perm_check_point.clone());
    points.push(perm_check_point_0.clone());
    points.push(perm_check_point_1.clone());
    points.push(prod_final_query_point);
    // frac(x)'s points
    comms.push(proof.perm_check_proof.frac_comm);
    comms.push(proof.perm_check_proof.frac_comm);
    comms.push(proof.perm_check_proof.frac_comm);
    points.push(perm_check_point.clone());
    points.push(perm_check_point_0);
    points.push(perm_check_point_1);

    // perms' points
    for &pcom in &vk.perm_commitments {
        comms.push(pcom);
        points.push(perm_check_point.clone());
    }

    // witnesses' points
    for &wcom in &proof.witness_commits {
        comms.push(wcom);
        points.push(perm_check_point.clone());
    }
    for &wcom in &proof.witness_commits {
        comms.push(wcom);
        points.push(zero_check_point.clone());
    }

    // selector_poly(zero_check_point)
    for &com in &vk.selector_commitments {
        comms.push(com);
        points.push(zero_check_point.clone());
    }

    // - 4.4. public input consistency checks
    //   - pi_poly(r_pi) where r_pi is sampled from transcript
    let r_pi = transcript.get_and_append_challenge_vectors(b"r_pi", ell)?;

    // check public evaluation
    let pi_poly = DenseMultilinearExtension::from_evaluations_slice(ell, pub_input);
    let expect_pi_eval = evaluate_opt(&pi_poly, &r_pi[..]);
    if expect_pi_eval != *pi_eval {
        return Err(PolyIOPErrors::InvalidProver(
            "Public input eval mismatch".to_string(),
        ));
    }
    let r_pi_padded = [r_pi, vec![E::ScalarField::zero(); num_vars - ell]].concat();

    comms.push(proof.witness_commits[0]);
    points.push(r_pi_padded);
    assert_eq!(comms.len(), proof.batch_openings.f_i_eval_at_point_i.len());

    // check proof
    pcs::batch_verify(
        &vk.pcs_param,
        &comms,
        &points,
        &proof.batch_openings,
        transcript,
    )
}
