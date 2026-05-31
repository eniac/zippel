//! Native PARI baseline — a faithful port of alireza-shirzad/garuda-pari
//! (commit 7a5be67) adapted for arkworks 0.5. Implements Fig. 6 of
//! "GARUDA and PARI: Faster and Smaller SNARK via Equifficient
//! Polynomial Commitments" (Dellepere, Mishra, Shirzad, USENIX 2026).
//!
//! Differences from the upstream crate (small, isolated):
//!   - skips the `ark-relations::gr1cs` circuit-synthesis layer — the
//!     upstream code takes a `ConstraintSynthesizer<F>` and uses
//!     `Sr1csAdapter` to lower it; that depends on a HEAD pin of
//!     `arkworks-rs/snark` and pulls a separate arkworks-main subtree
//!     that doesn't unify with zippel's 0.5 pin. Here we take the SR1CS
//!     matrices `(A, B)` and assignment `z` directly as inputs, which
//!     is the same shape `compute_wa_wb_za_zb` consumes upstream.
//!   - replaces the `shared_utils::IOPTranscript` (whose
//!     `append_serializable_element` signature `&challenge` requires the
//!     arkworks-main `&T: CanonicalSerialize` blanket impl) with the
//!     same transcript in a `&T`-by-value form that compiles against
//!     arkworks 0.5.
//!   - inlines `shared_utils::batch_inversion_and_mul` (used by
//!     `eval_last_lagrange_coeffs`) verbatim.
//!
//! Everything else — generator, prover, verifier, SRS layout, pairing
//! equation, Lagrange-coefficients trick — is copy-paste from upstream.

use ark_ec::pairing::Pairing;
use ark_ec::scalar_mul::BatchMulPreprocessing;
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{FftField, Field, One, PrimeField, Zero};
use ark_poly::{
    DenseUVPolynomial, EvaluationDomain, Evaluations, Radix2EvaluationDomain,
    univariate::DensePolynomial,
};
use ark_serialize::CanonicalSerialize;
use ark_std::UniformRand;
use rand::RngCore;
use std::marker::PhantomData;
use std::ops::Neg;

/// Row-major sparse SR1CS matrix: each row a list of `(coeff, col)` pairs.
/// Mirrors the `ark_relations::gr1cs::Matrix<F>` shape that upstream's
/// `compute_wa_wb_za_zb` iterates over.
pub type SparseMatrix<F> = Vec<Vec<(F, usize)>>;

// =============================================================================
// Data structures (port of pari/src/data_structures.rs)
// =============================================================================

#[derive(Clone)]
pub struct ProvingKey<E: Pairing> {
    pub sigma: Vec<E::G1Affine>,
    pub sigma_a: Vec<E::G1Affine>,
    pub sigma_b: Vec<E::G1Affine>,
    pub sigma_q_comm: Vec<E::G1Affine>,
    pub sigma_q_opening: Vec<E::G1Affine>,
    pub verifying_key: VerifyingKey<E>,
}

#[derive(Clone, Debug)]
pub struct VerifyingKey<E: Pairing> {
    pub num_constraints: usize,
    pub instance_len: usize,
    pub g: E::G1Affine,
    pub alpha_g: E::G1Affine,
    pub beta_g: E::G1Affine,
    pub delta_two_h: E::G2Affine,
    pub tau_h: E::G2Affine,
    pub h: E::G2Affine,
    pub domain: Radix2EvaluationDomain<E::ScalarField>,
}

impl<E: Pairing> CanonicalSerialize for VerifyingKey<E> {
    fn serialize_with_mode<W: std::io::Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        self.num_constraints
            .serialize_with_mode(&mut writer, compress)?;
        self.instance_len
            .serialize_with_mode(&mut writer, compress)?;
        self.alpha_g.serialize_with_mode(&mut writer, compress)?;
        self.beta_g.serialize_with_mode(&mut writer, compress)?;
        self.delta_two_h
            .serialize_with_mode(&mut writer, compress)?;
        self.tau_h.serialize_with_mode(&mut writer, compress)?;
        self.g.serialize_with_mode(&mut writer, compress)?;
        self.h.serialize_with_mode(&mut writer, compress)?;
        Ok(())
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        self.num_constraints.serialized_size(compress)
            + self.instance_len.serialized_size(compress)
            + self.alpha_g.serialized_size(compress)
            + self.beta_g.serialized_size(compress)
            + self.delta_two_h.serialized_size(compress)
            + self.tau_h.serialized_size(compress)
            + self.g.serialized_size(compress)
            + self.h.serialized_size(compress)
    }
}

#[derive(Clone)]
pub struct Proof<E: Pairing> {
    pub t_g: E::G1Affine,
    pub u_g: E::G1Affine,
    pub v_a: E::ScalarField,
    pub v_b: E::ScalarField,
}

impl<E: Pairing> CanonicalSerialize for Proof<E> {
    fn serialize_with_mode<W: std::io::Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        self.t_g.serialize_with_mode(&mut writer, compress)?;
        self.u_g.serialize_with_mode(&mut writer, compress)?;
        self.v_a.serialize_with_mode(&mut writer, compress)?;
        self.v_b.serialize_with_mode(&mut writer, compress)?;
        Ok(())
    }
    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        self.t_g.serialized_size(compress)
            + self.u_g.serialized_size(compress)
            + self.v_a.serialized_size(compress)
            + self.v_b.serialized_size(compress)
    }
}

// =============================================================================
// IOPTranscript (port of shared-utils/src/transcript/mod.rs)
//
// The upstream `append_serializable_element` takes `group_elem: S` (owned)
// and the upstream `get_and_append_challenge` calls
//   `self.append_serializable_element(label, &challenge)`
// which only typechecks under the `&T: CanonicalSerialize` blanket impl
// shipped by arkworks-main. arkworks 0.5 doesn't have it, so we switch
// to `&S` by reference — semantically identical, but compiles against
// either version.
// =============================================================================

pub struct IOPTranscript<F: PrimeField> {
    transcript: merlin::Transcript,
    is_empty: bool,
    _phantom: PhantomData<F>,
}

impl<F: PrimeField> IOPTranscript<F> {
    pub fn new(label: &'static [u8]) -> Self {
        Self {
            transcript: merlin::Transcript::new(label),
            is_empty: true,
            _phantom: PhantomData,
        }
    }

    pub fn append_message(&mut self, label: &'static [u8], msg: &[u8]) {
        self.transcript.append_message(label, msg);
        self.is_empty = false;
    }

    pub fn append_serializable_element<S: CanonicalSerialize>(
        &mut self,
        label: &'static [u8],
        group_elem: &S,
    ) {
        let mut bytes = Vec::with_capacity(group_elem.compressed_size());
        group_elem.serialize_compressed(&mut bytes).unwrap();
        self.append_message(label, &bytes);
    }

    pub fn get_and_append_challenge(&mut self, label: &'static [u8]) -> F {
        assert!(!self.is_empty, "transcript is empty");
        let mut buf = [0u8; 24];
        self.transcript.challenge_bytes(label, &mut buf);
        let challenge = F::from_le_bytes_mod_order(&buf);
        self.append_serializable_element(label, &challenge);
        challenge
    }
}

// =============================================================================
// Challenge computation (port of pari/src/utils.rs::compute_chall)
// =============================================================================

const SNARK_NAME: &[u8] = b"Pari";

pub fn compute_chall<E: Pairing>(
    vk: &VerifyingKey<E>,
    public_input: &[E::ScalarField],
    t_g: &E::G1Affine,
) -> E::ScalarField {
    let mut transcript = IOPTranscript::<E::ScalarField>::new(SNARK_NAME);
    transcript.append_serializable_element(b"vk", vk);
    transcript.append_serializable_element(b"input", &public_input.to_vec());
    transcript.append_serializable_element(b"comm", t_g);
    transcript.get_and_append_challenge(b"r")
}

// =============================================================================
// Generator (port of pari/src/generator.rs::keygen)
//
// Upstream takes `circuit: ConstraintSynthesizer` and lowers it through
// Sr1csAdapter to get `(matrices, num_variables, num_instance_variables)`.
// We take those three directly to avoid the gr1cs dep.
// =============================================================================

pub fn keygen<E: Pairing, R: RngCore>(
    a_mat: &SparseMatrix<E::ScalarField>,
    b_mat: &SparseMatrix<E::ScalarField>,
    num_variables: usize,
    instance_len: usize,
    rng: &mut R,
) -> (ProvingKey<E>, VerifyingKey<E>) {
    let num_constraints = a_mat.len();
    assert_eq!(b_mat.len(), num_constraints);

    // --- Generators + trapdoor ---
    let g = E::G1::rand(rng);
    let h = E::G2::rand(rng);
    let alpha = E::ScalarField::rand(rng);
    let beta = E::ScalarField::rand(rng);
    let delta_two = E::ScalarField::rand(rng);
    let tau = E::ScalarField::rand(rng);

    let alpha_g: E::G1 = g * alpha;
    let beta_g: E::G1 = g * beta;
    let delta_two_h: E::G2 = h * delta_two;
    let tau_h: E::G2 = h * tau;

    let delta_two_inverse = delta_two.inverse().unwrap();
    let alpha_over_delta_two = alpha * delta_two_inverse;
    let beta_over_delta_two = beta * delta_two_inverse;

    // --- Evaluation domain (Radix2 — upstream pins this explicitly) ---
    let domain = Radix2EvaluationDomain::<E::ScalarField>::new(num_constraints).unwrap();
    assert_ne!(
        domain.evaluate_vanishing_polynomial(tau),
        E::ScalarField::zero()
    );
    let domain_size = domain.size();
    let max_degree = domain_size - 1;

    // --- Compute a_i(τ), b_i(τ) via Lagrange-at-τ ---
    let lagrange_polys_at_tau = domain.evaluate_all_lagrange_coefficients(tau);
    let mut a = vec![E::ScalarField::zero(); num_variables];
    let mut b = vec![E::ScalarField::zero(); num_variables];
    for (i, u_i) in lagrange_polys_at_tau
        .iter()
        .enumerate()
        .take(num_constraints)
    {
        for &(coeff, idx) in &a_mat[i] {
            a[idx] += *u_i * coeff;
        }
        for &(coeff, idx) in &b_mat[i] {
            b[idx] += *u_i * coeff;
        }
    }

    // --- Powers of τ (length domain_size = max_degree + 1) ---
    let mut powers_of_tau = Vec::with_capacity(domain_size);
    let mut cur = E::ScalarField::one();
    for _ in 0..domain_size {
        powers_of_tau.push(cur);
        cur *= &tau;
    }

    // --- Build SRS via batch-mul preprocessing (upstream's hot path) ---
    let table = BatchMulPreprocessing::new(g, max_degree + 1);

    // Σ_a[i] = α τ^i · G, i = 0..max_degree
    let sigma_a_powers: Vec<_> = powers_of_tau.iter().map(|t| *t * alpha).collect();
    let sigma_a = table.batch_mul(&sigma_a_powers);

    // Σ_b[i] = β τ^i · G
    let sigma_b_powers: Vec<_> = powers_of_tau.iter().map(|t| *t * beta).collect();
    let sigma_b = table.batch_mul(&sigma_b_powers);

    // Σ_q_opening[i] = τ^i · G
    let sigma_q_opening = table.batch_mul(&powers_of_tau);

    // Σ[i] = (α a_i(τ) + β b_i(τ)) / δ_2 · G, for witness indices i ∈ [n, k)
    let sigma_powers: Vec<_> = a[instance_len..]
        .iter()
        .zip(&b[instance_len..])
        .map(|(a_i, b_i)| *a_i * alpha_over_delta_two + *b_i * beta_over_delta_two)
        .collect();
    let sigma = table.batch_mul(&sigma_powers);

    // Σ_q_comm[i] = τ^i / δ_2 · G, i = 0..max_degree (length = max_degree, not +1)
    let sigma_q_comm_powers: Vec<_> = powers_of_tau[..max_degree]
        .iter()
        .map(|t| *t * delta_two_inverse)
        .collect();
    let sigma_q_comm = table.batch_mul(&sigma_q_comm_powers);

    let vk = VerifyingKey {
        num_constraints,
        instance_len,
        g: g.into(),
        alpha_g: alpha_g.into(),
        beta_g: beta_g.into(),
        delta_two_h: delta_two_h.into(),
        tau_h: tau_h.into(),
        h: h.into(),
        domain,
    };
    let pk = ProvingKey {
        sigma,
        sigma_a,
        sigma_b,
        sigma_q_comm,
        sigma_q_opening,
        verifying_key: vk.clone(),
    };
    (pk, vk)
}

// =============================================================================
// Prover (port of pari/src/prover.rs::prove)
//
// Upstream takes `(circuit, pk)`; we take the assignment vectors directly
// (matching what upstream's `compute_wa_wb_za_zb` reaches in the end).
// =============================================================================

#[inline]
fn eval_constraint<F: Field>(row: &[(F, usize)], z: &[F]) -> F {
    let mut acc = F::zero();
    for &(c, j) in row {
        acc += c * z[j];
    }
    acc
}

pub fn prove<E: Pairing>(
    pk: &ProvingKey<E>,
    a_mat: &SparseMatrix<E::ScalarField>,
    b_mat: &SparseMatrix<E::ScalarField>,
    instance_assignment: &[E::ScalarField],
    witness_assignment: &[E::ScalarField],
) -> Proof<E> {
    let num_constraints = a_mat.len();
    let domain = Radix2EvaluationDomain::<E::ScalarField>::new(num_constraints).unwrap();
    let domain_size = domain.size();

    // assignment = (x ∥ w); punctured = (0 ∥ w) — upstream replicates this
    // in `compute_wa_wb_za_zb` to derive ŵ_M from ẑ_M without a separate pass.
    let mut assignment = instance_assignment.to_vec();
    assignment.extend_from_slice(witness_assignment);
    let mut punctured = vec![E::ScalarField::zero(); instance_assignment.len()];
    punctured.extend_from_slice(witness_assignment);

    let mut z_a = vec![E::ScalarField::zero(); domain_size];
    let mut z_b = vec![E::ScalarField::zero(); domain_size];
    let mut w_a = vec![E::ScalarField::zero(); domain_size];
    let mut w_b = vec![E::ScalarField::zero(); domain_size];
    for i in 0..num_constraints {
        z_a[i] = eval_constraint(&a_mat[i], &assignment);
        z_b[i] = eval_constraint(&b_mat[i], &assignment);
        w_a[i] = eval_constraint(&a_mat[i], &punctured);
        w_b[i] = eval_constraint(&b_mat[i], &punctured);
    }

    let z_a_hat = Evaluations::from_vec_and_domain(z_a, domain).interpolate();
    let z_b_hat = Evaluations::from_vec_and_domain(z_b, domain).interpolate();
    let w_a_hat = Evaluations::from_vec_and_domain(w_a, domain).interpolate();
    let w_b_hat = Evaluations::from_vec_and_domain(w_b, domain).interpolate();

    // q = (ẑ_A^2 - ẑ_B) / v_K
    let (q, _) = (&z_a_hat * &z_a_hat - &z_b_hat).divide_by_vanishing_poly(domain);

    // T = -(MSM(Σ, w) + MSM(Σ_q_comm, q))
    let t_ab = E::G1::msm_unchecked(&pk.sigma, witness_assignment);
    let t_q = E::G1::msm_unchecked(&pk.sigma_q_comm, &q.coeffs);
    let t: E::G1Affine = -((t_ab + t_q).into_affine());

    // Fiat–Shamir challenge r (instance_assignment[0] is the constant 1,
    // not part of the user-visible public input — upstream strips it).
    let r = compute_chall::<E>(&pk.verifying_key, &instance_assignment[1..], &t);

    // v_a = ŵ_A(r), v_b = ŵ_B(r), v_q = q(r)
    use ark_poly::Polynomial;
    let v_a = w_a_hat.evaluate(&r);
    let v_b = w_b_hat.evaluate(&r);
    let v_q = q.evaluate(&r);

    // Opening witnesses (ŵ_M - v_m) / (X - r), (q - v_q) / (X - r)
    let one = E::ScalarField::one();
    let chall_vanishing = DensePolynomial::from_coefficients_vec(vec![-r, one]);
    let w_a_const = DensePolynomial::from_coefficients_vec(vec![v_a]);
    let w_b_const = DensePolynomial::from_coefficients_vec(vec![v_b]);
    let q_const = DensePolynomial::from_coefficients_vec(vec![v_q]);
    let witness_a = (&w_a_hat - &w_a_const) / &chall_vanishing;
    let witness_b = (&w_b_hat - &w_b_const) / &chall_vanishing;
    let witness_q = (&q - &q_const) / &chall_vanishing;

    let w_a_proof = E::G1::msm_unchecked(&pk.sigma_a, &witness_a.coeffs);
    let w_b_proof = E::G1::msm_unchecked(&pk.sigma_b, &witness_b.coeffs);
    let q_proof = E::G1::msm_unchecked(&pk.sigma_q_opening, &witness_q.coeffs);
    let u: E::G1 = w_a_proof + w_b_proof + q_proof;

    Proof {
        t_g: t,
        u_g: u.into_affine(),
        v_a,
        v_b,
    }
}

// =============================================================================
// Verifier (port of pari/src/verifier.rs::verify)
//
// Lagrange-coefficients shortcut: x̂_A(r) = Σ_{i=0..n} L_{K-n+i}(r) · x[i],
// valid only when the matrix layout follows the upstream "instance
// outliner" convention — the test instance built in `pari.rs` constructs
// matrices that satisfy it (A's instance columns are zero on the
// original K-n constraints; the last n constraints are instance-defining
// e_i rows; B has no instance columns anywhere).
// =============================================================================

pub fn verify<E: Pairing>(
    proof: &Proof<E>,
    vk: &VerifyingKey<E>,
    public_input: &[E::ScalarField],
) -> bool
where
    <<E as Pairing>::G1Affine as AffineRepr>::BaseField: PrimeField,
    E::G1Affine: Neg<Output = E::G1Affine>,
{
    let Proof { t_g, u_g, v_a, v_b } = proof;
    let challenge = compute_chall::<E>(vk, public_input, t_g);

    let instance_size = vk.instance_len;
    let mut px_evaluations = Vec::with_capacity(instance_size);
    px_evaluations.push(E::ScalarField::ONE);
    px_evaluations.extend_from_slice(&public_input[..(instance_size - 1)]);

    let r1cs_orig_num_cnstrs = vk.num_constraints - instance_size;
    let (lagrange_coeffs, vanishing_poly_at_chall_inv) =
        eval_last_lagrange_coeffs(&vk.domain, challenge, r1cs_orig_num_cnstrs, vk.instance_len);

    let x_a = lagrange_coeffs
        .into_iter()
        .zip(px_evaluations)
        .fold(E::ScalarField::zero(), |acc, (x, d)| acc + x * d);
    let z_a = x_a + v_a;

    let v_q = (z_a * z_a - v_b) * vanishing_poly_at_chall_inv;

    // Multi-pairing equation:
    //   e(T, δ_2H) · e(U, τH) · e(v_a αG + v_b βG + v_q G − r·U, H) = 1_GT
    let bases = [vk.alpha_g, vk.beta_g, vk.g, -*u_g];
    let scalars = [*v_a, *v_b, v_q, challenge];
    let right_second_left: E::G1Affine = E::G1::msm_unchecked(&bases, &scalars).into_affine();

    let result = E::multi_pairing(
        [*t_g, *u_g, right_second_left],
        [vk.delta_two_h, vk.tau_h, vk.h],
    );
    result.is_zero()
}

/// Port of `pari::verifier::Pari::eval_last_lagrange_coeffs`.
///
/// Computes `L_{start_ind+i}(tau)` for `i ∈ 0..count`, where `L_j` is the
/// j-th Lagrange basis polynomial on `domain`. Returns those `count`
/// coefficients and the inverse of the vanishing polynomial at `tau`
/// (the verifier needs it for `v_q` anyway, so we reuse the computation).
fn eval_last_lagrange_coeffs<F: FftField>(
    domain: &Radix2EvaluationDomain<F>,
    tau: F,
    start_ind: usize,
    count: usize,
) -> (Vec<F>, F) {
    let z_h_at_tau: F = domain.evaluate_vanishing_polynomial(tau);
    let group_gen: F = domain.group_gen();
    assert!(!z_h_at_tau.is_zero());

    let group_gen_inv = domain.group_gen_inv();
    let v_0_inv = domain.size_as_field_element();

    let start_gen = group_gen.pow([start_ind as u64]);
    let z_h_at_tau_inv = z_h_at_tau.inverse().unwrap();
    let mut l_i = z_h_at_tau_inv * v_0_inv;
    let mut negative_cur_elem = -start_gen;
    let mut lagrange_coefficients_inverse = vec![F::zero(); count];
    for coeff in &mut lagrange_coefficients_inverse.iter_mut() {
        *coeff = l_i * (tau + negative_cur_elem);
        l_i *= &group_gen_inv;
        negative_cur_elem *= &group_gen;
    }
    batch_inversion_and_mul(lagrange_coefficients_inverse.as_mut_slice(), &start_gen);
    (lagrange_coefficients_inverse, z_h_at_tau_inv)
}

/// Inline port of `shared_utils::batch_inversion_and_mul` — Montgomery's
/// trick for batch field inversion, with each inverse pre-multiplied by
/// `coeff`. Bit-exact replica of the upstream single-threaded version.
fn batch_inversion_and_mul<F: Field>(v: &mut [F], coeff: &F) {
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
