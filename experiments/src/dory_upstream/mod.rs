//! Dory multilinear polynomial commitment (transparent mode), ported from
//! a16z's `dory-pcs` 0.4.2 (github.com/a16z/dory @ 5246da5) to arkworks 0.6
//! on BLS12-381. Protocol: Eval-VMV-RE of Dory (Lee, TCC 2021), §3-5.
//!
//! Ported: `ProverSetup::new` / `to_verifier_setup`, `commit`,
//! `create_evaluation_proof` and `verify_evaluation_proof`, the transparent
//! parts of `reduce_and_fold` (`DoryProverState`, `DoryVerifierState`), the
//! arkworks backend routines they call (parallel MSMs, folds, chunked
//! multi-pairings with the prepared-setup cache that jolt enables through the
//! `cache` feature) and `Blake2bTranscript`.
//!
//! Changes from upstream:
//!   - The trait layer (`Field`, `Group`, `PairingCurve`, `DoryRoutines`,
//!     `Mode`) is instantiated directly with BLS12-381 types, and the global
//!     prepared cache is a field of `ProverSetup`.
//!   - Square matrices only (nu = sigma), which is what the benchmark runs;
//!     upstream's nu < sigma padding is not ported.
//!   - Setup randomness comes from a caller-supplied rng.
//!   - Blinding (zk) is not ported; transparent mode samples zero blinds, so
//!     the masking terms upstream computes are dropped.

use ark_bls12_381::{Bls12_381, Fr, G1Affine, G1Projective as G1, G2Affine, G2Projective as G2};
use ark_ec::pairing::{MillerLoopOutput, Pairing, PairingOutput};
use ark_ec::{CurveGroup, VariableBaseMSM};
use ark_ff::{BigInteger, Field, One, PrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{UniformRand, rand::Rng};
use blake2::Blake2b512;
use digest::Digest;
use rayon::prelude::*;

pub type GT = PairingOutput<Bls12_381>;
type G2Prepared = <Bls12_381 as Pairing>::G2Prepared;
type G1Prepared = <Bls12_381 as Pairing>::G1Prepared;

// ---------------------------------------------------------------------------
// Setup (setup.rs)
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProverSetup {
    pub g1_vec: Vec<G1>,
    pub g2_vec: Vec<G2>,
    pub h1: G1,
    pub h2: G2,
    pub ht: GT,
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct VerifierSetup {
    pub delta_1l: Vec<GT>,
    pub delta_1r: Vec<GT>,
    pub delta_2l: Vec<GT>,
    pub delta_2r: Vec<GT>,
    pub chi: Vec<GT>,
    pub g1_0: G1,
    pub g2_0: G2,
    pub h1: G1,
    pub h2: G2,
    pub ht: GT,
    pub max_log_n: usize,
}

/// `ark_cache::PreparedCache`, built once from the setup vectors.
pub struct PreparedCache {
    pub g1_prepared: Vec<G1Prepared>,
    pub g2_prepared: Vec<G2Prepared>,
}

impl PreparedCache {
    /// `ark_cache::init_cache`.
    pub fn new(setup: &ProverSetup) -> Self {
        let (g1_prepared, g2_prepared) = rayon::join(
            || {
                setup
                    .g1_vec
                    .par_iter()
                    .map(|g| G1Affine::from(*g).into())
                    .collect()
            },
            || {
                setup
                    .g2_vec
                    .par_iter()
                    .map(|g| G2Affine::from(*g).into())
                    .collect()
            },
        );
        Self {
            g1_prepared,
            g2_prepared,
        }
    }
}

impl ProverSetup {
    pub fn new<R: Rng>(rng: &mut R, max_log_n: usize) -> Self {
        let n = 1 << max_log_n.div_ceil(2);
        let g1_vec: Vec<G1> = (0..n).map(|_| G1::rand(rng)).collect();
        let g2_vec: Vec<G2> = (0..n).map(|_| G2::rand(rng)).collect();
        // Upstream draws affine-normalized random points (z = 1).
        let g1_vec = G1::normalize_batch(&g1_vec)
            .into_iter()
            .map(G1::from)
            .collect();
        let g2_vec = G2::normalize_batch(&g2_vec)
            .into_iter()
            .map(G2::from)
            .collect();
        let h1 = G1::from(G1::rand(rng).into_affine());
        let h2 = G2::from(G2::rand(rng).into_affine());
        let ht = Bls12_381::pairing(h1, h2);
        Self {
            g1_vec,
            g2_vec,
            h1,
            h2,
            ht,
        }
    }

    pub fn to_verifier_setup(&self) -> VerifierSetup {
        let max_num_rounds = self.g1_vec.len().trailing_zeros() as usize;
        let mut delta_1l = Vec::with_capacity(max_num_rounds + 1);
        let mut delta_1r = Vec::with_capacity(max_num_rounds + 1);
        let mut delta_2r = Vec::with_capacity(max_num_rounds + 1);
        let mut chi: Vec<GT> = Vec::with_capacity(max_num_rounds + 1);
        for k in 0..=max_num_rounds {
            if k == 0 {
                delta_1l.push(GT::zero());
                delta_1r.push(GT::zero());
                delta_2r.push(GT::zero());
                chi.push(Bls12_381::pairing(self.g1_vec[0], self.g2_vec[0]));
            } else {
                let half_len = 1 << (k - 1);
                let full_len = 1 << k;
                let g1_first_half = &self.g1_vec[..half_len];
                let g1_second_half = &self.g1_vec[half_len..full_len];
                let g2_first_half = &self.g2_vec[..half_len];
                let g2_second_half = &self.g2_vec[half_len..full_len];
                delta_1l.push(chi[k - 1]);
                delta_1r.push(multi_pair(g1_second_half, g2_first_half));
                delta_2r.push(multi_pair(g1_first_half, g2_second_half));
                chi.push(chi[k - 1] + multi_pair(g1_second_half, g2_second_half));
            }
        }
        VerifierSetup {
            delta_1l: delta_1l.clone(),
            delta_1r,
            delta_2l: delta_1l,
            delta_2r,
            chi,
            g1_0: self.g1_vec[0],
            g2_0: self.g2_vec[0],
            h1: self.h1,
            h2: self.h2,
            ht: self.ht,
            max_log_n: max_num_rounds * 2,
        }
    }
}

// ---------------------------------------------------------------------------
// Backend routines (ark_group.rs, ark_pairing.rs)
// ---------------------------------------------------------------------------

fn msm_g1(bases: &[G1], scalars: &[Fr]) -> G1 {
    assert_eq!(
        bases.len(),
        scalars.len(),
        "MSM requires equal length vectors"
    );
    if bases.is_empty() {
        return G1::zero();
    }
    let bases_affine: Vec<G1Affine> = if bases.iter().all(|b| b.z.is_one()) {
        bases.iter().map(|b| b.into_affine()).collect()
    } else {
        G1::normalize_batch(bases)
    };
    G1::msm(&bases_affine, scalars).expect("MSM should not fail")
}

fn msm_g2(bases: &[G2], scalars: &[Fr]) -> G2 {
    assert_eq!(
        bases.len(),
        scalars.len(),
        "MSM requires equal length vectors"
    );
    if bases.is_empty() {
        return G2::zero();
    }
    let bases_affine: Vec<G2Affine> = if bases.iter().all(|b| b.z.is_one()) {
        bases.iter().map(|b| b.into_affine()).collect()
    } else {
        G2::normalize_batch(bases)
    };
    G2::msm(&bases_affine, scalars).expect("MSM should not fail")
}

fn fixed_base_vector_scalar_mul_g2(base: &G2, scalars: &[Fr]) -> Vec<G2> {
    scalars.par_iter().map(|s| *base * s).collect()
}

fn fixed_scalar_mul_bases_then_add<G: CurveGroup<ScalarField = Fr>>(
    bases: &[G],
    vs: &mut [G],
    scalar: &Fr,
) {
    assert_eq!(bases.len(), vs.len(), "Lengths must match");
    vs.par_iter_mut()
        .zip(bases.par_iter())
        .for_each(|(v, base)| *v += *base * scalar);
}

fn fixed_scalar_mul_vs_then_add<G: CurveGroup<ScalarField = Fr>>(
    vs: &mut [G],
    addends: &[G],
    scalar: &Fr,
) {
    assert_eq!(vs.len(), addends.len(), "Lengths must match");
    vs.par_iter_mut()
        .zip(addends.par_iter())
        .for_each(|(v, addend)| *v = *v * scalar + addend);
}

fn fold_field_vectors(left: &mut [Fr], right: &[Fr], scalar: &Fr) {
    assert_eq!(left.len(), right.len(), "Lengths must match");
    left.par_iter_mut()
        .zip(right.par_iter())
        .with_min_len(1 << 10)
        .for_each(|(l, r)| *l = *l * scalar + r);
}

fn determine_chunk_size(total: usize) -> usize {
    const MIN_CHUNK: usize = 32;
    const MAX_CHUNK: usize = 128;
    if total < MIN_CHUNK {
        return total;
    }
    total
        .div_ceil(rayon::current_num_threads())
        .clamp(MIN_CHUNK, MAX_CHUNK)
}

fn final_exp(ml: MillerLoopOutput<Bls12_381>) -> GT {
    Bls12_381::final_exponentiation(ml).expect("Final exponentiation should not fail")
}

fn product(
    a: MillerLoopOutput<Bls12_381>,
    b: MillerLoopOutput<Bls12_381>,
) -> MillerLoopOutput<Bls12_381> {
    MillerLoopOutput(a.0 * b.0)
}

fn identity_ml() -> MillerLoopOutput<Bls12_381> {
    MillerLoopOutput(<Bls12_381 as Pairing>::TargetField::one())
}

/// `multi_pair_parallel`.
pub fn multi_pair(ps: &[G1], qs: &[G2]) -> GT {
    assert_eq!(
        ps.len(),
        qs.len(),
        "multi_pair requires equal length vectors"
    );
    if ps.is_empty() {
        return GT::zero();
    }
    let chunk_size = determine_chunk_size(ps.len());
    let combined = ps
        .par_chunks(chunk_size)
        .zip(qs.par_chunks(chunk_size))
        .map(|(ps_chunk, qs_chunk)| {
            let ps_prep: Vec<G1Prepared> =
                ps_chunk.iter().map(|p| G1Affine::from(*p).into()).collect();
            let qs_prep: Vec<G2Prepared> =
                qs_chunk.iter().map(|q| G2Affine::from(*q).into()).collect();
            Bls12_381::multi_miller_loop(ps_prep, qs_prep)
        })
        .reduce(identity_ml, product);
    final_exp(combined)
}

/// `multi_pair_g2_setup_parallel` with the cache: qs = g2_vec[..ps.len()].
fn multi_pair_g2_setup(ps: &[G1], cache: &PreparedCache) -> GT {
    if ps.is_empty() {
        return GT::zero();
    }
    let chunk_size = determine_chunk_size(ps.len());
    let combined = ps
        .par_chunks(chunk_size)
        .enumerate()
        .map(|(chunk_idx, ps_chunk)| {
            let start_idx = chunk_idx * chunk_size;
            let end_idx = start_idx + ps_chunk.len();
            let ps_prep: Vec<G1Prepared> =
                ps_chunk.iter().map(|p| G1Affine::from(*p).into()).collect();
            let qs_prep = cache.g2_prepared[start_idx..end_idx].to_vec();
            Bls12_381::multi_miller_loop(ps_prep, qs_prep)
        })
        .reduce(identity_ml, product);
    final_exp(combined)
}

/// `multi_pair_g1_setup_parallel` with the cache: ps = g1_vec[..qs.len()].
fn multi_pair_g1_setup(qs: &[G2], cache: &PreparedCache) -> GT {
    if qs.is_empty() {
        return GT::zero();
    }
    let chunk_size = determine_chunk_size(qs.len());
    let combined = qs
        .par_chunks(chunk_size)
        .enumerate()
        .map(|(chunk_idx, qs_chunk)| {
            let start_idx = chunk_idx * chunk_size;
            let end_idx = start_idx + qs_chunk.len();
            let qs_prep: Vec<G2Prepared> =
                qs_chunk.iter().map(|q| G2Affine::from(*q).into()).collect();
            let ps_prep = cache.g1_prepared[start_idx..end_idx].to_vec();
            Bls12_381::multi_miller_loop(ps_prep, qs_prep)
        })
        .reduce(identity_ml, product);
    final_exp(combined)
}

fn pair(p: &G1, q: &G2) -> GT {
    Bls12_381::pairing(*p, *q)
}

// ---------------------------------------------------------------------------
// Transcript (blake2b_transcript.rs)
// ---------------------------------------------------------------------------

#[derive(Clone)]
pub struct Blake2bTranscript {
    hasher: Blake2b512,
    /// Test hook (not upstream): challenges handed out in order instead of
    /// hashing, so a proof can be recomputed under another prover's
    /// challenges.
    replay: Option<std::collections::VecDeque<Fr>>,
}

impl Blake2bTranscript {
    pub fn new(domain_label: &[u8]) -> Self {
        let mut hasher = Blake2b512::default();
        hasher.update(domain_label);
        Self {
            hasher,
            replay: None,
        }
    }

    /// A transcript whose challenges are `challenges`, in order.
    pub fn replay(challenges: Vec<Fr>) -> Self {
        Self {
            replay: Some(challenges.into()),
            ..Self::new(b"replay")
        }
    }

    fn append_bytes(&mut self, label: &[u8], bytes: &[u8]) {
        self.hasher.update(label);
        self.hasher.update((bytes.len() as u64).to_le_bytes());
        self.hasher.update(bytes);
    }

    /// `append_serde`: compressed serialization.
    pub fn append_serde<S: CanonicalSerialize>(&mut self, label: &[u8], s: &S) {
        let mut bytes = Vec::new();
        s.serialize_compressed(&mut bytes)
            .expect("serialization should not fail");
        self.append_bytes(label, &bytes);
    }

    pub fn append_field(&mut self, label: &[u8], x: &Fr) {
        self.append_bytes(label, &x.into_bigint().to_bytes_le());
    }

    pub fn challenge_scalar(&mut self, label: &[u8]) -> Fr {
        if let Some(queue) = self.replay.as_mut() {
            return queue
                .pop_front()
                .expect("replay transcript ran out of challenges");
        }
        self.hasher.update(label);
        let repr = self.hasher.clone().finalize().to_vec();
        let fe = Fr::from_le_bytes_mod_order(&repr);
        assert!(!fe.is_zero(), "Challenge scalar cannot be zero");
        self.hasher.update(&repr);
        fe
    }
}

// ---------------------------------------------------------------------------
// Messages and proof (messages.rs, proof.rs)
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct FirstReduceMessage {
    pub d1_left: GT,
    pub d1_right: GT,
    pub d2_left: GT,
    pub d2_right: GT,
    pub e1_beta: G1,
    pub e2_beta: G2,
}

#[derive(Clone, Debug)]
pub struct SecondReduceMessage {
    pub c_plus: GT,
    pub c_minus: GT,
    pub e1_plus: G1,
    pub e1_minus: G1,
    pub e2_plus: G2,
    pub e2_minus: G2,
}

#[derive(Clone, Debug)]
pub struct VMVMessage {
    pub c: GT,
    pub d2: GT,
    pub e1: G1,
}

#[derive(Clone, Debug)]
pub struct ScalarProductMessage {
    pub e1: G1,
    pub e2: G2,
}

#[derive(Clone, Debug)]
pub struct DoryProof {
    pub vmv_message: VMVMessage,
    pub first_messages: Vec<FirstReduceMessage>,
    pub second_messages: Vec<SecondReduceMessage>,
    pub final_message: ScalarProductMessage,
    pub nu: usize,
    pub sigma: usize,
}

// ---------------------------------------------------------------------------
// Polynomial (poly.rs, ark_poly.rs)
// ---------------------------------------------------------------------------

/// `multilinear_lagrange_basis` for a full-length output: point[0] is the low bit.
pub fn multilinear_lagrange_basis(output: &mut [Fr], point: &[Fr]) {
    assert!(output.len() <= (1 << point.len()));
    if point.is_empty() || output.is_empty() {
        output.fill(Fr::one());
        return;
    }
    output[0] = Fr::one() - point[0];
    if output.len() > 1 {
        output[1] = point[0];
    }
    for (level, p) in point[1..].iter().enumerate() {
        let mid = 1 << (level + 1);
        let one_minus_p = Fr::one() - p;
        if mid >= output.len() {
            for val in output.iter_mut() {
                *val *= one_minus_p;
            }
        } else {
            let (left, right) = output.split_at_mut(mid);
            let k = left.len().min(right.len());
            for (l, r) in left[..k].iter_mut().zip(right[..k].iter_mut()) {
                let l_val = *l;
                *r = l_val * p;
                *l = l_val * one_minus_p;
            }
            for l in &mut left[k..] {
                *l *= one_minus_p;
            }
        }
    }
}

/// `compute_left_right_vectors` for point.len() = nu + sigma.
pub fn compute_left_right_vectors(point: &[Fr], nu: usize, sigma: usize) -> (Vec<Fr>, Vec<Fr>) {
    let mut left_vec = vec![Fr::zero(); 1 << nu];
    let mut right_vec = vec![Fr::zero(); 1 << sigma];
    multilinear_lagrange_basis(&mut right_vec, &point[..sigma]);
    multilinear_lagrange_basis(&mut left_vec, &point[sigma..]);
    (left_vec, right_vec)
}

/// `ArkworksPolynomial::evaluate`.
pub fn evaluate(coefficients: &[Fr], point: &[Fr]) -> Fr {
    let mut basis = vec![Fr::zero(); coefficients.len()];
    multilinear_lagrange_basis(&mut basis, point);
    coefficients
        .iter()
        .zip(basis.iter())
        .map(|(c, b)| *c * b)
        .sum()
}

/// `ArkworksPolynomial::commit` (transparent): row commitments with Γ1, then
/// the tier-2 multi-pairing with Γ2.
pub fn commit(
    coefficients: &[Fr],
    nu: usize,
    sigma: usize,
    setup: &ProverSetup,
    cache: &PreparedCache,
) -> (GT, Vec<G1>) {
    assert_eq!(coefficients.len(), 1 << (nu + sigma));
    let num_rows = 1 << nu;
    let num_cols = 1 << sigma;
    let g1 = &setup.g1_vec[..num_cols];
    let row_commitments: Vec<G1> = (0..num_rows)
        .map(|i| msm_g1(g1, &coefficients[i * num_cols..(i + 1) * num_cols]))
        .collect();
    let tier_2 = multi_pair_g2_setup(&row_commitments, cache);
    (tier_2, row_commitments)
}

/// `ArkworksPolynomial::vector_matrix_product`.
fn vector_matrix_product(coefficients: &[Fr], left_vec: &[Fr], nu: usize, sigma: usize) -> Vec<Fr> {
    let num_cols = 1 << sigma;
    let num_rows = 1 << nu;
    let mut v_vec = vec![Fr::zero(); num_cols];
    for (j, v) in v_vec.iter_mut().enumerate() {
        let mut sum = Fr::zero();
        for (i, left_val) in left_vec.iter().enumerate().take(num_rows) {
            sum += *left_val * coefficients[i * num_cols + j];
        }
        *v = sum;
    }
    v_vec
}

// ---------------------------------------------------------------------------
// Reduce and fold (reduce_and_fold.rs, transparent)
// ---------------------------------------------------------------------------

struct DoryProverState<'a> {
    v1: Vec<G1>,
    v2: Vec<G2>,
    v2_scalars: Option<Vec<Fr>>,
    s1: Vec<Fr>,
    s2: Vec<Fr>,
    num_rounds: usize,
    setup: &'a ProverSetup,
    cache: &'a PreparedCache,
}

impl DoryProverState<'_> {
    fn compute_first_message(&self) -> FirstReduceMessage {
        let n2 = 1 << (self.num_rounds - 1);
        let (v1_l, v1_r) = self.v1.split_at(n2);
        let (v2_l, v2_r) = self.v2.split_at(n2);
        let g1_prime = &self.setup.g1_vec[..n2];
        let d1_left = multi_pair_g2_setup(v1_l, self.cache);
        let d1_right = multi_pair_g2_setup(v1_r, self.cache);
        let (d2_left, d2_right) = if let Some(scalars) = self.v2_scalars.as_ref() {
            let (s_l, s_r) = scalars.split_at(n2);
            let g2_fin = &self.setup.g2_vec[0];
            (
                pair(&msm_g1(g1_prime, s_l), g2_fin),
                pair(&msm_g1(g1_prime, s_r), g2_fin),
            )
        } else {
            (
                multi_pair_g1_setup(v2_l, self.cache),
                multi_pair_g1_setup(v2_r, self.cache),
            )
        };
        let e1_beta = msm_g1(&self.setup.g1_vec[..1 << self.num_rounds], &self.s2);
        let e2_beta = msm_g2(&self.setup.g2_vec[..1 << self.num_rounds], &self.s1);
        FirstReduceMessage {
            d1_left,
            d1_right,
            d2_left,
            d2_right,
            e1_beta,
            e2_beta,
        }
    }

    fn apply_first_challenge(&mut self, beta: &Fr) {
        let beta_inv = beta.inverse().expect("beta must be invertible");
        let n = 1 << self.num_rounds;
        fixed_scalar_mul_bases_then_add(&self.setup.g1_vec[..n], &mut self.v1, beta);
        fixed_scalar_mul_bases_then_add(&self.setup.g2_vec[..n], &mut self.v2, &beta_inv);
        self.v2_scalars = None;
    }

    fn compute_second_message(&self) -> SecondReduceMessage {
        let n2 = 1 << (self.num_rounds - 1);
        let (v1_l, v1_r) = self.v1.split_at(n2);
        let (v2_l, v2_r) = self.v2.split_at(n2);
        let (s1_l, s1_r) = self.s1.split_at(n2);
        let (s2_l, s2_r) = self.s2.split_at(n2);
        SecondReduceMessage {
            c_plus: multi_pair(v1_l, v2_r),
            c_minus: multi_pair(v1_r, v2_l),
            e1_plus: msm_g1(v1_l, s2_r),
            e1_minus: msm_g1(v1_r, s2_l),
            e2_plus: msm_g2(v2_r, s1_l),
            e2_minus: msm_g2(v2_l, s1_r),
        }
    }

    fn apply_second_challenge(&mut self, alpha: &Fr) {
        let alpha_inv = alpha.inverse().expect("alpha must be invertible");
        let n2 = 1 << (self.num_rounds - 1);
        let (v1_l, v1_r) = self.v1.split_at_mut(n2);
        fixed_scalar_mul_vs_then_add(v1_l, v1_r, alpha);
        self.v1.truncate(n2);
        let (v2_l, v2_r) = self.v2.split_at_mut(n2);
        fixed_scalar_mul_vs_then_add(v2_l, v2_r, &alpha_inv);
        self.v2.truncate(n2);
        let (s1_l, s1_r) = self.s1.split_at_mut(n2);
        fold_field_vectors(s1_l, s1_r, alpha);
        self.s1.truncate(n2);
        let (s2_l, s2_r) = self.s2.split_at_mut(n2);
        fold_field_vectors(s2_l, s2_r, &alpha_inv);
        self.s2.truncate(n2);
        self.num_rounds -= 1;
    }

    fn apply_fold_scalars(&mut self, gamma: &Fr) {
        let gamma_inv = gamma.inverse().expect("gamma must be invertible");
        self.v1[0] += self.setup.h1 * (*gamma * self.s1[0]);
        self.v2[0] += self.setup.h2 * (gamma_inv * self.s2[0]);
    }
}

struct DoryVerifierState {
    c: GT,
    d1: GT,
    d2: GT,
    e1: G1,
    e2: G2,
    e1_init: G1,
    d2_init: GT,
    s1_acc: Fr,
    s2_acc: Fr,
    s1_coords: Vec<Fr>,
    s2_coords: Vec<Fr>,
    num_rounds: usize,
}

impl DoryVerifierState {
    fn process_round(
        &mut self,
        setup: &VerifierSetup,
        first_msg: &FirstReduceMessage,
        second_msg: &SecondReduceMessage,
        alpha: &Fr,
        beta: &Fr,
    ) -> bool {
        if self.num_rounds == 0 {
            return false;
        }
        let (Some(alpha_inv), Some(beta_inv)) = (alpha.inverse(), beta.inverse()) else {
            return false;
        };
        let k = self.num_rounds;
        self.c = self.c
            + setup.chi[k]
            + self.d2 * beta
            + self.d1 * beta_inv
            + second_msg.c_plus * alpha
            + second_msg.c_minus * alpha_inv;
        let alpha_beta = *alpha * beta;
        self.d1 = first_msg.d1_left * alpha
            + first_msg.d1_right
            + setup.delta_1l[k] * alpha_beta
            + setup.delta_1r[k] * beta;
        let alpha_inv_beta_inv = alpha_inv * beta_inv;
        self.d2 = first_msg.d2_left * alpha_inv
            + first_msg.d2_right
            + setup.delta_2l[k] * alpha_inv_beta_inv
            + setup.delta_2r[k] * beta_inv;
        self.e1 = self.e1
            + first_msg.e1_beta * beta
            + second_msg.e1_plus * alpha
            + second_msg.e1_minus * alpha_inv;
        self.e2 = self.e2
            + first_msg.e2_beta * beta_inv
            + second_msg.e2_plus * alpha
            + second_msg.e2_minus * alpha_inv;
        let idx = self.num_rounds - 1;
        let (y_t, x_t) = (self.s1_coords[idx], self.s2_coords[idx]);
        let one = Fr::one();
        self.s1_acc *= *alpha * (one - y_t) + y_t;
        self.s2_acc *= alpha_inv * (one - x_t) + x_t;
        self.num_rounds -= 1;
        true
    }

    /// Transparent 4-pairing final check.
    fn verify_final(
        &self,
        setup: &VerifierSetup,
        msg: &ScalarProductMessage,
        gamma: &Fr,
        d: &Fr,
    ) -> bool {
        let (Some(d_inv), Some(gamma_inv)) = (d.inverse(), gamma.inverse()) else {
            return false;
        };
        let d_sq = *d * d;
        let neg_gamma = -*gamma;
        let neg_gamma_inv = -gamma_inv;
        let s_product = self.s1_acc * self.s2_acc;
        let rhs = self.c
            + setup.ht * s_product
            + setup.chi[0]
            + self.d2 * d
            + self.d1 * d_inv
            + self.d2_init * d_sq;
        let p1_g1 = msg.e1 + setup.g1_0 * d;
        let p1_g2 = msg.e2 + setup.g2_0 * d_inv;
        let p2_g1 = setup.h1;
        let p2_g2 = (self.e2 + setup.g2_0 * (d_inv * self.s1_acc)) * neg_gamma;
        let p3_g1 = (self.e1 + setup.g1_0 * (*d * self.s2_acc)) * neg_gamma_inv;
        let p3_g2 = setup.h2;
        let p4_g1 = self.e1_init * d_sq;
        let p4_g2 = setup.g2_0;
        let lhs = multi_pair(&[p1_g1, p2_g1, p3_g1, p4_g1], &[p1_g2, p2_g2, p3_g2, p4_g2]);
        lhs == rhs
    }
}

// ---------------------------------------------------------------------------
// Evaluation proof (evaluation_proof.rs, transparent)
// ---------------------------------------------------------------------------

/// `create_evaluation_proof` with precomputed row commitments.
#[allow(clippy::too_many_arguments)] // mirrors upstream's signature
pub fn create_evaluation_proof(
    coefficients: &[Fr],
    point: &[Fr],
    row_commitments: Vec<G1>,
    nu: usize,
    sigma: usize,
    setup: &ProverSetup,
    cache: &PreparedCache,
    transcript: &mut Blake2bTranscript,
) -> DoryProof {
    assert_eq!(point.len(), nu + sigma);
    assert_eq!(nu, sigma, "the port supports square matrices only");

    let (left_vec, right_vec) = compute_left_right_vectors(point, nu, sigma);
    let v_vec = vector_matrix_product(coefficients, &left_vec, nu, sigma);

    let g2_fin = &setup.g2_vec[0];
    // C = e(⟨row_commitments, v_vec⟩, Γ2,fin)
    let t_vec_v = msm_g1(&row_commitments, &v_vec);
    let c = pair(&t_vec_v, g2_fin);
    // D₂ = e(⟨Γ₁[sigma], v_vec⟩, Γ2,fin)
    let d2 = pair(&msm_g1(&setup.g1_vec[..1 << sigma], &v_vec), g2_fin);
    // E₁ = ⟨row_commitments, left_vec⟩
    let e1 = msm_g1(&row_commitments, &left_vec);
    let vmv_message = VMVMessage { c, d2, e1 };

    transcript.append_serde(b"vmv_c", &vmv_message.c);
    transcript.append_serde(b"vmv_d2", &vmv_message.d2);
    transcript.append_serde(b"vmv_e1", &vmv_message.e1);

    // v₂ = v_vec · Γ₂,fin
    let v2 = fixed_base_vector_scalar_mul_g2(g2_fin, &v_vec);

    let mut prover_state = DoryProverState {
        num_rounds: row_commitments.len().trailing_zeros() as usize,
        v1: row_commitments,
        v2,
        v2_scalars: Some(v_vec),
        s1: right_vec,
        s2: left_vec,
        setup,
        cache,
    };

    let num_rounds = nu.max(sigma);
    let mut first_messages = Vec::with_capacity(num_rounds);
    let mut second_messages = Vec::with_capacity(num_rounds);
    for _round in 0..num_rounds {
        let first_msg = prover_state.compute_first_message();
        transcript.append_serde(b"d1_left", &first_msg.d1_left);
        transcript.append_serde(b"d1_right", &first_msg.d1_right);
        transcript.append_serde(b"d2_left", &first_msg.d2_left);
        transcript.append_serde(b"d2_right", &first_msg.d2_right);
        transcript.append_serde(b"e1_beta", &first_msg.e1_beta);
        transcript.append_serde(b"e2_beta", &first_msg.e2_beta);
        let beta = transcript.challenge_scalar(b"beta");
        prover_state.apply_first_challenge(&beta);
        first_messages.push(first_msg);

        let second_msg = prover_state.compute_second_message();
        transcript.append_serde(b"c_plus", &second_msg.c_plus);
        transcript.append_serde(b"c_minus", &second_msg.c_minus);
        transcript.append_serde(b"e1_plus", &second_msg.e1_plus);
        transcript.append_serde(b"e1_minus", &second_msg.e1_minus);
        transcript.append_serde(b"e2_plus", &second_msg.e2_plus);
        transcript.append_serde(b"e2_minus", &second_msg.e2_minus);
        let alpha = transcript.challenge_scalar(b"alpha");
        prover_state.apply_second_challenge(&alpha);
        second_messages.push(second_msg);
    }

    let gamma = transcript.challenge_scalar(b"gamma");
    prover_state.apply_fold_scalars(&gamma);

    let final_message = ScalarProductMessage {
        e1: prover_state.v1[0],
        e2: prover_state.v2[0],
    };
    transcript.append_serde(b"final_e1", &final_message.e1);
    transcript.append_serde(b"final_e2", &final_message.e2);
    let _d = transcript.challenge_scalar(b"d");

    DoryProof {
        vmv_message,
        first_messages,
        second_messages,
        final_message,
        nu,
        sigma,
    }
}

/// `verify_evaluation_proof` (transparent).
pub fn verify_evaluation_proof(
    commitment: GT,
    evaluation: Fr,
    point: &[Fr],
    proof: &DoryProof,
    setup: &VerifierSetup,
    transcript: &mut Blake2bTranscript,
) -> bool {
    let nu = proof.nu;
    let sigma = proof.sigma;
    if point.len() != nu + sigma || nu > sigma {
        return false;
    }

    let vmv_message = &proof.vmv_message;
    transcript.append_serde(b"vmv_c", &vmv_message.c);
    transcript.append_serde(b"vmv_d2", &vmv_message.d2);
    transcript.append_serde(b"vmv_e1", &vmv_message.e1);

    let e2 = setup.g2_0 * evaluation;

    let num_rounds = sigma;
    if num_rounds > setup.max_log_n / 2
        || proof.first_messages.len() != num_rounds
        || proof.second_messages.len() != num_rounds
    {
        return false;
    }

    let s1_coords: Vec<Fr> = point[..sigma].to_vec();
    let mut s2_coords: Vec<Fr> = vec![Fr::zero(); sigma];
    s2_coords[..nu].copy_from_slice(&point[sigma..sigma + nu]);

    let mut verifier_state = DoryVerifierState {
        c: vmv_message.c,
        d1: commitment,
        d2: vmv_message.d2,
        e1: vmv_message.e1,
        e2,
        e1_init: vmv_message.e1,
        d2_init: vmv_message.d2,
        s1_acc: Fr::one(),
        s2_acc: Fr::one(),
        s1_coords,
        s2_coords,
        num_rounds,
    };

    for round in 0..num_rounds {
        let first_msg = &proof.first_messages[round];
        let second_msg = &proof.second_messages[round];
        transcript.append_serde(b"d1_left", &first_msg.d1_left);
        transcript.append_serde(b"d1_right", &first_msg.d1_right);
        transcript.append_serde(b"d2_left", &first_msg.d2_left);
        transcript.append_serde(b"d2_right", &first_msg.d2_right);
        transcript.append_serde(b"e1_beta", &first_msg.e1_beta);
        transcript.append_serde(b"e2_beta", &first_msg.e2_beta);
        let beta = transcript.challenge_scalar(b"beta");
        transcript.append_serde(b"c_plus", &second_msg.c_plus);
        transcript.append_serde(b"c_minus", &second_msg.c_minus);
        transcript.append_serde(b"e1_plus", &second_msg.e1_plus);
        transcript.append_serde(b"e1_minus", &second_msg.e1_minus);
        transcript.append_serde(b"e2_plus", &second_msg.e2_plus);
        transcript.append_serde(b"e2_minus", &second_msg.e2_minus);
        let alpha = transcript.challenge_scalar(b"alpha");
        if !verifier_state.process_round(setup, first_msg, second_msg, &alpha, &beta) {
            return false;
        }
    }

    let gamma = transcript.challenge_scalar(b"gamma");
    let msg = &proof.final_message;
    transcript.append_serde(b"final_e1", &msg.e1);
    transcript.append_serde(b"final_e2", &msg.e2);
    let d = transcript.challenge_scalar(b"d");
    verifier_state.verify_final(setup, msg, &gamma, &d)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_std::rand::{SeedableRng, rngs::StdRng};

    #[test]
    fn transparent_roundtrip() {
        let mut rng = StdRng::seed_from_u64(3);
        for k in [1usize, 2, 3] {
            let setup = ProverSetup::new(&mut rng, 2 * k);
            let vsetup = setup.to_verifier_setup();
            let cache = PreparedCache::new(&setup);
            let coeffs: Vec<Fr> = (0..1 << (2 * k)).map(|_| Fr::rand(&mut rng)).collect();
            let point: Vec<Fr> = (0..2 * k).map(|_| Fr::rand(&mut rng)).collect();
            let y = evaluate(&coeffs, &point);
            let (com, rows) = commit(&coeffs, k, k, &setup, &cache);
            let mut tp = Blake2bTranscript::new(b"dory");
            let proof =
                create_evaluation_proof(&coeffs, &point, rows, k, k, &setup, &cache, &mut tp);
            let mut tv = Blake2bTranscript::new(b"dory");
            assert!(verify_evaluation_proof(
                com, y, &point, &proof, &vsetup, &mut tv
            ));
            let mut tv = Blake2bTranscript::new(b"dory");
            assert!(!verify_evaluation_proof(
                com,
                y + Fr::one(),
                &point,
                &proof,
                &vsetup,
                &mut tv
            ));
            let mut bad = proof.clone();
            bad.final_message.e1 += setup.h1;
            let mut tv = Blake2bTranscript::new(b"dory");
            assert!(!verify_evaluation_proof(
                com, y, &point, &bad, &vsetup, &mut tv
            ));
        }
    }
}
