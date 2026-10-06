//! Vendored DeKART univariate range proof (v2), ported from
//! aptos-labs/aptos-core `crates/aptos-dkg/src/range_proofs/dekart_univariate_v2.rs`
//! (main, fetched 2026-09-27). Paper: <https://eprint.iacr.org/2025/1159>,
//! blog: <https://alinush.github.io/dekart>.
//!
//! Why vendored: aptos-dkg pins arkworks 0.5 (a fork of algebra.git) and drags
//! in the whole aptos-crypto stack (blstrs, bcs, derive macros, ...). This copy
//! runs on the same git-main arkworks 0.6 as the zippel side so MSM / FFT /
//! pairing primitives are bit-identical on both sides.
//!
//! What changed vs. upstream (none of it touches the hot path):
//!   - The generic `sigma_protocol` / `homomorphism` / `fixed_base_msms` trait
//!     framework is flattened into direct functions for the only two
//!     homomorphisms DeKART uses: the hiding-KZG commitment (`hkzg`) and the
//!     two-term Okamoto PoK (`two_term_msm`). Same MSMs, same arithmetic.
//!   - The helpers pulled from aptos-crypto (`barycentric_eval`,
//!     `quotient_evaluations_batch`, `differentiate[_in_place]`, `msm_bool`,
//!     `lagrange_basis`, `scalars_to_bits_le`, `transpose_bit_matrix`,
//!     `sample_field_element`) are copied verbatim.
//!   - Fiat–Shamir uses merlin with upstream's labels and challenge widths
//!     (128-bit betas/mus, full-width gamma/sigma challenge). The byte encoding
//!     of absorbed items is canonical-compressed but not byte-identical to
//!     upstream (upstream serializes sigma-proof enums / bcs context via
//!     derive macros), so proofs are not interoperable with aptos-dkg. Cost
//!     is unchanged: a handful of O(ell) hash absorptions.
//!   - Sigma-protocol verification: upstream merges the single MSM input via a
//!     HashMap (no-op for one input) then runs a 4-term MSM; we run the same
//!     4-term MSM directly.
//!   - `#[cfg(feature = "range_proof_timing_univariate_v2")]` timing probes and
//!     the (de)serialization of precomputed tables are dropped.

use ark_ec::{
    AffineRepr, CurveGroup, VariableBaseMSM,
    pairing::{Pairing, PairingOutput},
};
use ark_ff::{AdditiveGroup, Field, PrimeField, Zero};
use ark_poly::{EvaluationDomain, Polynomial, Radix2EvaluationDomain};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::{CryptoRng, RngCore};
use merlin::Transcript;

pub const DST: &[u8] = b"APTOS_UNIVARIATE_DEKART_V2_RANGE_PROOF_DST";

// ---------------------------------------------------------------------------
// aptos-crypto helpers (verbatim)
// ---------------------------------------------------------------------------

pub fn sample_field_element<F: PrimeField, R: RngCore>(rng: &mut R) -> F {
    loop {
        let num_bytes = (F::MODULUS_BIT_SIZE as usize).div_ceil(8);
        let mut bytes = vec![0u8; num_bytes];
        rng.fill_bytes(&mut bytes);
        if let Some(f) = F::from_random_bytes(&bytes) {
            return f;
        }
    }
}

pub fn sample_field_elements<F: PrimeField, R: RngCore>(n: usize, rng: &mut R) -> Vec<F> {
    (0..n).map(|_| sample_field_element(rng)).collect()
}

fn powers<F: Field>(x: F, n: usize) -> Vec<F> {
    let mut v = Vec::with_capacity(n);
    let mut acc = F::one();
    for _ in 0..n {
        v.push(acc);
        acc *= x;
    }
    v
}

pub fn powers_of_two<F: Field>(ell: usize) -> Vec<F> {
    (0..ell).map(|j| F::from(1u64 << j)).collect()
}

pub fn msm_bool<A: AffineRepr>(bases: &[A], scalars: &[bool]) -> A::Group {
    debug_assert_eq!(bases.len(), scalars.len());
    let mut acc = A::Group::zero();
    for (base, &bit) in bases.iter().zip(scalars) {
        if bit {
            acc += base;
        }
    }
    acc
}

pub fn lagrange_basis<C: CurveGroup>(
    group_generator: C,
    tau: C::ScalarField,
    n: usize,
    eval_dom: Radix2EvaluationDomain<C::ScalarField>,
) -> Vec<C::Affine> {
    let powers_of_tau = powers(tau, n);
    let lagr_basis_scalars = eval_dom.ifft(&powers_of_tau);
    group_generator.batch_mul(&lagr_basis_scalars)
}

mod polynomials {
    use super::*;

    pub fn differentiate<F: Field>(coeffs: &[F]) -> Vec<F> {
        let degree = coeffs.len().saturating_sub(1);
        let mut result = Vec::with_capacity(degree);
        for i in 0..degree {
            result.push(coeffs[i + 1] * F::from((i + 1) as u64));
        }
        result
    }

    pub fn differentiate_in_place<F: Field>(coeffs: &mut Vec<F>) {
        let degree = coeffs.len() - 1;
        for i in 0..degree {
            coeffs[i] = coeffs[i + 1] * F::from((i + 1) as u64);
        }
        coeffs.truncate(degree);
    }

    pub fn quotient_evaluations_batch<F: Field>(f_vals: &[F], x_vals: &[F], x: F, y: F) -> Vec<F> {
        assert_eq!(f_vals.len(), x_vals.len());
        let mut denoms: Vec<F> = x_vals.iter().map(|&xi| xi - x).collect();
        ark_ff::batch_inversion(&mut denoms);
        f_vals
            .iter()
            .zip(denoms.iter())
            .map(|(&f_val, &denom_inv)| (f_val - y) * denom_inv)
            .collect()
    }

    pub fn barycentric_eval<F: Field>(evals: &[F], roots: &[F], x: F, n_inv: F) -> F {
        let n = evals.len();
        assert_eq!(n, roots.len());
        let mut denoms = Vec::with_capacity(n);
        for (&omega_j, &val) in roots.iter().zip(evals.iter()) {
            let denom = x - omega_j;
            if denom.is_zero() {
                return val;
            }
            denoms.push(denom);
        }
        let mut z_pow_n = x.pow([n as u64]);
        z_pow_n -= F::one();
        let prefactor = z_pow_n * n_inv;
        ark_ff::batch_inversion(&mut denoms);
        let mut sum = F::zero();
        for ((omega_j, &f_j), &inv) in roots.iter().zip(evals.iter()).zip(denoms.iter()) {
            sum += *omega_j * f_j * inv;
        }
        sum * prefactor
    }
}

mod scalars_to_bits {
    use super::*;

    pub fn transpose_bit_matrix(bit_matrix: &[Vec<bool>]) -> Vec<Vec<bool>> {
        let num_cols = match bit_matrix.first() {
            Some(row) => row.len(),
            None => return vec![],
        };
        (0..num_cols)
            .map(|j| bit_matrix.iter().map(|row| row[j]).collect())
            .collect()
    }

    pub fn scalars_to_bits_le<F: PrimeField>(
        scalars: &[F],
        number_of_bits: usize,
    ) -> Vec<Vec<bool>> {
        scalars
            .iter()
            .map(|s| {
                let bigint: F::BigInt = s.into_bigint();
                ark_ff::BitIteratorLE::new(&bigint)
                    .take(number_of_bits)
                    .collect::<Vec<_>>()
            })
            .collect()
    }
}

// ---------------------------------------------------------------------------
// Fiat–Shamir (merlin, upstream labels)
// ---------------------------------------------------------------------------

mod fiat_shamir {
    use super::*;

    fn append<T: CanonicalSerialize>(t: &mut Transcript, label: &'static [u8], v: &T) {
        let mut buf = Vec::new();
        v.serialize_compressed(&mut buf)
            .expect("serialize for transcript");
        t.append_message(label, &buf);
    }

    fn challenge_full_scalars<F: PrimeField>(
        t: &mut Transcript,
        label: &'static [u8],
        n: usize,
    ) -> Vec<F> {
        let byte_size = (F::MODULUS_BIT_SIZE as usize) / 8;
        let mut buf = vec![0u8; 2 * n * byte_size];
        t.challenge_bytes(label, &mut buf);
        buf.chunks(2 * byte_size)
            .map(F::from_le_bytes_mod_order)
            .collect()
    }

    fn challenge_128bit_scalars<F: PrimeField>(
        t: &mut Transcript,
        label: &'static [u8],
        n: usize,
    ) -> Vec<F> {
        let mut buf = vec![0u8; n * 16];
        t.challenge_bytes(label, &mut buf);
        buf.chunks(16).map(F::from_le_bytes_mod_order).collect()
    }

    pub fn append_initial_data<E: Pairing>(
        t: &mut Transcript,
        vk: &VerificationKey<E>,
        n: usize,
        ell: usize,
        comm: &E::G1Affine,
    ) {
        t.append_message(b"dom-sep", DST);
        // upstream's `SerializeForFiatShamirTranscript for VerificationKey`:
        // xi_1, lagr_0, vk_hkzg (skips the precomputed tables)
        let mut vk_bytes = Vec::new();
        vk.xi_1.serialize_compressed(&mut vk_bytes).unwrap();
        vk.lagr_0.serialize_compressed(&mut vk_bytes).unwrap();
        vk.vk_hkzg.serialize_compressed(&mut vk_bytes).unwrap();
        t.append_message(b"vk", &vk_bytes);
        let mut ps = Vec::new();
        (n as u64).serialize_compressed(&mut ps).unwrap();
        (ell as u64).serialize_compressed(&mut ps).unwrap();
        comm.serialize_compressed(&mut ps).unwrap();
        t.append_message(b"public-statements", &ps);
    }

    pub fn append_hat_f_commitment<E: Pairing>(t: &mut Transcript, c: &E::G1Affine) {
        append(t, b"hat-f-commitment", c);
    }

    pub fn append_sigma_proof<E: Pairing>(t: &mut Transcript, p: &two_term_msm::Proof<E>) {
        append(t, b"sigma-proof-commitment", p);
    }

    pub fn append_f_j_commitments<E: Pairing>(t: &mut Transcript, cs: &Vec<E::G1Affine>) {
        append(t, b"f-j-commitments", cs);
    }

    pub fn append_h_commitment<E: Pairing>(t: &mut Transcript, d: &E::G1Affine) {
        append(t, b"h-commitment", d);
    }

    pub fn get_beta_challenges<E: Pairing>(
        t: &mut Transcript,
        ell: usize,
    ) -> (E::ScalarField, Vec<E::ScalarField>) {
        let mut betas = challenge_128bit_scalars(t, b"challenge-for-quotient-polynomials", ell + 1);
        let beta = betas
            .pop()
            .expect("The betas must have at least one element");
        (beta, betas)
    }

    pub fn get_gamma_challenge<E: Pairing>(
        t: &mut Transcript,
        roots: &[E::ScalarField],
    ) -> E::ScalarField {
        loop {
            let gamma =
                challenge_full_scalars(t, b"verifier-challenge-for-linear-combination", 1)[0];
            if !roots.contains(&gamma) {
                return gamma;
            }
        }
    }

    pub fn append_evaluations_at_gamma<E: Pairing>(
        t: &mut Transcript,
        a: E::ScalarField,
        a_h: E::ScalarField,
        a_js: &[E::ScalarField],
    ) {
        let mut buf = Vec::new();
        a.serialize_compressed(&mut buf).unwrap();
        a_h.serialize_compressed(&mut buf).unwrap();
        for x in a_js {
            x.serialize_compressed(&mut buf).unwrap();
        }
        t.append_message(b"evaluation-points", &buf);
    }

    pub fn get_mu_challenges<E: Pairing>(
        t: &mut Transcript,
        ell: usize,
    ) -> (E::ScalarField, E::ScalarField, Vec<E::ScalarField>) {
        let mut mus = challenge_128bit_scalars(t, b"challenge-for-linear-combination", ell + 2);
        let mu = mus.pop().expect("The mus must have at least one element");
        let mu_h = mus.pop().expect("The mus must have at least two elements");
        (mu, mu_h, mus)
    }

    pub fn sigma_challenge<E: Pairing>(
        hom: &two_term_msm::Homomorphism<E>,
        statement: &E::G1Affine,
        first_msg: &E::G1Affine,
    ) -> E::ScalarField {
        let mut t = Transcript::new(b"DEKART_V2_SIGMA_PROTOCOL");
        // upstream: bcs::to_bytes(&DST) = uleb128(len) || DST
        let mut cntxt = vec![DST.len() as u8];
        cntxt.extend_from_slice(DST);
        t.append_message(b"cntxt", &cntxt);
        let mut hb = Vec::new();
        hom.base_1.serialize_compressed(&mut hb).unwrap();
        hom.base_2.serialize_compressed(&mut hb).unwrap();
        t.append_message(b"hom-msm-bases", &hb);
        append(&mut t, b"sigma-protocol-claim", statement);
        append(&mut t, b"sigma-protocol-first-message", first_msg);
        challenge_full_scalars(&mut t, b"challenge-for-sigma-protocol", 1)[0]
    }
}

// ---------------------------------------------------------------------------
// Hiding KZG in the Lagrange basis (upstream `pcs/univariate_hiding_kzg.rs`)
// ---------------------------------------------------------------------------

pub mod hkzg {
    use super::*;

    #[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Copy, Debug, PartialEq, Eq)]
    pub struct VerificationKey<E: Pairing> {
        pub xi_2: E::G2Affine,
        pub tau_2: E::G2Affine,
        pub g1: E::G1Affine,
        pub g2: E::G2Affine,
    }

    #[derive(Clone, Debug)]
    pub struct CommitmentKey<E: Pairing> {
        pub xi_1: E::G1Affine,
        pub tau_1: E::G1Affine,
        pub lagr_g1: Vec<E::G1Affine>,
        pub eval_dom: Radix2EvaluationDomain<E::ScalarField>,
        pub roots_of_unity_in_eval_dom: Vec<E::ScalarField>,
        pub g1: E::G1Affine,
        pub m_inv: E::ScalarField,
    }

    /// `setup_with_trapdoor(m, SrsType::Lagrange, ...)`. `lagr_g1` may be
    /// supplied from an on-disk cache (it's the only expensive part).
    pub fn setup_with_trapdoor<E: Pairing>(
        m: usize,
        g1: E::G1Affine,
        g2: E::G2Affine,
        xi: E::ScalarField,
        tau: E::ScalarField,
        lagr_g1: Option<Vec<E::G1Affine>>,
    ) -> (VerificationKey<E>, CommitmentKey<E>) {
        assert!(m.is_power_of_two());
        let (xi_1, tau_1) = ((g1 * xi).into_affine(), (g1 * tau).into_affine());
        let (xi_2, tau_2) = ((g2 * xi).into_affine(), (g2 * tau).into_affine());
        let eval_dom = Radix2EvaluationDomain::<E::ScalarField>::new(m).expect("eval domain");
        let lagr_g1 =
            lagr_g1.unwrap_or_else(|| lagrange_basis::<E::G1>(g1.into(), tau, m, eval_dom));
        assert_eq!(lagr_g1.len(), m);
        let roots_of_unity_in_eval_dom = eval_dom.elements().collect();
        let m_inv = E::ScalarField::from(m as u64).inverse().unwrap();
        (
            VerificationKey {
                xi_2,
                tau_2,
                g1,
                g2,
            },
            CommitmentKey {
                xi_1,
                tau_1,
                lagr_g1,
                eval_dom,
                roots_of_unity_in_eval_dom,
                g1,
                m_inv,
            },
        )
    }

    /// `CommitmentHomomorphism::apply` = MSM over [xi_1, lagr_0, lagr_1, ...].
    pub fn commit_with_randomness<E: Pairing>(
        ck: &CommitmentKey<E>,
        values: &[E::ScalarField],
        r: E::ScalarField,
    ) -> E::G1 {
        assert!(ck.lagr_g1.len() >= values.len());
        let mut scalars = Vec::with_capacity(values.len() + 1);
        scalars.push(r);
        scalars.extend_from_slice(values);
        let mut bases = Vec::with_capacity(values.len() + 1);
        bases.push(ck.xi_1);
        bases.extend_from_slice(&ck.lagr_g1[..values.len()]);
        E::G1::msm(&bases, &scalars).expect("KZG commit")
    }

    #[derive(Debug, Clone)]
    pub struct OpeningProofProjective<E: Pairing> {
        pub pi_1: E::G1,
        pub pi_2: E::G1,
    }

    #[derive(CanonicalSerialize, CanonicalDeserialize, Debug, Clone, PartialEq, Eq)]
    pub struct OpeningProof<E: Pairing> {
        pub pi_1: E::G1Affine,
        pub pi_2: E::G1Affine,
    }

    impl<E: Pairing> From<OpeningProofProjective<E>> for OpeningProof<E> {
        fn from(p: OpeningProofProjective<E>) -> Self {
            let n = E::G1::normalize_batch(&[p.pi_1, p.pi_2]);
            OpeningProof {
                pi_1: n[0],
                pi_2: n[1],
            }
        }
    }

    /// Lagrange-basis branch of `CommitmentHomomorphism::open` (offset = 0).
    pub fn open<E: Pairing>(
        ck: &CommitmentKey<E>,
        f_vals: Vec<E::ScalarField>,
        rho: E::ScalarField,
        x: E::ScalarField,
        y: E::ScalarField,
        s: E::ScalarField,
    ) -> OpeningProofProjective<E> {
        if ck.roots_of_unity_in_eval_dom.contains(&x) {
            panic!("x is not allowed to be a root of unity");
        }
        let q_vals =
            polynomials::quotient_evaluations_batch(&f_vals, &ck.roots_of_unity_in_eval_dom, x, y);
        let pi_1 = commit_with_randomness(ck, &q_vals, s);
        let pi_2 = (ck.g1 * rho) - (ck.tau_1 - ck.g1 * x) * s;
        OpeningProofProjective { pi_1, pi_2 }
    }

    #[allow(non_snake_case)]
    pub fn pairing_for_verify<E: Pairing>(
        vk: VerificationKey<E>,
        C: E::G1,
        x: E::ScalarField,
        y: E::ScalarField,
        pi: &OpeningProof<E>,
    ) -> (Vec<E::G1Affine>, Vec<E::G2Affine>) {
        let VerificationKey {
            xi_2,
            tau_2,
            g1: one_1,
            g2: one_2,
        } = vk;
        (
            E::G1::normalize_batch(&[C - one_1 * y, -pi.pi_1.into_group(), -pi.pi_2.into_group()]),
            vec![one_2, (tau_2 - one_2 * x).into_affine(), xi_2],
        )
    }
}

// ---------------------------------------------------------------------------
// Okamoto PoK: base_1 * x1 + base_2 * x2 (upstream `two_term_msm`)
// ---------------------------------------------------------------------------

pub mod two_term_msm {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct Homomorphism<E: Pairing> {
        pub base_1: E::G1Affine,
        pub base_2: E::G1Affine,
    }

    #[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Debug, PartialEq, Eq)]
    pub struct Proof<E: Pairing> {
        /// first prover message A (upstream stores `FirstProofItem::Commitment(A)`)
        pub a: E::G1Affine,
        /// z = (poly_randomness, hiding_kzg_randomness)
        pub z1: E::ScalarField,
        pub z2: E::ScalarField,
    }

    impl<E: Pairing> Homomorphism<E> {
        fn apply(&self, x1: E::ScalarField, x2: E::ScalarField) -> E::G1 {
            // upstream: "Not doing msm because E::G1::msm is slower!"
            self.base_1 * x1 + self.base_2 * x2
        }

        pub fn prove<R: RngCore + CryptoRng>(
            &self,
            w1: E::ScalarField,
            w2: E::ScalarField,
            statement: E::G1,
            rng: &mut R,
        ) -> Proof<E> {
            let r1: E::ScalarField = sample_field_element(rng);
            let r2: E::ScalarField = sample_field_element(rng);
            let a_proj = self.apply(r1, r2);
            let norm = E::G1::normalize_batch(&[a_proj, statement]);
            let (a, st) = (norm[0], norm[1]);
            let c = fiat_shamir::sigma_challenge::<E>(self, &st, &a);
            Proof {
                a,
                z1: r1 + c * w1,
                z2: r2 + c * w2,
            }
        }

        pub fn verify(
            &self,
            statement: &E::G1Affine,
            proof: &Proof<E>,
        ) -> Result<(), &'static str> {
            let c = fiat_shamir::sigma_challenge::<E>(self, statement, &proof.a);
            let bases = [self.base_1, self.base_2, proof.a, *statement];
            let scalars = [proof.z1, proof.z2, -E::ScalarField::ONE, -c];
            let r = E::G1::msm(&bases, &scalars).map_err(|_| "msm length")?;
            if r.is_zero() {
                Ok(())
            } else {
                Err("sigma protocol verification failed")
            }
        }
    }
}

// ---------------------------------------------------------------------------
// DeKART univariate v2
// ---------------------------------------------------------------------------

#[allow(non_snake_case)]
#[derive(CanonicalSerialize, CanonicalDeserialize, Debug, Clone, PartialEq, Eq)]
pub struct Proof<E: Pairing> {
    hat_C: E::G1Affine,
    pi_PoK: two_term_msm::Proof<E>,
    Cs: Vec<E::G1Affine>,
    D: E::G1Affine,
    a: E::ScalarField,
    a_h: E::ScalarField,
    a_js: Vec<E::ScalarField>,
    pi_gamma: hkzg::OpeningProof<E>,
}

#[allow(non_snake_case)]
pub struct ProofProjective<E: Pairing> {
    hat_C: E::G1Affine,
    pi_PoK: two_term_msm::Proof<E>,
    Cs: Vec<E::G1Affine>,
    D: E::G1Affine,
    a: E::ScalarField,
    a_h: E::ScalarField,
    a_js: Vec<E::ScalarField>,
    pi_gamma: hkzg::OpeningProofProjective<E>,
}

impl<E: Pairing> From<ProofProjective<E>> for Proof<E> {
    fn from(p: ProofProjective<E>) -> Self {
        Self {
            hat_C: p.hat_C,
            pi_PoK: p.pi_PoK,
            Cs: p.Cs,
            D: p.D,
            a: p.a,
            a_h: p.a_h,
            a_js: p.a_js,
            pi_gamma: p.pi_gamma.into(),
        }
    }
}

pub struct ProverKey<E: Pairing> {
    pub vk: VerificationKey<E>,
    pub ck_s: hkzg::CommitmentKey<E>,
    pub max_n: usize,
    powers_of_two: Vec<E::ScalarField>,
    h_denom_eval: Vec<E::ScalarField>,
}

#[derive(Clone, Debug)]
pub struct VerificationKey<E: Pairing> {
    xi_1: E::G1Affine,
    lagr_0: E::G1Affine,
    vk_hkzg: hkzg::VerificationKey<E>,
    powers_of_two: Vec<E::ScalarField>,
    roots_of_unity: Vec<E::ScalarField>,
}

fn compute_h_denom_eval<E: Pairing>(roots: &[E::ScalarField]) -> Vec<E::ScalarField> {
    let num_omegas = roots.len();
    assert!(
        num_omegas >= 2,
        "num_omegas must be at least 2 (max_n >= 1)"
    );
    let mut h_denom_eval = Vec::with_capacity(num_omegas);
    h_denom_eval.push(
        E::ScalarField::from(((num_omegas - 1) * num_omegas / 2) as u64)
            .inverse()
            .expect("Value should be invertible"),
    );
    h_denom_eval.extend(roots.iter().skip(1).map(|&root| {
        (root * (root - E::ScalarField::ONE)) / E::ScalarField::from(num_omegas as u64)
    }));
    h_denom_eval
}

/// `setup_for_testing(max_n, max_ell, GroupGenerators::default(), rng)`.
/// `lagr_g1` lets the bench harness feed a cached Lagrange SRS; when it is
/// `Some`, `(xi, tau)` must be the trapdoor it was built from.
#[allow(non_snake_case)]
pub fn setup_for_testing<E: Pairing>(
    max_n: usize,
    max_ell: usize,
    xi: E::ScalarField,
    tau: E::ScalarField,
    lagr_g1: Option<Vec<E::G1Affine>>,
) -> (ProverKey<E>, VerificationKey<E>) {
    let num_omegas = max_n + 1;
    assert!(num_omegas.is_power_of_two());
    let g1 = E::G1Affine::generator();
    let g2 = E::G2Affine::generator();
    let (vk_hkzg, ck_s) = hkzg::setup_with_trapdoor::<E>(num_omegas, g1, g2, xi, tau, lagr_g1);
    let h_denom_eval = compute_h_denom_eval::<E>(&ck_s.roots_of_unity_in_eval_dom);
    let powers_of_two = powers_of_two::<E::ScalarField>(max_ell);
    let vk = VerificationKey {
        xi_1: ck_s.xi_1,
        lagr_0: ck_s.lagr_g1[0],
        vk_hkzg,
        powers_of_two: powers_of_two.clone(),
        roots_of_unity: ck_s.roots_of_unity_in_eval_dom.clone(),
    };
    let pk = ProverKey {
        vk: vk.clone(),
        ck_s,
        max_n,
        powers_of_two,
        h_denom_eval,
    };
    (pk, vk)
}

/// Commits to `[0, values...]` in the Lagrange basis with hiding randomness `rho`.
pub fn commit_with_randomness<E: Pairing>(
    ck_s: &hkzg::CommitmentKey<E>,
    values: &[E::ScalarField],
    rho: E::ScalarField,
) -> E::G1 {
    let mut values_shifted = vec![E::ScalarField::ZERO];
    values_shifted.extend(values);
    hkzg::commit_with_randomness(ck_s, &values_shifted, rho)
}

#[allow(non_snake_case)]
pub fn prove<E: Pairing, R: RngCore + CryptoRng>(
    pk: &ProverKey<E>,
    values: &[E::ScalarField],
    ell: usize,
    comm: &E::G1Affine,
    rho: E::ScalarField,
    rng: &mut R,
) -> ProofProjective<E> {
    let comm_g1 = comm.into_group();
    let mut fs_t = Transcript::new(DST);

    // Step 1a
    let ProverKey {
        vk,
        ck_s,
        max_n,
        powers_of_two,
        h_denom_eval,
    } = pk;
    let n = values.len();
    let max_ell = powers_of_two.len();
    assert!(
        n <= *max_n,
        "n (got {n}) must be ≤ max_n (which is {max_n})"
    );
    assert!(
        ell <= max_ell,
        "ell (got {ell}) must be ≤ max_ell (which is {max_ell})"
    );
    let num_omegas = max_n + 1;
    let hkzg::CommitmentKey {
        xi_1,
        lagr_g1,
        eval_dom,
        m_inv: num_omegas_inv,
        ..
    } = ck_s;

    // Step 1b
    fiat_shamir::append_initial_data(&mut fs_t, vk, n, ell, comm);

    // Step 2a
    let r: E::ScalarField = sample_field_element(rng);
    let delta_rho: E::ScalarField = sample_field_element(rng);
    let hatC_proj: E::G1 = *xi_1 * delta_rho + lagr_g1[0] * r + comm_g1;
    let hat_C = hatC_proj.into_affine();

    // Step 2b
    fiat_shamir::append_hat_f_commitment::<E>(&mut fs_t, &hat_C);

    // Step 3a
    let pi_PoK = two_term_msm::Homomorphism::<E> {
        base_1: lagr_g1[0],
        base_2: *xi_1,
    }
    .prove(r, delta_rho, hatC_proj - comm_g1, rng);

    // Step 3b
    fiat_shamir::append_sigma_proof::<E>(&mut fs_t, &pi_PoK);

    // Step 4a
    let bits = scalars_to_bits::scalars_to_bits_le(values, ell);
    let f_j_evals_without_r = scalars_to_bits::transpose_bit_matrix(&bits);
    let rs: Vec<E::ScalarField> = sample_field_elements(ell, rng);
    let f_js_evals: Vec<Vec<E::ScalarField>> = f_j_evals_without_r
        .iter()
        .enumerate()
        .map(|(j, col)| {
            let mut evals: Vec<E::ScalarField> = vec![rs[j]];
            evals.extend(col.iter().map(|&b| E::ScalarField::from(b)));
            evals.resize(num_omegas, E::ScalarField::ZERO);
            evals
        })
        .collect();
    let rhos: Vec<E::ScalarField> = sample_field_elements(ell, rng);
    let Cs_proj: Vec<E::G1> = f_js_evals
        .iter()
        .zip(rhos.iter())
        .enumerate()
        .map(|(j, (f_j_evals, &rho))| {
            let bits = &f_j_evals_without_r[j];
            let sum = lagr_g1[0] * f_j_evals[0] + msm_bool(&lagr_g1[1..(1 + n)], bits);
            *xi_1 * rho + sum
        })
        .collect();

    // Step 4b
    let Cs = E::G1::normalize_batch(&Cs_proj);
    fiat_shamir::append_f_j_commitments::<E>(&mut fs_t, &Cs);

    // Step 6
    let (beta, betas) = fiat_shamir::get_beta_challenges::<E>(&mut fs_t, ell);

    let hat_f_evals: Vec<E::ScalarField> = {
        let mut v = Vec::with_capacity(num_omegas);
        v.push(r);
        v.extend_from_slice(values);
        v.resize(num_omegas, E::ScalarField::ZERO);
        v
    };
    let hat_f_coeffs = eval_dom.ifft(&hat_f_evals);
    let diff_hat_f_evals: Vec<E::ScalarField> = {
        let mut result = polynomials::differentiate(&hat_f_coeffs);
        eval_dom.fft_in_place(&mut result);
        result
    };
    let f_j_coeffs: Vec<Vec<E::ScalarField>> = (0..ell)
        .map(|j| {
            let mut f_j = f_js_evals[j].clone();
            eval_dom.ifft_in_place(&mut f_j);
            f_j
        })
        .collect();
    let diff_f_js_evals: Vec<Vec<E::ScalarField>> = f_js_evals
        .iter()
        .map(|f_j_eval| {
            let mut result = eval_dom.ifft(f_j_eval);
            polynomials::differentiate_in_place(&mut result);
            eval_dom.fft_in_place(&mut result);
            result
        })
        .collect();

    let h_evals: Vec<E::ScalarField> = {
        let two = E::ScalarField::from(2u64);
        let first_h_eval = {
            let mut pow2 = E::ScalarField::ONE;
            let mut sum_pow2_rs = E::ScalarField::ZERO;
            for r_j in &rs {
                sum_pow2_rs += pow2 * r_j;
                pow2 = pow2.double();
            }
            let sum_betas_term: E::ScalarField = betas
                .iter()
                .zip(&rs)
                .map(|(&beta_j, r_j)| beta_j * r_j * (*r_j - E::ScalarField::ONE))
                .sum();
            let numerator = beta * (r - sum_pow2_rs) + sum_betas_term;
            numerator * num_omegas_inv
        };
        let mut result = Vec::with_capacity(num_omegas);
        result.push(first_h_eval);
        for i in 1..num_omegas {
            result.push(beta * diff_hat_f_evals[i]);
        }
        for j in 0..ell {
            let diff_f_j = &diff_f_js_evals[j];
            let f_j = &f_js_evals[j];
            let coeff1 = beta * powers_of_two[j];
            let beta_j = betas[j];
            for i in 1..num_omegas {
                let d = diff_f_j[i];
                result[i] -= coeff1 * d;
                result[i] += beta_j * d * (two * f_j[i] - E::ScalarField::ONE);
            }
        }
        for i in 1..num_omegas {
            result[i] *= h_denom_eval[i];
        }
        result
    };

    // Step 7
    let rho_h: E::ScalarField = sample_field_element(rng);
    let D = hkzg::commit_with_randomness(ck_s, &h_evals, rho_h).into_affine();
    fiat_shamir::append_h_commitment::<E>(&mut fs_t, &D);

    // Step 8
    let gamma = fiat_shamir::get_gamma_challenge::<E>(&mut fs_t, &ck_s.roots_of_unity_in_eval_dom);

    // Step 9a
    let a = ark_poly::univariate::DensePolynomial {
        coeffs: hat_f_coeffs,
    }
    .evaluate(&gamma);
    let a_h = polynomials::barycentric_eval(
        &h_evals,
        &ck_s.roots_of_unity_in_eval_dom,
        gamma,
        *num_omegas_inv,
    );
    let a_js: Vec<E::ScalarField> = (0..ell)
        .map(|i| {
            ark_poly::univariate::DensePolynomial {
                coeffs: f_j_coeffs[i].clone(),
            }
            .evaluate(&gamma)
        })
        .collect();

    // Step 9b, 9c
    fiat_shamir::append_evaluations_at_gamma::<E>(&mut fs_t, a, a_h, &a_js);
    let (mu, mu_h, mus) = fiat_shamir::get_mu_challenges::<E>(&mut fs_t, ell);

    // Step 10
    let u_values: Vec<_> = (0..num_omegas)
        .map(|i| {
            mu * hat_f_evals[i]
                + mu_h * h_evals[i]
                + mus
                    .iter()
                    .zip(&f_js_evals)
                    .map(|(&mu_j, f_j)| mu_j * f_j[i])
                    .sum::<E::ScalarField>()
        })
        .collect();
    let s: E::ScalarField = sample_field_element(rng);
    let rho_u = mu * (rho + delta_rho)
        + mu_h * rho_h
        + mus
            .iter()
            .zip(&rhos)
            .map(|(&mu_j, &rho_j)| mu_j * rho_j)
            .sum::<E::ScalarField>();
    let u_val = polynomials::barycentric_eval(
        &u_values,
        &ck_s.roots_of_unity_in_eval_dom,
        gamma,
        *num_omegas_inv,
    );
    let pi_gamma = hkzg::open(ck_s, u_values, rho_u, gamma, u_val, s);

    ProofProjective {
        hat_C,
        pi_PoK,
        Cs,
        D,
        a,
        a_h,
        a_js,
        pi_gamma,
    }
}

impl<E: Pairing> Proof<E> {
    #[allow(non_snake_case)]
    pub fn pairing_for_verify(
        &self,
        vk: &VerificationKey<E>,
        n: usize,
        ell: usize,
        comm: &E::G1Affine,
    ) -> Result<(Vec<E::G1Affine>, Vec<E::G2Affine>), &'static str> {
        let mut fs_t = Transcript::new(DST);

        // Step 1
        let VerificationKey {
            xi_1,
            lagr_0,
            vk_hkzg,
            powers_of_two,
            roots_of_unity,
        } = vk;
        if ell > powers_of_two.len() || n > roots_of_unity.len().saturating_sub(1) {
            return Err("n/ell out of range");
        }
        let Proof {
            hat_C,
            pi_PoK,
            Cs,
            D,
            a,
            a_h,
            a_js,
            pi_gamma,
        } = self;
        if Cs.len() != ell || a_js.len() != ell {
            return Err("Cs / a_js length must equal ell");
        }

        // Step 2
        fiat_shamir::append_initial_data(&mut fs_t, vk, n, ell, comm);
        fiat_shamir::append_hat_f_commitment::<E>(&mut fs_t, hat_C);

        // Step 3
        two_term_msm::Homomorphism::<E> {
            base_1: *lagr_0,
            base_2: *xi_1,
        }
        .verify(&(*hat_C - *comm).into_affine(), pi_PoK)?;

        // Steps 4a–9
        fiat_shamir::append_sigma_proof::<E>(&mut fs_t, pi_PoK);
        fiat_shamir::append_f_j_commitments::<E>(&mut fs_t, Cs);
        let (beta, beta_js) = fiat_shamir::get_beta_challenges::<E>(&mut fs_t, ell);
        fiat_shamir::append_h_commitment::<E>(&mut fs_t, D);
        let gamma = fiat_shamir::get_gamma_challenge::<E>(&mut fs_t, roots_of_unity);
        fiat_shamir::append_evaluations_at_gamma::<E>(&mut fs_t, *a, *a_h, a_js);
        let (mu, mu_h, mu_js) = fiat_shamir::get_mu_challenges::<E>(&mut fs_t, ell);

        // Step 10
        let mut U_bases = Vec::with_capacity(2 + Cs.len());
        U_bases.push(*hat_C);
        U_bases.push(*D);
        U_bases.extend_from_slice(Cs);
        let mut U_scalars = Vec::with_capacity(2 + mu_js.len());
        U_scalars.push(mu);
        U_scalars.push(mu_h);
        U_scalars.extend_from_slice(&mu_js);
        let U = E::G1::msm(&U_bases, &U_scalars).map_err(|_| "U msm length mismatch")?;
        let a_u = *a * mu
            + *a_h * mu_h
            + a_js
                .iter()
                .zip(&mu_js)
                .map(|(&a_j, &mu_j)| a_j * mu_j)
                .sum::<E::ScalarField>();

        // Step 11
        let num_omegas = roots_of_unity.len();
        let LHS = {
            let denom = (gamma - E::ScalarField::ONE)
                .inverse()
                .ok_or("gamma must not be 1")?;
            let V_eval_gamma = (gamma.pow([num_omegas as u64]) - E::ScalarField::ONE) * denom;
            *a_h * V_eval_gamma
        };
        let RHS = {
            let sum1: E::ScalarField = powers_of_two
                .iter()
                .zip(a_js.iter())
                .map(|(&p, aj)| p * aj)
                .sum();
            let sum2: E::ScalarField = beta_js
                .iter()
                .zip(a_js.iter())
                .map(|(b, &a)| a * (a - E::ScalarField::ONE) * b)
                .sum();
            beta * (*a - sum1) + sum2
        };
        if LHS != RHS {
            return Err("DeKART quotient check failed");
        }

        Ok(hkzg::pairing_for_verify(*vk_hkzg, U, gamma, a_u, pi_gamma))
    }

    /// `BatchedRangeProof::verify`: `pairing_for_verify` + one multi-pairing.
    pub fn verify(
        &self,
        vk: &VerificationKey<E>,
        n: usize,
        ell: usize,
        comm: &E::G1Affine,
    ) -> Result<(), &'static str> {
        let (g1, g2) = self.pairing_for_verify(vk, n, ell, comm)?;
        if PairingOutput::<E>::ZERO == E::multi_pairing(g1, g2) {
            Ok(())
        } else {
            Err("hiding KZG pairing check failed")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::{Bls12_381, Fr, G1Projective};
    use ark_ec::PrimeGroup;
    use ark_std::rand::{SeedableRng, rngs::StdRng};

    fn roundtrip(n: usize, ell: usize) {
        let mut rng = StdRng::seed_from_u64(42);
        let xi: Fr = sample_field_element(&mut rng);
        let tau: Fr = sample_field_element(&mut rng);
        let (pk, vk) = setup_for_testing::<Bls12_381>(n, ell, xi, tau, None);
        let values: Vec<Fr> = (0..n)
            .map(|_| Fr::from(rng.next_u64() >> (64 - ell)))
            .collect();
        let rho: Fr = sample_field_element(&mut rng);
        let comm = commit_with_randomness(&pk.ck_s, &values, rho).into_affine();
        let proof: Proof<Bls12_381> = prove(&pk, &values, ell, &comm, rho, &mut rng).into();
        proof
            .verify(&vk, n, ell, &comm)
            .expect("valid proof should verify");

        // Out-of-range value must be rejected.
        let mut bad = values.clone();
        bad[0] = Fr::from(1u64 << ell);
        let comm_bad = commit_with_randomness(&pk.ck_s, &bad, rho).into_affine();
        let proof_bad: Proof<Bls12_381> = prove(&pk, &bad, ell, &comm_bad, rho, &mut rng).into();
        assert!(proof_bad.verify(&vk, n, ell, &comm_bad).is_err());

        // Mauled proof must be rejected (upstream's `maul`).
        let mut mauled = proof.clone();
        mauled.D = (mauled.D + G1Projective::generator()).into_affine();
        assert!(mauled.verify(&vk, n, ell, &comm).is_err());
    }

    #[test]
    fn dekart_roundtrip_small() {
        roundtrip(3, 8);
        roundtrip(15, 16);
        roundtrip(255, 32);
    }
}
