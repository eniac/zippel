//! Vendored `ark-poly-commit-0.6.0::hyrax` with the matrix-vector
//! multiplication implementation fixed for the native baseline.
//!
//! The upstream `Matrix::row_mul` is the hot path of `open`. It computes
//! `lt[col] = Σ_row v[row] * mat[row][col]` over a (1<<n/2) × (1<<n/2)
//! coefficient matrix. The reference implementation is:
//!
//! ```ignore
//! cfg_into_iter!(0..self.m).map(|col| {
//!     inner_product(v, &cfg_into_iter!(0..self.n)
//!         .map(|row| self.entries[row][col])    // <-- per-row heap chase
//!         .collect::<Vec<F>>())                 // <-- per-column 16KB alloc
//! }).collect()
//! ```
//!
//! At n=18 (dim=512) this allocates 512 × 16KB = 8MB of temporary Vecs
//! per call and walks 262K cache-missing column gathers over a
//! `Vec<Vec<F>>` whose rows are scattered in heap memory. Combined with
//! nested `par_iter` overhead it costs ~8s at threads=1 even though the
//! actual field work is ~40ms.
//!
//! This module replaces it with two fixes:
//!
//! 1. **Flat row-major matrix storage**. `FlatMatrix.entries: Vec<F>`
//!    holds the coefficients in one contiguous allocation, indexed as
//!    `entries[row * m + col]`. Walking a row is a sequential memory
//!    sweep.
//!
//! 2. **SAXPY-pattern `row_mul`**. Stream rows in row-major order and
//!    accumulate into a thread-local output buffer:
//!    `for col { acc[col] += v[row] * row_slice[col] }`. No per-column
//!    allocations, fully sequential reads, single fold-reduce over
//!    rayon's pool.
//!
//! The Fiat-Shamir transcript byte sequence is identical to upstream
//! (same `serialize_to_vec!` calls in the same order), so the
//! cryptographic protocol is bit-for-bit unchanged — only the
//! implementation efficiency changes.
//!
//! `setup` is also byte-identical to upstream (same Blake2s256 seed
//! derivation, same `mul_by_cofactor_to_group`, same `normalize_batch`),
//! so on-disk `hyrax_universal_params_log{n}.bin` caches written by the
//! upstream code reload here without rebuild.

use ark_bls12_381::{Fr, G1Affine, G1Projective};
use ark_crypto_primitives::sponge::CryptographicSponge;
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{One, PrimeField, UniformRand, Zero};
use ark_poly::{DenseMultilinearExtension, MultilinearExtension};
use ark_poly_commit::hyrax::{HyraxCommitment, HyraxProof, HyraxUniversalParams};
use ark_serialize::serialize_to_vec;
use ark_std::rand::RngCore;
use blake2::{Blake2s256, Digest};
use rayon::prelude::*;

pub const PROTOCOL_NAME: &'static [u8] = b"Hyrax protocol";

pub type CommitterKey = HyraxUniversalParams<G1Affine>;
pub type VerifierKey = HyraxUniversalParams<G1Affine>;
pub type Commitment = HyraxCommitment<G1Affine>;
pub type Proof = HyraxProof<G1Affine>;

#[derive(Default, Clone)]
pub struct CommitmentState {
    pub randomness: Vec<Fr>,
    pub mat: FlatMatrix,
}

#[derive(Default, Clone)]
pub struct FlatMatrix {
    pub n: usize,
    pub m: usize,
    /// Row-major: `entries[row * m + col]`.
    pub entries: Vec<Fr>,
}

impl FlatMatrix {
    /// Returns `v^T · M` — a length-`m` vector where
    /// `out[col] = Σ_row v[row] * M[row][col]`.
    ///
    /// At threads > 1: each rayon task takes a strip of rows and
    /// SAXPYs them into a thread-local length-`m` accumulator; the
    /// inner loop reads one row sequentially and writes the
    /// accumulator sequentially, so memory traffic is cache-friendly.
    /// Final reduce sums the strip accumulators componentwise.
    ///
    /// At threads == 1: skip rayon entirely. The fold-reduce pattern
    /// still chunks at threads=1 and allocates a fresh `vec![Fr::zero(); m]`
    /// accumulator per chunk, then walks the queue overhead per task.
    /// On a 256-thread Xeon with `RAYON_NUM_THREADS=1` that overhead
    /// can balloon to ~6× the actual SAXPY work — the cost of going
    /// through rayon's scheduler when there's nothing to parallelize.
    pub fn row_mul(&self, v: &[Fr]) -> Vec<Fr> {
        assert_eq!(v.len(), self.n);
        let m = self.m;
        let entries = &self.entries;

        if rayon::current_num_threads() <= 1 {
            let mut acc = vec![Fr::zero(); m];
            for row in 0..self.n {
                let v_row = v[row];
                let row_slice = &entries[row * m..row * m + m];
                for col in 0..m {
                    acc[col] += v_row * row_slice[col];
                }
            }
            return acc;
        }

        (0..self.n)
            .into_par_iter()
            .fold(
                || vec![Fr::zero(); m],
                |mut acc, row| {
                    let v_row = v[row];
                    let row_slice = &entries[row * m..row * m + m];
                    for col in 0..m {
                        acc[col] += v_row * row_slice[col];
                    }
                    acc
                },
            )
            .reduce(
                || vec![Fr::zero(); m],
                |mut a, b| {
                    for col in 0..m {
                        a[col] += b[col];
                    }
                    a
                },
            )
    }
}

fn pedersen_commit(key: &[G1Affine], scalars: &[Fr]) -> G1Projective {
    assert_eq!(key.len(), scalars.len());
    // Avoid nested par_iter at threads=1 — the outer commit loop is
    // already a par_iter, and rayon's scheduler queues every nested
    // par_iter task even when there's no parallelism to gain.
    let scalars_bigint: Vec<_> = if rayon::current_num_threads() <= 1 {
        scalars.iter().map(|s| s.into_bigint()).collect()
    } else {
        scalars.par_iter().map(|s| s.into_bigint()).collect()
    };
    <G1Projective as VariableBaseMSM>::msm_bigint(key, &scalars_bigint)
}

/// Tensor product expansion of `EQ(·, values)`. Same algorithm as
/// upstream `hyrax::utils::tensor_prime`.
fn tensor_prime(values: &[Fr]) -> Vec<Fr> {
    if values.is_empty() {
        return vec![Fr::one()];
    }
    let tail = tensor_prime(&values[1..]);
    let val = values[0];
    tail.par_iter()
        .map(|v| *v * (Fr::one() - val))
        .chain(tail.par_iter().map(|v| *v * val))
        .collect()
}

fn inner_product(v1: &[Fr], v2: &[Fr]) -> Fr {
    v1.par_iter()
        .zip(v2.par_iter())
        .map(|(li, ri)| *li * ri)
        .sum()
}

/// Byte-identical reproduction of upstream `HyraxPC::setup`: derive
/// `dim+1` group points from `Blake2s256(PROTOCOL_NAME || i)`, push the
/// last as `h`. Cached on disk under `hyrax_universal_params_log{n}.bin`.
pub fn setup<R: RngCore>(num_vars: usize, _rng: &mut R) -> HyraxUniversalParams<G1Affine> {
    assert!(
        num_vars % 2 == 0,
        "Hyrax requires an even number of variables"
    );
    let dim = 1usize << (num_vars / 2);
    let points: Vec<G1Projective> = (0u64..(dim as u64 + 1))
        .into_par_iter()
        .map(|i| {
            let hash = Blake2s256::digest([PROTOCOL_NAME, &i.to_le_bytes()].concat().as_slice());
            let mut p = G1Affine::from_random_bytes(&hash);
            let mut j = 0u64;
            while p.is_none() {
                let mut bytes = PROTOCOL_NAME.to_vec();
                bytes.extend(i.to_le_bytes());
                bytes.extend(j.to_le_bytes());
                let hash = Blake2s256::digest(bytes.as_slice());
                p = G1Affine::from_random_bytes(&hash);
                j += 1;
            }
            p.unwrap().mul_by_cofactor_to_group()
        })
        .collect();
    let mut points = G1Projective::normalize_batch(&points);
    let h = points.pop().unwrap();
    HyraxUniversalParams { com_key: points, h }
}

pub fn trim(pp: &HyraxUniversalParams<G1Affine>) -> (CommitterKey, VerifierKey) {
    (pp.clone(), pp.clone())
}

/// Commit to a multilinear polynomial via row-wise Pedersen
/// commitments to its (1<<n/2) × (1<<n/2) evaluation matrix.
pub fn commit(
    ck: &CommitterKey,
    poly: &DenseMultilinearExtension<Fr>,
) -> (Commitment, CommitmentState) {
    let n = poly.num_vars();
    assert!(n % 2 == 0);
    let dim = 1usize << (n / 2);
    assert!(ck.com_key.len() >= dim);

    let evals = poly.to_evaluations();

    // Upstream stores the matrix column-major (mat[row][col] =
    // evals[col * dim + row]) using `flat_to_matrix_column_major`. We
    // store row-major in a flat Vec instead. Same logical matrix —
    // just the physical layout that lets `row_mul` stream rows
    // sequentially.
    let mut entries = vec![Fr::zero(); dim * dim];
    if rayon::current_num_threads() <= 1 {
        for row in 0..dim {
            let row_slice = &mut entries[row * dim..row * dim + dim];
            for col in 0..dim {
                row_slice[col] = evals[col * dim + row];
            }
        }
    } else {
        entries
            .par_chunks_mut(dim)
            .enumerate()
            .for_each(|(row, row_slice)| {
                for col in 0..dim {
                    row_slice[col] = evals[col * dim + row];
                }
            });
    }
    let mat = FlatMatrix {
        n: dim,
        m: dim,
        entries,
    };

    // Outer row loop: serial at threads=1 (rayon scheduler overhead per
    // task dominates the actual MSM work on big-core counts), par_iter
    // at threads>1.
    let (row_coms, com_rands): (Vec<G1Affine>, Vec<Fr>) = if rayon::current_num_threads() <= 1 {
        let mut rng = rand::thread_rng();
        (0..dim)
            .map(|row| {
                let r = Fr::rand(&mut rng);
                let row_slice = &mat.entries[row * dim..row * dim + dim];
                let c = (pedersen_commit(&ck.com_key, row_slice) + ck.h * r).into_affine();
                (c, r)
            })
            .unzip()
    } else {
        (0..dim)
            .into_par_iter()
            .map(|row| {
                let mut rng = rand::thread_rng();
                let r = Fr::rand(&mut rng);
                let row_slice = &mat.entries[row * dim..row * dim + dim];
                let c = (pedersen_commit(&ck.com_key, row_slice) + ck.h * r).into_affine();
                (c, r)
            })
            .unzip()
    };

    let com = HyraxCommitment { row_coms };
    let state = CommitmentState {
        randomness: com_rands,
        mat,
    };
    (com, state)
}

/// Open the commitment at `point`. Returns the σ-protocol proof.
/// Mirrors upstream `HyraxPC::open` line-for-line — only the
/// `state.mat.row_mul(&l)` call is the fast path.
pub fn open(
    ck: &CommitterKey,
    com: &Commitment,
    point: &[Fr],
    sponge: &mut impl CryptographicSponge,
    state: &CommitmentState,
) -> Proof {
    let n = point.len();
    assert!(n % 2 == 0);
    let dim = 1usize << (n / 2);

    let point_rev: Vec<Fr> = point.iter().rev().cloned().collect();
    let point_lower = &point_rev[n / 2..];
    let point_upper = &point_rev[..n / 2];
    let l = tensor_prime(point_lower);
    let r = tensor_prime(point_upper);

    let point_vec: Vec<Fr> = point.to_vec();
    sponge.absorb(&serialize_to_vec!(*ck).expect("serialize ck"));
    sponge.absorb(&serialize_to_vec!(com.row_coms).expect("serialize row_coms"));
    sponge.absorb(&point_vec);

    let lt = state.mat.row_mul(&l);
    let r_lt: Fr = l
        .par_iter()
        .zip(&state.randomness)
        .map(|(l, r)| *l * r)
        .sum();
    let eval = inner_product(&lt, &r);

    let mut rng = rand::thread_rng();
    let r_eval = Fr::rand(&mut rng);
    let com_eval = (ck.com_key[0] * eval + ck.h * r_eval).into_affine();

    let d: Vec<Fr> = (0..dim).map(|_| Fr::rand(&mut rng)).collect();
    let b = inner_product(&r, &d);

    let r_d = Fr::rand(&mut rng);
    let com_d = (pedersen_commit(&ck.com_key, &d) + ck.h * r_d).into_affine();

    let r_b = Fr::rand(&mut rng);
    let com_b = (ck.com_key[0] * b + ck.h * r_b).into_affine();

    sponge.absorb(&serialize_to_vec!(com_eval).expect("serialize com_eval"));
    sponge.absorb(&serialize_to_vec!(com_d).expect("serialize com_d"));
    sponge.absorb(&serialize_to_vec!(com_b).expect("serialize com_b"));

    let c: Fr = sponge.squeeze_field_elements(1)[0];

    let z: Vec<Fr> = d
        .par_iter()
        .zip(lt.par_iter())
        .map(|(d, lt)| *d + c * lt)
        .collect();
    let z_d = c * r_lt + r_d;
    let z_b = c * r_eval + r_b;

    HyraxProof {
        com_eval,
        com_d,
        com_b,
        z,
        z_d,
        z_b,
    }
}

/// Verify a σ-protocol opening. Identical algebra and absorb sequence
/// to upstream `HyraxPC::check`.
pub fn check(
    vk: &VerifierKey,
    com: &Commitment,
    point: &[Fr],
    proof: &Proof,
    sponge: &mut impl CryptographicSponge,
) -> bool {
    let n = point.len();
    assert!(n % 2 == 0);

    let point_rev: Vec<Fr> = point.iter().rev().cloned().collect();
    let point_lower = &point_rev[n / 2..];
    let point_upper = &point_rev[..n / 2];
    let l = tensor_prime(point_lower);
    let r = tensor_prime(point_upper);

    let row_coms = &com.row_coms;
    if row_coms.len() != 1usize << (n / 2) {
        return false;
    }

    let point_vec: Vec<Fr> = point.to_vec();
    sponge.absorb(&serialize_to_vec!(*vk).expect("serialize vk"));
    sponge.absorb(&serialize_to_vec!(*row_coms).expect("serialize row_coms"));
    sponge.absorb(&point_vec);
    sponge.absorb(&serialize_to_vec!(proof.com_eval).expect("serialize com_eval"));
    sponge.absorb(&serialize_to_vec!(proof.com_d).expect("serialize com_d"));
    sponge.absorb(&serialize_to_vec!(proof.com_b).expect("serialize com_b"));

    let c: Fr = sponge.squeeze_field_elements(1)[0];

    let com_dp =
        (vk.com_key[0] * inner_product(&r, &proof.z) + vk.h * proof.z_b).into_affine();
    if com_dp != (proof.com_eval.into_group() * c + proof.com_b).into_affine() {
        return false;
    }

    let l_bigint: Vec<_> = l.par_iter().map(|x| x.into_bigint()).collect();
    let t_prime = <G1Projective as VariableBaseMSM>::msm_bigint(row_coms, &l_bigint).into_affine();
    let com_z_zd = (pedersen_commit(&vk.com_key, &proof.z) + vk.h * proof.z_d).into_affine();
    if com_z_zd != (t_prime.into_group() * c + proof.com_d).into_affine() {
        return false;
    }

    true
}
