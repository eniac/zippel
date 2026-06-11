//! PST13 multilinear polynomial commitment comparison: zippel-compiled
//! `examples/pst13/pst13.zippel` vs. a hand-written native PST13 baseline,
//! both on git-main BLS12-381.
//!
//! Statement on both sides: prover knows multilinear polynomial p with 2^N
//! coefficients; commits to it, then proves p̃(z) = y at the challenge point z.
//!
//! Parity decisions:
//!   - Both sides time **commit + open** as "prove" (zippel does
//!     `c_p <- pst13_commit(p, ck)` inside the proto body — the native
//!     `prove()` mirrors that ordering).
//!   - Both verifiers compute a single fused `multi_pairing` over [(c_p − y·g),
//!     (−π_i)_i] × [h, (α_h_i − z_i·h)_i] — the same path the zippel proto
//!     hits via `dot(VecG1, VecG2) → GT`.
//!   - The commitment-key SRS (`ck`, length 2^N) is `public` in the proto
//!     so the verifier graph sees it. PST13's verifier doesn't actually
//!     touch `ck` (only α_H matters), so this contributes O(2^N) bytes
//!     of FS absorption to zippel verify time. We document the cost
//!     rather than hide it; PST13's "real" verifier is O(N) and the gap
//!     is purely the runtime's FS-absorption model.
//!
//! Sweep knob: `n = log_2(poly_size)`. Helpers cap at K = 20.

use crate::Timing;

pub const DEFAULT_N: usize = 10;

// ---------------------------------------------------------------------------
// Shared inputs: one PST13 setup + one (p, z, y) pair, fed to both sides.
// ---------------------------------------------------------------------------

pub mod shared {
    use ark_bls12_381::{Fr, G1Projective, G2Projective};
    use ark_ec::CurveGroup;
    use ark_ff::{One, Zero};
    use ark_std::UniformRand;
    use ark_std::rand::SeedableRng;

    pub struct Shared {
        pub n: usize,
        pub g_gen: G1Projective,
        pub h_gen: G2Projective,
        pub alpha: Vec<Fr>,
        /// ck[i] = eq_N(α, i) · g_gen for i ∈ {0, 1}^N, MSB-first indexing
        /// (bit `n-1-j` of `i` is the value of variable j).
        pub ck: Vec<G1Projective>,
        /// Affine view of `ck` — avoids per-prove `normalize_batch` like in
        /// the Groth16 bench fix.
        pub ck_affine: Vec<ark_bls12_381::G1Affine>,
        pub alpha_h: Vec<G2Projective>,
        pub p: Vec<Fr>,
        pub z: Vec<Fr>,
        pub y: Fr,
    }

    /// Seeded build so multiple calls at the same `n` produce identical data,
    /// matching how Groth16/KZG benches reseed inside `Setup::new`.
    pub fn build(n: usize) -> Shared {
        assert!((1..=20).contains(&n), "n must be in 1..=20");
        let size = 1usize << n;

        // Distinct seed per n so successive sweep rows don't share state.
        let mut seed_bytes = [0u8; 32];
        seed_bytes[..8].copy_from_slice(&(0xC0FFEE_u64 ^ n as u64).to_le_bytes());
        let mut rng = ark_std::rand::rngs::StdRng::from_seed(seed_bytes);

        let g_gen = G1Projective::rand(&mut rng);
        let h_gen = G2Projective::rand(&mut rng);

        let one = Fr::one();
        let alpha: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
        let one_m_alpha: Vec<Fr> = alpha.iter().map(|a| one - *a).collect();

        // ck[i] = Π_j L_j(b_j) · g_gen, b = MSB-first bits of i.
        let ck_scalars: Vec<Fr> = (0..size)
            .map(|i| {
                (0..n).fold(one, |acc, j| {
                    let bit = (i >> (n - 1 - j)) & 1;
                    if bit == 1 {
                        acc * alpha[j]
                    } else {
                        acc * one_m_alpha[j]
                    }
                })
            })
            .collect();
        let ck: Vec<G1Projective> = ck_scalars.iter().map(|s| g_gen * s).collect();
        let ck_affine = G1Projective::normalize_batch(&ck);

        let alpha_h: Vec<G2Projective> = alpha.iter().map(|a| h_gen * a).collect();

        let p: Vec<Fr> = (0..size).map(|_| Fr::rand(&mut rng)).collect();
        let z: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();

        // y = p̃(z) = Σ_i p_i · eq_N(z, i), same bit order as ck.
        let y: Fr = (0..size)
            .map(|i| {
                let eq_z_i = (0..n).fold(one, |prod, j| {
                    let bit = (i >> (n - 1 - j)) & 1;
                    if bit == 1 {
                        prod * z[j]
                    } else {
                        prod * (one - z[j])
                    }
                });
                p[i] * eq_z_i
            })
            .fold(Fr::zero(), |acc, v| acc + v);

        Shared {
            n,
            g_gen,
            h_gen,
            alpha,
            ck,
            ck_affine,
            alpha_h,
            p,
            z,
            y,
        }
    }
}

// ---------------------------------------------------------------------------
// Native PST13 baseline: EspressoSystems/hyperplonk's `MultilinearKzgPCS`.
//
// "Multilinear KZG" in hyperplonk terminology is exactly PST13 — same algorithm
// (Lagrange-basis ck, per-variable quotient commitments, pairing-equation check).
// Using a published, well-tested implementation here puts the PST13 native
// baseline on the same footing as KZG (vs `ark-poly-commit::kzg10`) and Groth16
// (vs `ark-groth16`).
//
// Hyperplonk pins arkworks v0.4, so we go through the `hp-ark-*` rename in
// `Cargo.toml`. The `Shared` inputs (g_gen, ck, etc.) are zippel-side; the
// hyperplonk side does its own SRS setup via `gen_srs_for_testing` and runs
// against an internally-generated `DenseMultilinearExtension` of the same size.
// Performance comparison only — no cross-side byte equality.
// ---------------------------------------------------------------------------

/// Native PST13 baseline: `ark_poly_commit::multilinear_pc::MultilinearPC`
/// (0.6 from crates.io, same arkworks set the zippel side uses — so
/// MSM/pairing primitives are bit-identical on both sides). Replaces the
/// previous hyperplonk `MultilinearKzgPCS` baseline that was locked at
/// arkworks 0.4. Same setup/commit/open/check shape — only API rename:
/// `gen_srs_for_testing` → `setup`, `verify` → `check`, `open` no longer
/// returns `value` so we evaluate the MLE inside the prove timer (which
/// is correct — the prover has to compute it to build the proof).
pub mod native_side {
    use super::Timing;
    use super::shared::Shared;
    use ark_bls12_381::{Bls12_381, Fr};
    use ark_ff::UniformRand;
    use ark_poly::{DenseMultilinearExtension, MultilinearExtension, Polynomial};
    use ark_poly_commit::multilinear_pc::{
        data_structures::{CommitterKey, VerifierKey},
        MultilinearPC,
    };
    use ark_std::rand::SeedableRng;
    use std::time::Instant;

    type Pcs = MultilinearPC<Bls12_381>;

    pub struct Setup {
        n: usize,
        ck: CommitterKey<Bls12_381>,
        vk: VerifierKey<Bls12_381>,
    }

    impl Setup {
        /// Takes `&Shared` only to read `n` — the native side generates its
        /// own SRS + polynomial + point internally. Both sides run the
        /// same protocol on a random size-2^n MLE; only the wall-clock
        /// matters for the comparison.
        pub fn new(shared: &Shared) -> Self {
            let n = shared.n;
            // Cache UniversalParams — the heavy setup at n=20. Re-trim
            // per call (cheap slice over cached params). Seed is fixed
            // per `n` so the cache key is well-defined.
            let pp = crate::cache::load_or_build_canonical::<
                ark_poly_commit::multilinear_pc::data_structures::UniversalParams<Bls12_381>,
            >("pst13_universal_params", n, || {
                let mut seed_bytes = [0u8; 32];
                seed_bytes[..8].copy_from_slice(&(0xC0FFEE_u64 ^ n as u64).to_le_bytes());
                let mut rng = ark_std::rand::rngs::StdRng::from_seed(seed_bytes);
                Pcs::setup(n, &mut rng)
            });
            let (ck, vk) = Pcs::trim(&pp, n);

            Setup { n, ck, vk }
        }

        pub fn time_protocol(&self) -> Timing {
            // Re-seed for the per-call poly/point so timing is reproducible.
            let mut seed_bytes = [0u8; 32];
            seed_bytes[..8].copy_from_slice(&(0xDEC0DE_u64 ^ self.n as u64).to_le_bytes());
            let mut rng = ark_std::rand::rngs::StdRng::from_seed(seed_bytes);

            let poly = DenseMultilinearExtension::<Fr>::rand(self.n, &mut rng);
            let point: Vec<Fr> = (0..self.n).map(|_| Fr::rand(&mut rng)).collect();

            // Prove timer covers commit + evaluate + open — same scope the
            // zippel side measures (`c_p <- pst13_commit(...)` plus the
            // open recursion). The MLE evaluation is the prover's
            // statement-of-fact and is implicit in the proof structure.
            let mut prove_sum = std::time::Duration::ZERO;
            let mut last_outputs = None;
            for _ in 0..crate::PROVER_SAMPLES {
                let t = Instant::now();
                let comm = Pcs::commit(&self.ck, &poly);
                let value = poly.evaluate(&point);
                let proof = Pcs::open(&self.ck, &poly, &point);
                prove_sum += t.elapsed();
                last_outputs = Some((comm, value, proof));
            }
            let prove = prove_sum / crate::PROVER_SAMPLES;
            let (comm, value, proof) = last_outputs.expect("PROVER_SAMPLES > 0");

            let mut verify_sum = std::time::Duration::ZERO;
            let mut last_ok = false;
            for _ in 0..crate::VERIFY_SAMPLES {
                let t = Instant::now();
                let ok = Pcs::check(&self.vk, &comm, &point, value, &proof);
                verify_sum += t.elapsed();
                last_ok = ok;
            }
            let verify = verify_sum / crate::VERIFY_SAMPLES;
            assert!(last_ok, "ark-poly-commit MultilinearPC verification FAILED");

            Timing { prove, verify }
        }
    }
}

// ---------------------------------------------------------------------------
// Textbook hand-rolled PST13 — kept for the byte-equality cross-tests below
// (which validate that zippel's PST13 computes the same proof bytes as a
// straightforward textbook implementation given the same SRS). Not used by
// the bench bin — the bench compares zippel against `native_side` (hyperplonk).
// ---------------------------------------------------------------------------

mod textbook_native_side {
    use super::Timing;
    use super::shared::Shared;
    use ark_bls12_381::{Bls12_381, Fr, G1Affine, G1Projective, G2Affine, G2Projective};
    use ark_ec::pairing::Pairing;
    use ark_ec::scalar_mul::ScalarMul;
    use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
    use ark_ff::PrimeField;
    use std::time::Instant;

    type E = Bls12_381;

    pub struct Proof {
        pub c: G1Projective,
        pub pis: Vec<G1Projective>,
    }

    pub struct Setup<'a> {
        shared: &'a Shared,
    }

    impl<'a> Setup<'a> {
        pub fn new(shared: &'a Shared) -> Self {
            Setup { shared }
        }

        pub fn time_protocol(&self) -> Timing {
            let t = Instant::now();
            let proof = prove(self.shared);
            let prove = t.elapsed();

            let t = Instant::now();
            let ok = verify(self.shared, &proof);
            let verify = t.elapsed();
            assert!(ok, "native PST13 verification FAILED");

            Timing { prove, verify }
        }
    }

    /// One MSM commitment + N quotient MSMs of geometrically shrinking length.
    /// Total prover work is O(2^N) field ops + (2^N + 2^(N-1) + ... + 1) ≈ 2^{N+1}
    /// G1 scalar mults across all MSMs.
    pub fn prove(shared: &Shared) -> Proof {
        let n = shared.n;
        let size = 1usize << n;

        // C = MSM(p, ck).
        let p_bi: Vec<<Fr as PrimeField>::BigInt> =
            shared.p.iter().map(|x| x.into_bigint()).collect();
        let c = G1Projective::msm_bigint(&shared.ck_affine, &p_bi);

        // Open rounds: peel one variable per iteration.
        let mut p_cur: Vec<Fr> = shared.p.clone();
        let mut ck_cur_aff: Vec<G1Affine> = shared.ck_affine.clone();
        let mut pis: Vec<G1Projective> = Vec::with_capacity(n);

        for j in 0..n {
            let half = p_cur.len() / 2;
            // Split p_cur into [lo | hi]; q = hi - lo.
            let mut q: Vec<Fr> = Vec::with_capacity(half);
            for i in 0..half {
                q.push(p_cur[half + i] - p_cur[i]);
            }
            // ck'_i = ck_cur[i] + ck_cur[half + i]. Add in projective then
            // batch-normalize back to affine for the next round's MSM.
            let mut ck_next_proj: Vec<G1Projective> = Vec::with_capacity(half);
            for i in 0..half {
                ck_next_proj.push(ck_cur_aff[i].into_group() + ck_cur_aff[half + i].into_group());
            }
            let ck_next_aff = G1Projective::normalize_batch(&ck_next_proj);

            let q_bi: Vec<<Fr as PrimeField>::BigInt> = q.iter().map(|x| x.into_bigint()).collect();
            let pi = G1Projective::msm_bigint(&ck_next_aff, &q_bi);
            pis.push(pi);

            // p_red = p_lo + z_j · q.
            let z_j = shared.z[j];
            let p_red: Vec<Fr> = (0..half).map(|i| p_cur[i] + z_j * q[i]).collect();
            p_cur = p_red;
            ck_cur_aff = ck_next_aff;
        }

        Proof { c, pis }
    }

    /// Single fused multi_pairing of length (n+1):
    ///   e(C − y·g, h) · Π_j e(−π_j, α_h_j − z_j·h) == 1_GT.
    /// One Miller loop + one final exponentiation.
    pub fn verify(shared: &Shared, proof: &Proof) -> bool {
        let n = shared.n;
        let g = shared.g_gen;
        let h = shared.h_gen;

        // ---- G1 side: [C − y·g, −π_0, ..., −π_{n-1}] -----------------------
        // Batch-normalize via Montgomery's trick — 1 inversion for the whole
        // batch vs N+1 individual inversions.
        let mut g1_proj: Vec<G1Projective> = Vec::with_capacity(n + 1);
        g1_proj.push(proof.c - g * shared.y);
        for pi in &proof.pis {
            g1_proj.push(-(*pi));
        }
        let g1_terms: Vec<G1Affine> = G1Projective::normalize_batch(&g1_proj);

        // ---- G2 side: [h, α_h_0 − z_0·h, ..., α_h_{n-1} − z_{n-1}·h] -------
        // The n G2 muls (h_gen * z_j) share a single base. Use arkworks'
        // fixed-base `batch_mul` — windowed precomputation amortized across
        // all n scalars, ~2-3× faster than n sequential muls. This is what
        // zippel's `value_mul` for `G2 * VecScalar` dispatches to under the
        // hood ([backend/src/config.rs:256-266]); matching that path here
        // keeps the comparison honest.
        //
        // Same n=1 special-case: batch_mul precomputation costs ~85
        // inversions, which is wasted work below 2 scalars. zippel does the
        // same fast path at the same call site, so mirror it here.
        let hz: Vec<G2Projective> = if n == 1 {
            vec![h * shared.z[0]]
        } else {
            h.batch_mul(&shared.z)
                .into_iter()
                .map(|aff| aff.into_group())
                .collect()
        };
        let mut g2_proj: Vec<G2Projective> = Vec::with_capacity(n + 1);
        g2_proj.push(h);
        for j in 0..n {
            g2_proj.push(shared.alpha_h[j] - hz[j]);
        }
        let g2_terms: Vec<G2Affine> = G2Projective::normalize_batch(&g2_proj);

        let result = <E as Pairing>::multi_pairing(g1_terms, g2_terms);
        // GT additive identity check via the `r == r − r` idiom — same as
        // other benches in this crate.
        result == result - result
    }
}

// ---------------------------------------------------------------------------
// Zippel side: compile examples/pst13/pst13.zippel, feed Shared inputs, time
// prove + verify. Prove timer covers `c_p <- ...` (commit) + the recursion's
// log-N π log-events (open).
// ---------------------------------------------------------------------------

pub mod zippel_side {
    use super::Timing;
    use super::shared::Shared;
    use backend::{ArkBls12_381, Value};
    use lang::id::{Tid, Vid};
    use share::Ctx;
    use std::path::PathBuf;
    use std::time::Instant;
    use zippel::{ZippelArgs, ZippelHandler, check_verification};

    pub struct Setup<'a> {
        handler: ZippelHandler<ArkBls12_381>,
        inputs_base: Ctx<Vid, Value<ArkBls12_381>>,
        #[allow(dead_code)]
        shared: &'a Shared,
    }

    impl<'a> Setup<'a> {
        pub fn new(shared: &'a Shared) -> Self {
            // Pre-affinize ck — same fix as the Groth16 bench (avoids per-prove
            // `normalize_batch`). ck_affine is already computed in `Shared`.
            let inputs_base = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
                (
                    Vid("p".to_string()),
                    Value::VecScalar(shared.p.clone()),
                ),
                (
                    Vid("z".to_string()),
                    Value::VecScalar(shared.z.clone()),
                ),
                (Vid("y".to_string()), Value::Scalar(shared.y)),
                (
                    Vid("ck_N".to_string()),
                    Value::VecG1Affine(shared.ck_affine.clone()),
                ),
                (Vid("g_gen".to_string()), Value::G1(shared.g_gen)),
                (Vid("h_gen".to_string()), Value::G2(shared.h_gen)),
                (
                    Vid("alpha_H".to_string()),
                    Value::VecG2(shared.alpha_h.clone()),
                ),
            ]);

            let args = ZippelArgs::new(PathBuf::from("examples/pst13/pst13.zippel"));
            let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
            let mut sizes = Ctx::new();
            sizes.insert(&Tid::new("N"), &shared.n);
            handler.compile(&sizes);

            Setup {
                handler,
                inputs_base,
                shared,
            }
        }

        pub fn time_protocol(&mut self) -> Timing {
            let prover_scheduled = self.handler.default_schedule_prover();

            let mut prove_sum = std::time::Duration::ZERO;
            let mut last_proof = None;
            for _ in 0..crate::PROVER_SAMPLES {
                let sched = prover_scheduled.clone();
                let inputs_c = self.inputs_base.clone();
                let t = Instant::now();
                let proof = self
                    .handler
                    .run_prover(sched, inputs_c)
                    .expect("zippel pst13 prover failed");
                prove_sum += t.elapsed();
                last_proof = Some(proof);
            }
            let prove = prove_sum / crate::PROVER_SAMPLES;
            let proof = last_proof.expect("PROVER_SAMPLES > 0");

            let verifier_scheduled = self.handler.default_schedule_verifier();
            let mut verify_sum = std::time::Duration::ZERO;
            let mut last_result = None;
            for _ in 0..crate::VERIFY_SAMPLES {
                let sched = verifier_scheduled.clone();
                let proof_c = proof.clone();
                let t = Instant::now();
                let verifier_result = self
                    .handler
                    .run_verifier(sched, proof_c)
                    .expect("zippel pst13 verifier failed");
                verify_sum += t.elapsed();
                last_result = Some(verifier_result);
            }
            let verify = verify_sum / crate::VERIFY_SAMPLES;
            let result = check_verification(last_result.expect("VERIFY_SAMPLES > 0"));
            assert!(result.passed, "zippel PST13 verification FAILED");

            Timing { prove, verify }
        }
    }
}

// ---------------------------------------------------------------------------
// Cross-verification tests: each side verifies the other's proof.
// PST13 is deterministic (no blinding factors), so we additionally assert
// byte-equality of the commitment and the per-round π values.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod cross_tests {
    use super::textbook_native_side::{Proof, prove, verify};
    use super::shared::{Shared, build};
    use ark_bls12_381::G1Projective;
    use backend::{ArkBls12_381, Value};
    use lang::id::{Tid, Vid};
    use share::Ctx;
    use std::path::PathBuf;
    use zippel::{ZippelArgs, ZippelHandler, check_verification};

    const N_SWEEP: &[usize] = &[1, 2, 4, 6];

    fn zippel_handler(shared: &Shared) -> ZippelHandler<ArkBls12_381> {
        let zippel_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join("examples/pst13/pst13.zippel");
        let args = ZippelArgs::new(zippel_path);
        let mut handler: ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);
        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("N"), &shared.n);
        handler.compile(&sizes);
        handler
    }

    fn zip_inputs(shared: &Shared) -> Ctx<Vid, Value<ArkBls12_381>> {
        Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
            (Vid("p".to_string()), Value::VecScalar(shared.p.clone())),
            (Vid("z".to_string()), Value::VecScalar(shared.z.clone())),
            (Vid("y".to_string()), Value::Scalar(shared.y)),
            (
                Vid("ck_N".to_string()),
                Value::VecG1Affine(shared.ck_affine.clone()),
            ),
            (Vid("g_gen".to_string()), Value::G1(shared.g_gen)),
            (Vid("h_gen".to_string()), Value::G2(shared.h_gen)),
            (
                Vid("alpha_H".to_string()),
                Value::VecG2(shared.alpha_h.clone()),
            ),
        ])
    }

    /// Test 1: native produces (c, π_0..π_{n-1}); zippel verifier accepts.
    #[test]
    fn native_prove_then_zippel_verify() {
        for &n in N_SWEEP {
            run_native_prove_zippel_verify(n);
        }
    }

    fn run_native_prove_zippel_verify(n: usize) {
        let shared = build(n);
        let proof_n = prove(&shared);

        // Sanity: native verifier accepts its own proof.
        assert!(
            verify(&shared, &proof_n),
            "n={n}: native verifier rejected its own proof"
        );

        // Prime zippel handler state by running its prover once.
        let mut handler = zippel_handler(&shared);
        let prover_sched = handler.default_schedule_prover();
        let _ = handler
            .run_prover(prover_sched, zip_inputs(&shared))
            .expect("zippel run_prover (priming handler state)");

        // Pack native proof into the zippel transcript order: [c_p, π_0, ..., π_{n-1}].
        let mut cross_proof: Vec<Value<ArkBls12_381>> = Vec::with_capacity(n + 1);
        cross_proof.push(Value::G1(proof_n.c));
        for pi in &proof_n.pis {
            cross_proof.push(Value::G1(*pi));
        }

        let verifier_sched = handler.default_schedule_verifier();
        let verifier_result = handler
            .run_verifier(verifier_sched, cross_proof)
            .expect("zippel run_verifier on cross-proof");
        let result = check_verification(verifier_result);
        assert!(
            result.passed,
            "n={n}: CROSS-VERIFY FAILED: zippel verifier rejected native-produced proof"
        );
    }

    /// Test 2: zippel produces (c, π_0..π_{n-1}); native verifier accepts.
    /// Additionally asserts byte-equality with the native-produced proof
    /// (PST13 is deterministic, so they should match exactly).
    #[test]
    fn zippel_prove_then_native_verify() {
        for &n in N_SWEEP {
            run_zippel_prove_native_verify(n);
        }
    }

    fn run_zippel_prove_native_verify(n: usize) {
        let shared = build(n);

        let mut handler = zippel_handler(&shared);
        let prover_sched = handler.default_schedule_prover();
        let zip_proof: Vec<Value<ArkBls12_381>> = handler
            .run_prover(prover_sched, zip_inputs(&shared))
            .expect("zippel run_prover");

        assert_eq!(
            zip_proof.len(),
            n + 1,
            "n={n}: expected n+1 transcript items (c_p, π_0..π_{{n-1}})"
        );

        let c = match &zip_proof[0] {
            Value::G1(g) => *g,
            other => panic!("expected G1 c_p, got {:?}", std::mem::discriminant(other)),
        };
        let mut pis: Vec<G1Projective> = Vec::with_capacity(n);
        for (i, v) in zip_proof.iter().enumerate().skip(1) {
            match v {
                Value::G1(g) => pis.push(*g),
                other => panic!(
                    "expected G1 π_{}, got {:?}",
                    i - 1,
                    std::mem::discriminant(other)
                ),
            }
        }
        let proof_z = Proof { c, pis };

        // Byte-equality with native: PST13 is deterministic.
        let proof_n = prove(&shared);
        assert_eq!(
            proof_z.c, proof_n.c,
            "n={n}: c_p mismatch (zippel vs native)"
        );
        assert_eq!(proof_z.pis, proof_n.pis, "n={n}: π values mismatch");

        // Native verifier accepts zippel's proof.
        assert!(
            verify(&shared, &proof_z),
            "n={n}: native verifier rejected zippel-produced proof"
        );
    }
}
