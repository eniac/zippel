//! Spartan comparison: zippel-compiled Spartan NIZK vs. the vendored
//! `ark-spartan` implementation — both on Curve25519.
//!
//! Statement on both sides: a synthetic satisfiable R1CS instance with
//! `2^M` constraints, proved with a sumcheck-based polynomial IOP whose
//! witness commitment is Hyrax over a `2^L x 2^Mh` matrix (see
//! [`hyrax_split`]). Timing covers prove and verify only — instance
//! generation and `.zippel` compilation are excluded.

use crate::Timing;
use ark_curve25519::{EdwardsProjective as G1Projective, Fr};
use ark_ec::CurveGroup;
use ark_ff::{Field, Zero};
use ark_std::UniformRand;
use ark_std::rand::SeedableRng;
use backend::{ArkCurve25519, PolyVariant, Value, VirtualPolynomial};
use lang::id::{Tid, Vid};
use rand::Rng;
use share::Ctx;
use std::path::PathBuf;
use zippel::{Inputs, ZippelArgs, ZippelHandler, check_verification, proof_size_bytes};

/// Default `log_2` of the R1CS constraint count used by the Spartan sweep.
pub const DEFAULT_M: usize = 8;

/// Splits the `m - 1` witness variables into the row/column halves of the
/// Hyrax commitment matrix, returning `(log2(rows), log2(cols))`.
///
/// The column half absorbs the odd variable, so `cols >= rows`; the verifier
/// cost is `O(cols)` group operations while the prover commits `rows` rows.
///
/// # Panics
/// Panics on debug builds if `m` is zero, since the witness variable count
/// `m - 1` underflows.
pub fn hyrax_split(m: usize) -> (usize, usize) {
    let nw = m - 1;
    let l = nw / 2;
    let m_h = nw - l;
    (l, m_h)
}

/// Result of one timed zippel Spartan run: every prove/verify sample plus
/// the proof size and verification outcome of the last sample.
pub struct ZippelTiming {
    /// Per-sample wall-times and peak heaps.
    pub timing: Timing,
    /// Serialized size of the produced proof certificate, in bytes.
    pub proof_bytes: usize,
    /// Whether the verifier graph returned all-`true`, i.e. the proof checked.
    pub passed: bool,
}

/// Compiled Spartan protocol plus its pre-generated prover inputs, reused
/// across every timing sample at one size.
pub struct Setup {
    m: usize,
    handler: ZippelHandler<ArkCurve25519>,
    inputs: Inputs<ArkCurve25519>,
    compile_time: Vec<std::time::Duration>,
}

impl Setup {
    /// Compiles `examples/spartan/spartan.zippel` with size variable `M` bound
    /// to `m` and generates a satisfying synthetic R1CS instance for it.
    ///
    /// # Panics
    /// Panics if `m < 3` (the Hyrax split needs at least two witness
    /// variables), if the generated R1CS is unsatisfied, or if compiling the
    /// `.zippel` source fails.
    pub fn new(m: usize) -> Self {
        assert!(m >= 3, "M must be >= 3 (Hyrax needs NW >= 2)");

        let zippel_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join("examples/spartan/spartan.zippel");
        let zippel_path = if zippel_path.exists() {
            zippel_path
        } else {
            PathBuf::from("examples/spartan/spartan.zippel")
        };

        let inputs = prover_create_inputs(m);

        let (handler, compile_time) = crate::sample_compile(|| {
            let args = ZippelArgs::new(zippel_path.clone());
            let mut handler: ZippelHandler<ArkCurve25519> = ZippelHandler::new(args);
            let mut sizes = Ctx::new();
            sizes.insert(&Tid::new("M"), &m);
            handler.compile(&sizes);
            handler
        });

        Setup {
            m,
            handler,
            inputs,
            compile_time,
        }
    }

    /// Wall-clock time the `.zippel` source took to compile in [`Setup::new`].
    pub fn compile_time(&self) -> Vec<std::time::Duration> {
        self.compile_time.clone()
    }

    /// (prover graph node count, verifier graph node count).
    pub fn graph_sizes(&self) -> (usize, usize) {
        (
            self.handler.prover_graph().node_count(),
            self.handler.verifier_graph().node_count(),
        )
    }

    /// Runs prover and verifier [`crate::SAMPLES`] times each and reports
    /// every sample, the proof size, and whether verification passed.
    ///
    /// # Panics
    /// Panics if either graph fails to execute.
    /// Unlike the other benches this does not assert on a failed verification;
    /// the outcome is reported in [`ZippelTiming::passed`].
    pub fn time_protocol(&mut self) -> ZippelTiming {
        let (prove, prove_peak, proof) = crate::sample(|| {
            self.handler
                .run_prover(&self.inputs)
                .expect("zippel spartan prover failed")
        });
        let proof_bytes = proof_size_bytes::<ArkCurve25519>(&proof);
        let (verify, verify_peak, result) = crate::sample(|| {
            self.handler
                .run_verifier(&proof, &self.inputs)
                .expect("zippel spartan verifier failed")
        });
        let passed = check_verification(&result);

        ZippelTiming {
            timing: Timing {
                prove,
                verify,
                prove_peak,
                verify_peak,
            },
            proof_bytes,
            passed,
        }
    }

    /// [`Self::time_protocol`] reduced to the crate-wide [`Timing`] shape,
    /// dropping the proof size, for a caller that requires the proof to
    /// verify, as every other bench does.
    ///
    /// # Panics
    /// Panics under the same conditions as [`Self::time_protocol`], and if
    /// the proof fails verification.
    pub fn timing(&mut self) -> Timing {
        let t = self.time_protocol();
        assert!(t.passed, "zippel spartan proof failed verification");
        t.timing
    }

    /// `log_2` of the constraint count this setup was compiled for.
    pub fn m(&self) -> usize {
        self.m
    }
}

struct R1csInstance<F> {
    mat_a: Vec<(usize, usize, F)>,
    mat_b: Vec<(usize, usize, F)>,
    mat_c: Vec<(usize, usize, F)>,
    io: Vec<F>,
    w: Vec<F>,
}

fn random_r1cs<F, R>(rng: &mut R, m: usize, w: &[F], io: &[F]) -> R1csInstance<F>
where
    F: Field,
    R: Rng + ?Sized,
{
    let num_vars = w.len() + io.len() + 1;
    assert_eq!(num_vars, m);

    let mut z = Vec::with_capacity(m);
    z.extend_from_slice(w);
    z.extend_from_slice(io);
    z.push(F::from(1u64));

    let const_col = m - 1;
    const K_NNZ_PER_ROW: usize = 1;
    let pick_k_cols = |rng: &mut R, force_include: Option<usize>| -> Vec<usize> {
        let mut cols: Vec<usize> = Vec::with_capacity(K_NNZ_PER_ROW);
        if let Some(c) = force_include {
            cols.push(c);
        }
        while cols.len() < K_NNZ_PER_ROW && cols.len() < m {
            let c = rng.gen_range(0..m);
            if !cols.contains(&c) {
                cols.push(c);
            }
        }
        cols
    };
    let mut mat_a: Vec<(usize, usize, F)> = Vec::with_capacity(K_NNZ_PER_ROW * m);
    let mut mat_b: Vec<(usize, usize, F)> = Vec::with_capacity(K_NNZ_PER_ROW * m);
    let mut mat_c: Vec<(usize, usize, F)> = Vec::with_capacity(K_NNZ_PER_ROW * m);

    for i in 0..m {
        let a_cols = pick_k_cols(rng, None);
        let b_cols = pick_k_cols(rng, None);
        let c_cols = pick_k_cols(rng, Some(const_col));

        let a_vals: Vec<F> = (0..a_cols.len()).map(|_| F::rand(rng)).collect();
        let b_vals: Vec<F> = (0..b_cols.len()).map(|_| F::rand(rng)).collect();
        let mut c_vals: Vec<F> = (0..c_cols.len()).map(|_| F::rand(rng)).collect();

        let az_i: F = a_cols
            .iter()
            .zip(a_vals.iter())
            .map(|(c, v)| z[*c] * *v)
            .sum();
        let bz_i: F = b_cols
            .iter()
            .zip(b_vals.iter())
            .map(|(c, v)| z[*c] * *v)
            .sum();
        let target = az_i * bz_i;

        let const_col_pos_in_c = c_cols
            .iter()
            .position(|&c| c == const_col)
            .expect("c_cols must include const_col");
        let other: F = c_cols
            .iter()
            .zip(c_vals.iter())
            .enumerate()
            .filter(|(idx, _)| *idx != const_col_pos_in_c)
            .map(|(_, (c, v))| z[*c] * *v)
            .sum();
        c_vals[const_col_pos_in_c] = target - other;

        for (c, v) in a_cols.iter().zip(a_vals.iter()) {
            mat_a.push((i, *c, *v));
        }
        for (c, v) in b_cols.iter().zip(b_vals.iter()) {
            mat_b.push((i, *c, *v));
        }
        for (c, v) in c_cols.iter().zip(c_vals.iter()) {
            mat_c.push((i, *c, *v));
        }
    }

    R1csInstance {
        mat_a,
        mat_b,
        mat_c,
        io: io.to_vec(),
        w: w.to_vec(),
    }
}

fn prover_create_inputs(m: usize) -> Inputs<ArkCurve25519> {
    let num_cons = 1usize << m;
    let witness_len = 1usize << (m - 1);
    let io_len = witness_len - 1;
    let (_l, m_h) = hyrax_split(m);
    let ncols = 1usize << m_h;

    let mut seed_bytes = [0u8; 32];
    seed_bytes[..8].copy_from_slice(&(0xFEEDFACE_u64 ^ m as u64).to_le_bytes());
    let mut rng = ark_std::rand::rngs::StdRng::from_seed(seed_bytes);
    let one = Fr::from(1u64);

    let witness: Vec<Fr> = (0..witness_len).map(|_| Fr::rand(&mut rng)).collect();
    let instance: Vec<Fr> = (0..io_len).map(|_| Fr::rand(&mut rng)).collect();

    let r1cs = random_r1cs::<Fr, _>(&mut rng, num_cons, &witness, &instance);

    let mut z: Vec<Fr> = Vec::with_capacity(num_cons);
    z.extend_from_slice(&witness);
    z.extend_from_slice(&instance);
    z.push(one);

    let mut az: Vec<Fr> = vec![Fr::from(0u64); num_cons];
    let mut bz: Vec<Fr> = vec![Fr::from(0u64); num_cons];
    let mut cz: Vec<Fr> = vec![Fr::from(0u64); num_cons];
    for &(i, c, v) in &r1cs.mat_a {
        az[i] += v * z[c];
    }
    for &(i, c, v) in &r1cs.mat_b {
        bz[i] += v * z[c];
    }
    for &(i, c, v) in &r1cs.mat_c {
        cz[i] += v * z[c];
    }
    for i in 0..num_cons {
        assert_eq!(
            az[i] * bz[i],
            cz[i],
            "row {i} of synthetic R1CS is unsatisfied"
        );
    }

    let triples_to_mle_evals = |triples: &[(usize, usize, Fr)]| -> Vec<(usize, Fr)> {
        triples
            .iter()
            .filter(|(_, _, v)| !v.is_zero())
            .map(|(i, c, v)| (c * num_cons + i, *v))
            .collect()
    };
    let two_m_vars = 2 * m;
    let mk_sparse_mle = |evals: Vec<(usize, Fr)>| {
        Value::Poly(VirtualPolynomial::from_poly(PolyVariant::SparseMle {
            num_vars: two_m_vars,
            evals,
        }))
    };
    let mat_a_t = mk_sparse_mle(triples_to_mle_evals(&r1cs.mat_a));
    let mat_b_t = mk_sparse_mle(triples_to_mle_evals(&r1cs.mat_b));
    let mat_c_t = mk_sparse_mle(triples_to_mle_evals(&r1cs.mat_c));

    let g_vec_proj: Vec<G1Projective> = (0..ncols).map(|_| G1Projective::rand(&mut rng)).collect();
    let g_vec_aff = G1Projective::normalize_batch(&g_vec_proj);
    let g_base_w = G1Projective::rand(&mut rng);
    let h_base_w = G1Projective::rand(&mut rng);

    let g_evs_d3_proj: Vec<G1Projective> = (0..4).map(|_| G1Projective::rand(&mut rng)).collect();
    let g_evs_d3_aff = G1Projective::normalize_batch(&g_evs_d3_proj);
    let g_evs_d2_proj: Vec<G1Projective> = (0..3).map(|_| G1Projective::rand(&mut rng)).collect();
    let g_evs_d2_aff = G1Projective::normalize_batch(&g_evs_d2_proj);
    let h_evs = G1Projective::rand(&mut rng);

    let placeholder_tau: Vec<Fr> = vec![Fr::from(0u64); m];

    Inputs::<ArkCurve25519>::from_iter([
        (Vid("mat_a_t".to_string()), mat_a_t),
        (Vid("mat_b_t".to_string()), mat_b_t),
        (Vid("mat_c_t".to_string()), mat_c_t),
        (Vid("io".to_string()), Value::vec_scalar(r1cs.io)),
        (Vid("w".to_string()), Value::vec_scalar(r1cs.w)),
        (Vid("az".to_string()), Value::vec_scalar(az)),
        (Vid("bz".to_string()), Value::vec_scalar(bz)),
        (Vid("cz".to_string()), Value::vec_scalar(cz)),
        (Vid("g_vec_w".to_string()), Value::vec_g1_affine(g_vec_aff)),
        (Vid("g_base_w".to_string()), Value::G1(g_base_w)),
        (Vid("h_base_w".to_string()), Value::G1(h_base_w)),
        (
            Vid("g_evs_d3".to_string()),
            Value::vec_g1_affine(g_evs_d3_aff),
        ),
        (
            Vid("g_evs_d2".to_string()),
            Value::vec_g1_affine(g_evs_d2_aff),
        ),
        (Vid("h_evs".to_string()), Value::G1(h_evs)),
        (
            Vid("placeholder_tau".to_string()),
            Value::vec_scalar(placeholder_tau),
        ),
    ])
}
