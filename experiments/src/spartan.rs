//! Spartan comparison: zippel-compiled Spartan NIZK, on any backend
//! (`ArkCurve25519`, or `DalekRistretto`, the curve25519-dalek group
//! libspartan uses), vs. the vendored `ark-spartan` implementation and
//! libspartan.
//!
//! Statement on both sides: a synthetic satisfiable R1CS instance with
//! `2^M` constraints, proved with a sumcheck-based polynomial IOP whose
//! witness commitment is Hyrax over a `2^L x 2^Mh` matrix (see
//! [`hyrax_split`]). Timing covers prove and verify only — instance
//! generation and `.zippel` compilation are excluded.

use crate::Timing;
use ark_std::rand::SeedableRng;
use backend::{Backend, Field, Group, PolyVariant, Value, VirtualPolynomial};
use lang::id::{Tid, Vid};
use rand::Rng;
use share::Ctx;
use std::collections::HashMap;
use std::path::PathBuf;
use zippel::{
    CompileOptions, CompiledProtocol, CompiledProver, CompiledVerifier, ParsedModule,
    proof_size_bytes,
};

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
pub struct Setup<C: Backend> {
    m: usize,
    prover: CompiledProver<C>,
    verifier: CompiledVerifier<C>,
    inputs: HashMap<Vid, Value<C>>,
    /// What the prover's `az`, `bz`, `cz` inputs are computed from, inside
    /// each timed run, as libspartan computes them inside `prove`.
    products: MatVec<C::F>,
    compile_time: Vec<std::time::Duration>,
}

/// The R1CS matrices (as `(row, col, value)` triples) and the assignment
/// `z = (w, 1, io)` they multiply.
struct MatVec<F> {
    mats: [Vec<(usize, usize, F)>; 3],
    z: Vec<F>,
}

impl<F: Field> MatVec<F> {
    /// `[Az, Bz, Cz]`.
    fn products(&self) -> [Vec<F>; 3] {
        self.mats.each_ref().map(|mat| {
            let mut out = vec![F::zero(); self.z.len()];
            for &(i, c, v) in mat {
                out[i] += v * self.z[c];
            }
            out
        })
    }
}

impl<C: Backend> Setup<C> {
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

        let (inputs, products) = make_inputs::<C>(m);

        let ((prover, verifier), compile_time) = crate::sample_compile(|| {
            let module = ParsedModule::load(zippel_path.clone()).expect("parse protocol");
            let mut sizes = Ctx::new();
            sizes.insert(&Tid::new("M"), &m);
            let protocol: CompiledProtocol<C> = module
                .compile(&sizes, CompileOptions::default())
                .expect("compile protocol");
            (
                protocol.project_prover(),
                protocol.project_verifier().expect("project verifier"),
            )
        });

        Setup {
            m,
            prover,
            verifier,
            inputs,
            products,
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
            self.prover.graph().node_count(),
            self.verifier.graph().node_count(),
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
        // Az, Bz, Cz are computed inside each run, as libspartan computes
        // them inside `prove`.
        let (prove, prove_peak, proof) = crate::sample(|| {
            let [az, bz, cz] = self.products.products();
            let computed = [("az", az), ("bz", bz), ("cz", cz)]
                .map(|(name, v)| (Vid::from(name), Value::vec_scalar(v)));
            self.prover
                .prove(crate::lend(&self.inputs).chain(computed))
                .expect("run_prover failed")
        });
        let proof_bytes = proof_size_bytes::<C>(&proof);
        let (verify, verify_peak, passed) =
            crate::sample_zippel_verifier(&self.verifier, &proof, &self.inputs);

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
    z.push(F::from(1u64));
    z.extend_from_slice(io);

    let const_col = w.len();
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

fn make_inputs<C: Backend>(m: usize) -> (HashMap<Vid, Value<C>>, MatVec<C::F>) {
    let num_cons = 1usize << m;
    let witness_len = 1usize << (m - 1);
    let io_len = witness_len - 1;
    let (_l, m_h) = hyrax_split(m);
    let ncols = 1usize << m_h;

    let mut seed_bytes = [0u8; 32];
    seed_bytes[..8].copy_from_slice(&(0xFEEDFACE_u64 ^ m as u64).to_le_bytes());
    let mut rng = ark_std::rand::rngs::StdRng::from_seed(seed_bytes);
    let one = C::F::one();

    let witness: Vec<C::F> = (0..witness_len).map(|_| C::F::rand(&mut rng)).collect();
    let instance: Vec<C::F> = (0..io_len).map(|_| C::F::rand(&mut rng)).collect();

    let r1cs = random_r1cs::<C::F, _>(&mut rng, num_cons, &witness, &instance);

    let mut z: Vec<C::F> = Vec::with_capacity(num_cons);
    z.extend_from_slice(&witness);
    z.push(one);
    z.extend_from_slice(&instance);

    let products = MatVec {
        mats: [r1cs.mat_a.clone(), r1cs.mat_b.clone(), r1cs.mat_c.clone()],
        z,
    };
    let [az, bz, cz] = products.products();
    for i in 0..num_cons {
        assert_eq!(
            az[i] * bz[i],
            cz[i],
            "row {i} of synthetic R1CS is unsatisfied"
        );
    }

    let triples_to_mle_evals = |triples: &[(usize, usize, C::F)]| -> Vec<(usize, C::F)> {
        triples
            .iter()
            .filter(|(_, _, v)| !v.is_zero())
            .map(|(i, c, v)| (c * num_cons + i, *v))
            .collect()
    };
    let two_m_vars = 2 * m;
    let mk_sparse_mle = |evals: Vec<(usize, C::F)>| {
        Value::poly(VirtualPolynomial::from_poly(PolyVariant::SparseMle {
            num_vars: two_m_vars,
            evals,
        }))
    };
    let mat_a_t = mk_sparse_mle(triples_to_mle_evals(&r1cs.mat_a));
    let mat_b_t = mk_sparse_mle(triples_to_mle_evals(&r1cs.mat_b));
    let mat_c_t = mk_sparse_mle(triples_to_mle_evals(&r1cs.mat_c));

    let g_vec_proj: Vec<C::G1> = (0..ncols).map(|_| C::G1::rand(&mut rng)).collect();
    let g_vec_aff = C::G1::normalize_batch(&g_vec_proj);
    // libspartan's generators: `gens_1` (g_1, h_1, shared by the PCS and the
    // sumchecks), and `gens_4`, `gens_3` for the round polynomials, each with its
    // own blinding base.
    let g_1 = C::G1::rand(&mut rng);
    let h_1 = C::G1::rand(&mut rng);
    let g_4_proj: Vec<C::G1> = (0..4).map(|_| C::G1::rand(&mut rng)).collect();
    let g_4 = C::G1::normalize_batch(&g_4_proj);
    let h_4 = C::G1::rand(&mut rng);
    let g_3_proj: Vec<C::G1> = (0..3).map(|_| C::G1::rand(&mut rng)).collect();
    let g_3 = C::G1::normalize_batch(&g_3_proj);
    let h_3 = C::G1::rand(&mut rng);

    let placeholder_tau: Vec<C::F> = vec![C::F::zero(); m];

    let inputs = crate::harness_inputs([
        (Vid("mat_a_t".to_string()), mat_a_t),
        (Vid("mat_b_t".to_string()), mat_b_t),
        (Vid("mat_c_t".to_string()), mat_c_t),
        (Vid("io".to_string()), Value::vec_scalar(r1cs.io)),
        (Vid("w".to_string()), Value::vec_scalar(r1cs.w)),
        (Vid("g_vec_w".to_string()), Value::vec_g1_affine(g_vec_aff)),
        (Vid("g_1".to_string()), Value::g1(g_1)),
        (Vid("h_1".to_string()), Value::g1(h_1)),
        (Vid("g_4".to_string()), Value::vec_g1_affine(g_4)),
        (Vid("h_4".to_string()), Value::g1(h_4)),
        (Vid("g_3".to_string()), Value::vec_g1_affine(g_3)),
        (Vid("h_3".to_string()), Value::g1(h_3)),
        (
            Vid("placeholder_tau".to_string()),
            Value::vec_scalar(placeholder_tau),
        ),
    ]);
    (inputs, products)
}

#[cfg(test)]
mod tests {
    use super::*;
    /// `v` changed: one added to a scalar or index, the generator added to a group
    /// element, the first entry of a vector changed.
    pub(super) fn tampered<C: Backend>(v: &Value<C>) -> Value<C> {
        match v {
            Value::Scalar(x) => Value::Scalar(*x + C::F::one()),
            Value::G1(g) => Value::g1(**g + C::G1::generator()),
            Value::G1Affine(g) => Value::g1(Into::<C::G1>::into(**g) + C::G1::generator()),
            Value::VecScalar(xs) => {
                let mut xs = xs.to_vec();
                xs[0] += C::F::one();
                Value::vec_scalar(xs)
            }
            Value::VecG1(gs) => {
                let mut gs = gs.to_vec();
                gs[0] += C::G1::generator();
                Value::vec_g1(gs)
            }
            Value::VecG1Affine(gs) => {
                let mut gs: Vec<C::G1> = gs.iter().map(|g| (*g).into()).collect();
                gs[0] += C::G1::generator();
                Value::vec_g1(gs)
            }
            other => panic!("no tampering for {other}"),
        }
    }

    /// The verifier rejects the proof with any one element changed, including the
    /// last messages, which no later challenge depends on.
    #[test]
    fn every_proof_element_is_checked() {
        let setup = Setup::<backend::ArkCurve25519>::new(4);
        let [az, bz, cz] = setup.products.products();
        let computed = [("az", az), ("bz", bz), ("cz", cz)]
            .map(|(name, v)| (Vid::from(name), Value::vec_scalar(v)));
        let proof = setup
            .prover
            .prove(crate::lend(&setup.inputs).chain(computed))
            .unwrap();
        let verify = |proof: Vec<Value<backend::ArkCurve25519>>| {
            setup
                .verifier
                .verify(proof, crate::lend(&setup.inputs))
                .unwrap()
        };
        assert!(verify(proof.clone()));
        for i in 0..proof.len() {
            let mut bad = proof.clone();
            bad[i] = tampered(&proof[i]);
            assert!(!verify(bad), "element {i} ({}) is unchecked", proof[i]);
        }
    }
}

#[cfg(test)]
mod cross_tests;
