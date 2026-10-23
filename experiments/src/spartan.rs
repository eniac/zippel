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
mod cross_tests {
    use backend::{Backend, Field, Value};

    fn corrupt_response<C: Backend>(proof: &mut [Value<C>]) {
        let Some(Value::Scalar(response)) = proof.last_mut() else {
            panic!("expected a final scalar response");
        };
        *response += C::F::one();
    }

    mod ark {
        const HAS_PCS_BATCHING: bool = false;
        use crate::upstream::ark_spartan as native;
        use backend::{ArkCurve25519 as C, Backend, Value};
        type G = <C as Backend>::G1;
        type F = <C as Backend>::F;
        type V = Value<C>;
        type NativeNizk = native::NIZK<G>;
        type NativeInstance = native::Instance<F>;
        type NativeGens = native::NIZKGens<G>;
        type NativeVars = native::VarsAssignment<F>;
        type NativeInputs = native::InputsAssignment<F>;
        type NativeGroup = G;
        type NativeScalar = F;
        type R1csProof = native::r1csproof::R1CSProof<G>;
        type SumcheckProof = native::sumcheck::ZKSumcheckInstanceProof<G>;
        type PolyCommitment = native::dense_mlpoly::PolyCommitment<G>;
        type PolyEvalProof = native::dense_mlpoly::PolyEvalProof<G>;
        type KnowledgeProof = native::nizk::KnowledgeProof<G>;
        type ProductProof = native::nizk::ProductProof<G>;
        type EqualityProof = native::nizk::EqualityProof<G>;
        type DotProductProof = native::nizk::DotProductProof<G>;
        type DotProductProofLog = native::nizk::DotProductProofLog<G>;
        type BulletReductionProof = native::nizk::bullet::BulletReductionProof<G>;

        fn group(g: &G) -> V {
            Value::g1(*g)
        }
        fn native_group(v: &V) -> G {
            match v {
                Value::G1(g) => **g,
                Value::G1Affine(g) => (**g).into(),
                _ => panic!("expected group element, got {v}"),
            }
        }
        fn scalar(f: &F) -> V {
            Value::Scalar(*f)
        }
        fn native_scalar(v: &V) -> F {
            match v {
                Value::Scalar(f) => *f,
                _ => panic!("expected scalar, got {v}"),
            }
        }

        fn setup(
            m: usize,
            inputs: &mut std::collections::HashMap<lang::id::Vid, V>,
            products: &super::super::MatVec<F>,
        ) -> (NativeInstance, NativeGens, NativeVars, NativeInputs) {
            let n = 1 << m;
            let nw = n / 2;
            let inst = NativeInstance::new(
                n,
                nw,
                nw - 1,
                &products.mats[0],
                &products.mats[1],
                &products.mats[2],
            )
            .unwrap();
            let vars = NativeVars::new(&products.z[..nw]).unwrap();
            let io = NativeInputs::new(&products.z[nw + 1..]).unwrap();
            assert!(inst.is_sat(&vars, &io).unwrap());
            let gens = NativeGens::new(n, nw, nw - 1);
            let pc = &gens.gens_r1cs_sat.gens_pc.gens;
            let sc = &gens.gens_r1cs_sat.gens_sc;
            inputs.extend(
                [
                    (
                        "g_vec_w",
                        group_values(pc.gens_n.G.iter().map(group).collect()),
                    ),
                    ("g_1", group(&pc.gens_1.G[0])),
                    ("h_1", group(&pc.gens_1.h)),
                    ("g_3", group_values(sc.gens_3.G.iter().map(group).collect())),
                    ("h_3", group(&sc.gens_3.h)),
                    ("g_4", group_values(sc.gens_4.G.iter().map(group).collect())),
                    ("h_4", group(&sc.gens_4.h)),
                ]
                .map(|(name, value)| (Vid::from(name), value)),
            );
            (inst, gens, vars, io)
        }

        use crate::cross::{Challenges, Direction};
        use lang::id::Vid;
        use zippel::runtime::Challenger;

        // ark-spartan's older PCS omits libspartan's random-base challenge. Its
        // proof is the rho=1 specialization; do not consume a native draw for it.
        struct SpartanChallenges {
            sequence: Challenges,
            draws: usize,
            pcs_batching_index: usize,
        }
        impl SpartanChallenges {
            fn new(m: usize) -> Self {
                Self {
                    sequence: Challenges::default(),
                    draws: 0,
                    pcs_batching_index: 9 * m + 6,
                }
            }
        }
        impl Challenger<C> for SpartanChallenges {
            fn instance(&mut self, _: &V) {}
            fn message(&mut self, _: &V) {}
            fn challenge(&mut self) -> V {
                let index = self.draws;
                self.draws += 1;
                if !HAS_PCS_BATCHING && index == self.pcs_batching_index {
                    Value::Scalar(<F as backend::Field>::one())
                } else {
                    <Challenges as Challenger<C>>::challenge(&mut self.sequence)
                }
            }
        }

        fn group_values(values: Vec<V>) -> V {
            Value::vec_g1(
                values
                    .into_iter()
                    .map(|v| match v {
                        Value::G1(g) => *g,
                        _ => unreachable!("group conversion produces G1 values"),
                    })
                    .collect(),
            )
        }

        fn scalar_vec(fs: &[NativeScalar]) -> V {
            Value::vec_scalar(
                fs.iter()
                    .map(|f| match scalar(f) {
                        Value::Scalar(f) => f,
                        _ => unreachable!(),
                    })
                    .collect(),
            )
        }
        fn group_vec(gs: &[NativeGroup]) -> V {
            group_values(gs.iter().map(group).collect())
        }

        fn append_sumcheck(out: &mut Vec<V>, sc: &SumcheckProof) {
            for i in 0..sc.proofs.len() {
                let p = &sc.proofs[i];
                out.extend([
                    group(&sc.comm_polys[i]),
                    group(&sc.comm_evals[i]),
                    group(&p.delta),
                    group(&p.beta),
                    scalar_vec(&p.z),
                    scalar(&p.z_delta),
                    scalar(&p.z_beta),
                ]);
            }
        }

        fn as_zippel(p: &NativeNizk) -> Vec<V> {
            let p = &p.r1cs_sat_proof;
            let mut out = vec![group_vec(&p.comm_vars.C)];
            append_sumcheck(&mut out, &p.sc_proof_phase1);
            let (a, b, c, prod) = &p.claims_phase2;
            let (know, product) = &p.pok_claims_phase2;
            out.extend([
                group(c),
                group(&know.alpha),
                scalar(&know.z1),
                scalar(&know.z2),
                group(a),
                group(b),
                group(prod),
                group(&product.alpha),
                group(&product.beta),
                group(&product.delta),
            ]);
            out.extend(product.z.iter().map(scalar));
            out.extend([
                group(&p.proof_eq_sc_phase1.alpha),
                scalar(&p.proof_eq_sc_phase1.z),
            ]);
            append_sumcheck(&mut out, &p.sc_proof_phase2);
            out.push(group(&p.comm_vars_at_ry));
            let eval = &p.proof_eval_vars_at_ry.proof;
            let bullet = &eval.bullet_reduction_proof;
            for (l, r) in bullet.L_vec.iter().zip(&bullet.R_vec) {
                out.extend([group(l), group(r)]);
            }
            out.extend([
                group(&eval.delta),
                group(&eval.beta),
                scalar(&eval.z1),
                scalar(&eval.z2),
                group(&p.proof_eq_sc_phase2.alpha),
                scalar(&p.proof_eq_sc_phase2.z),
            ]);
            out
        }

        struct Messages<'a>(std::slice::Iter<'a, V>);
        impl Messages<'_> {
            fn group(&mut self) -> NativeGroup {
                native_group(self.0.next().expect("group message"))
            }
            fn scalar(&mut self) -> NativeScalar {
                native_scalar(self.0.next().expect("scalar message"))
            }
            fn scalars(&mut self) -> Vec<NativeScalar> {
                match self.0.next().expect("scalar vector") {
                    Value::VecScalar(fs) => fs
                        .iter()
                        .map(|f| native_scalar(&Value::Scalar(*f)))
                        .collect(),
                    v => panic!("expected scalar vector, got {v}"),
                }
            }
            fn groups(&mut self) -> Vec<NativeGroup> {
                match self.0.next().expect("group vector") {
                    Value::Vec(vs) => vs.iter().map(native_group).collect(),
                    Value::VecG1(gs) => gs.iter().map(|g| native_group(&Value::g1(*g))).collect(),
                    Value::VecG1Affine(gs) => gs
                        .iter()
                        .map(|g| native_group(&Value::g1_affine(*g)))
                        .collect(),
                    v => panic!("expected group vector, got {v}"),
                }
            }
            fn sumcheck(&mut self, m: usize) -> SumcheckProof {
                let (mut comm_polys, mut comm_evals, mut proofs) =
                    (Vec::new(), Vec::new(), Vec::new());
                for _ in 0..m {
                    comm_polys.push(self.group());
                    comm_evals.push(self.group());
                    proofs.push(DotProductProof {
                        delta: self.group(),
                        beta: self.group(),
                        z: self.scalars(),
                        z_delta: self.scalar(),
                        z_beta: self.scalar(),
                    });
                }
                SumcheckProof {
                    comm_polys,
                    comm_evals,
                    proofs,
                }
            }
        }

        fn points(m: usize) -> (Vec<NativeScalar>, Vec<NativeScalar>) {
            let mut seq = Challenges::default();
            let mut next = || native_scalar(&<Challenges as Challenger<C>>::challenge(&mut seq));
            for _ in 0..m {
                next();
            }
            let rx = (0..m)
                .map(|_| {
                    let r = next();
                    for _ in 0..3 {
                        next();
                    }
                    r
                })
                .collect();
            // Knowledge, product and equality proofs, then the A/B/C coefficients.
            for _ in 0..6 {
                next();
            }
            let ry = (0..m)
                .map(|_| {
                    let r = next();
                    for _ in 0..3 {
                        next();
                    }
                    r
                })
                .collect();
            (rx, ry)
        }

        fn as_native(messages: &[V], m: usize) -> NativeNizk {
            let mut r = Messages(messages.iter());
            let comm_vars = PolyCommitment { C: r.groups() };
            let sc_proof_phase1 = r.sumcheck(m);
            let c = r.group();
            let know = KnowledgeProof {
                alpha: r.group(),
                z1: r.scalar(),
                z2: r.scalar(),
            };
            let (a, b, prod) = (r.group(), r.group(), r.group());
            let product = ProductProof {
                alpha: r.group(),
                beta: r.group(),
                delta: r.group(),
                z: std::array::from_fn(|_| r.scalar()),
            };
            let proof_eq_sc_phase1 = EqualityProof {
                alpha: r.group(),
                z: r.scalar(),
            };
            let sc_proof_phase2 = r.sumcheck(m);
            let comm_vars_at_ry = r.group();
            let (mut ls, mut rs) = (Vec::new(), Vec::new());
            for _ in 0..m - 1 - (m - 1) / 2 {
                ls.push(r.group());
                rs.push(r.group());
            }
            let proof_eval_vars_at_ry = PolyEvalProof {
                proof: DotProductProofLog {
                    bullet_reduction_proof: BulletReductionProof {
                        L_vec: ls,
                        R_vec: rs,
                    },
                    delta: r.group(),
                    beta: r.group(),
                    z1: r.scalar(),
                    z2: r.scalar(),
                },
            };
            let proof_eq_sc_phase2 = EqualityProof {
                alpha: r.group(),
                z: r.scalar(),
            };
            assert!(r.0.next().is_none(), "unconsumed Zippel proof messages");
            NativeNizk {
                r1cs_sat_proof: R1csProof {
                    comm_vars,
                    sc_proof_phase1,
                    claims_phase2: (a, b, c, prod),
                    pok_claims_phase2: (know, product),
                    proof_eq_sc_phase1,
                    sc_proof_phase2,
                    comm_vars_at_ry,
                    proof_eval_vars_at_ry,
                    proof_eq_sc_phase2,
                },
                r: points(m),
            }
        }

        #[test]
        fn native_prove_then_zippel_verify() {
            cross_verify(Direction::NativeToZippel);
        }
        #[test]
        fn zippel_prove_then_native_verify() {
            cross_verify(Direction::ZippelToNative);
        }

        fn cross_verify(direction: Direction) {
            for m in [3usize, 4, 5] {
                let (mut inputs, products) = super::super::make_inputs::<C>(m);
                let (inst, gens, vars, io) = setup(m, &mut inputs, &products);
                let (prover, verifier) = crate::cross::compile::<C>("spartan", &[("M", m)]);
                let [az, bz, cz] = products.products();
                for (name, v) in [("az", az), ("bz", bz), ("cz", cz)] {
                    inputs.insert(Vid::from(name), Value::vec_scalar(v));
                }
                match direction {
                    Direction::NativeToZippel => {
                        let native =
                            NativeNizk::prove(&inst, vars, &io, &gens, &mut Challenges::default());
                        assert!(
                            native
                                .verify(&inst, &io, &mut Challenges::default(), &gens)
                                .is_ok()
                        );
                        let proof = as_zippel(&native);
                        assert!(
                            verifier
                                .verify_with(
                                    proof.clone(),
                                    crate::lend(&inputs),
                                    &mut SpartanChallenges::new(m)
                                )
                                .unwrap(),
                            "M={m}: Zippel rejects native proof"
                        );
                        let mut wrong = proof;
                        super::corrupt_response(&mut wrong);
                        assert!(
                            !verifier
                                .verify_with(
                                    wrong,
                                    crate::lend(&inputs),
                                    &mut SpartanChallenges::new(m)
                                )
                                .unwrap(),
                            "M={m}: Zippel accepts corrupted native proof"
                        );
                    }
                    Direction::ZippelToNative => {
                        let proof = prover
                            .prove_with(crate::lend(&inputs), &mut SpartanChallenges::new(m))
                            .unwrap();
                        let native = as_native(&proof, m);
                        assert!(
                            native
                                .verify(&inst, &io, &mut Challenges::default(), &gens)
                                .is_ok(),
                            "M={m}: native rejects Zippel proof"
                        );
                        let mut wrong = proof;
                        super::corrupt_response(&mut wrong);
                        assert!(
                            as_native(&wrong, m)
                                .verify(&inst, &io, &mut Challenges::default(), &gens)
                                .is_err(),
                            "M={m}: native accepts corrupted Zippel proof"
                        );
                    }
                }
            }
        }
    }

    mod libspartan {
        const HAS_PCS_BATCHING: bool = true;
        use crate::upstream::libspartan as native;
        use backend::{Backend, DalekRistretto as C, Field, Group, Value};
        use curve25519_dalek::ristretto::CompressedRistretto;
        type F = <C as Backend>::F;
        type G = <C as Backend>::G1;
        type V = Value<C>;
        type NativeNizk = native::NIZK;
        type NativeInstance = native::Instance;
        type NativeGens = native::NIZKGens;
        type NativeVars = native::VarsAssignment;
        type NativeInputs = native::InputsAssignment;
        type NativeGroup = CompressedRistretto;
        type NativeScalar = native::scalar::Scalar;
        use native::dense_mlpoly::{PolyCommitment, PolyEvalProof};
        use native::nizk::bullet::BulletReductionProof;
        use native::nizk::{
            DotProductProof, DotProductProofLog, EqualityProof, KnowledgeProof, ProductProof,
        };
        use native::r1csproof::R1CSProof as R1csProof;
        use native::sumcheck::ZKSumcheckInstanceProof as SumcheckProof;

        fn group(g: &NativeGroup) -> V {
            let p = curve25519_dalek_5::ristretto::CompressedRistretto(g.to_bytes())
                .decompress()
                .unwrap();
            Value::g1(backend::ff_group::FfPoint::new(p))
        }
        fn native_group(v: &V) -> NativeGroup {
            let mut bytes = Vec::new();
            match v {
                Value::G1(g) => g.write_bytes(&mut bytes),
                Value::G1Affine(g) => G::write_affine_bytes(g, &mut bytes),
                _ => panic!("expected group element, got {v}"),
            }
            CompressedRistretto(bytes.try_into().unwrap())
        }
        fn scalar(f: &NativeScalar) -> V {
            Value::Scalar(F::from_le_bytes_mod_order(&f.to_bytes()))
        }
        fn native_scalar(v: &V) -> NativeScalar {
            let mut bytes = Vec::new();
            match v {
                Value::Scalar(f) => f.write_bytes(&mut bytes),
                _ => panic!("expected scalar, got {v}"),
            }
            NativeScalar::from_bytes(&bytes.try_into().unwrap()).unwrap()
        }
        fn bytes(f: &F) -> [u8; 32] {
            let mut bytes = Vec::new();
            f.write_bytes(&mut bytes);
            bytes.try_into().unwrap()
        }

        fn setup(
            m: usize,
            inputs: &mut std::collections::HashMap<lang::id::Vid, V>,
            products: &super::super::MatVec<F>,
        ) -> (NativeInstance, NativeGens, NativeVars, NativeInputs) {
            let n = 1 << m;
            let nw = n / 2;
            let mats = products.mats.each_ref().map(|mat| {
                mat.iter()
                    .map(|&(r, c, f)| (r, c, bytes(&f)))
                    .collect::<Vec<_>>()
            });
            let inst = NativeInstance::new(n, nw, nw - 1, &mats[0], &mats[1], &mats[2]).unwrap();
            let vars =
                NativeVars::new(&products.z[..nw].iter().map(bytes).collect::<Vec<_>>()).unwrap();
            let io = NativeInputs::new(&products.z[nw + 1..].iter().map(bytes).collect::<Vec<_>>())
                .unwrap();
            assert!(inst.is_sat(&vars, &io).unwrap());
            let gens = NativeGens::new(n, nw, nw - 1);
            let pc = &gens.gens_r1cs_sat.gens_pc.gens;
            let sc = &gens.gens_r1cs_sat.gens_sc;
            inputs.extend(
                [
                    (
                        "g_vec_w",
                        group_values(pc.gens_n.G.iter().map(|g| group(&g.compress())).collect()),
                    ),
                    ("g_1", group(&pc.gens_1.G[0].compress())),
                    ("h_1", group(&pc.gens_1.h.compress())),
                    (
                        "g_3",
                        group_values(sc.gens_3.G.iter().map(|g| group(&g.compress())).collect()),
                    ),
                    ("h_3", group(&sc.gens_3.h.compress())),
                    (
                        "g_4",
                        group_values(sc.gens_4.G.iter().map(|g| group(&g.compress())).collect()),
                    ),
                    ("h_4", group(&sc.gens_4.h.compress())),
                ]
                .map(|(name, value)| (Vid::from(name), value)),
            );
            (inst, gens, vars, io)
        }

        use crate::cross::{Challenges, Direction};
        use lang::id::Vid;
        use zippel::runtime::Challenger;

        // ark-spartan's older PCS omits libspartan's random-base challenge. Its
        // proof is the rho=1 specialization; do not consume a native draw for it.
        struct SpartanChallenges {
            sequence: Challenges,
            draws: usize,
            pcs_batching_index: usize,
        }
        impl SpartanChallenges {
            fn new(m: usize) -> Self {
                Self {
                    sequence: Challenges::default(),
                    draws: 0,
                    pcs_batching_index: 9 * m + 6,
                }
            }
        }
        impl Challenger<C> for SpartanChallenges {
            fn instance(&mut self, _: &V) {}
            fn message(&mut self, _: &V) {}
            fn challenge(&mut self) -> V {
                let index = self.draws;
                self.draws += 1;
                if !HAS_PCS_BATCHING && index == self.pcs_batching_index {
                    Value::Scalar(<F as backend::Field>::one())
                } else {
                    <Challenges as Challenger<C>>::challenge(&mut self.sequence)
                }
            }
        }

        fn group_values(values: Vec<V>) -> V {
            Value::vec_g1(
                values
                    .into_iter()
                    .map(|v| match v {
                        Value::G1(g) => *g,
                        _ => unreachable!("group conversion produces G1 values"),
                    })
                    .collect(),
            )
        }

        fn scalar_vec(fs: &[NativeScalar]) -> V {
            Value::vec_scalar(
                fs.iter()
                    .map(|f| match scalar(f) {
                        Value::Scalar(f) => f,
                        _ => unreachable!(),
                    })
                    .collect(),
            )
        }
        fn group_vec(gs: &[NativeGroup]) -> V {
            group_values(gs.iter().map(group).collect())
        }

        fn append_sumcheck(out: &mut Vec<V>, sc: &SumcheckProof) {
            for i in 0..sc.proofs.len() {
                let p = &sc.proofs[i];
                out.extend([
                    group(&sc.comm_polys[i]),
                    group(&sc.comm_evals[i]),
                    group(&p.delta),
                    group(&p.beta),
                    scalar_vec(&p.z),
                    scalar(&p.z_delta),
                    scalar(&p.z_beta),
                ]);
            }
        }

        fn as_zippel(p: &NativeNizk) -> Vec<V> {
            let p = &p.r1cs_sat_proof;
            let mut out = vec![group_vec(&p.comm_vars.C)];
            append_sumcheck(&mut out, &p.sc_proof_phase1);
            let (a, b, c, prod) = &p.claims_phase2;
            let (know, product) = &p.pok_claims_phase2;
            out.extend([
                group(c),
                group(&know.alpha),
                scalar(&know.z1),
                scalar(&know.z2),
                group(a),
                group(b),
                group(prod),
                group(&product.alpha),
                group(&product.beta),
                group(&product.delta),
            ]);
            out.extend(product.z.iter().map(scalar));
            out.extend([
                group(&p.proof_eq_sc_phase1.alpha),
                scalar(&p.proof_eq_sc_phase1.z),
            ]);
            append_sumcheck(&mut out, &p.sc_proof_phase2);
            out.push(group(&p.comm_vars_at_ry));
            let eval = &p.proof_eval_vars_at_ry.proof;
            let bullet = &eval.bullet_reduction_proof;
            for (l, r) in bullet.L_vec.iter().zip(&bullet.R_vec) {
                out.extend([group(l), group(r)]);
            }
            out.extend([
                group(&eval.delta),
                group(&eval.beta),
                scalar(&eval.z1),
                scalar(&eval.z2),
                group(&p.proof_eq_sc_phase2.alpha),
                scalar(&p.proof_eq_sc_phase2.z),
            ]);
            out
        }

        struct Messages<'a>(std::slice::Iter<'a, V>);
        impl Messages<'_> {
            fn group(&mut self) -> NativeGroup {
                native_group(self.0.next().expect("group message"))
            }
            fn scalar(&mut self) -> NativeScalar {
                native_scalar(self.0.next().expect("scalar message"))
            }
            fn scalars(&mut self) -> Vec<NativeScalar> {
                match self.0.next().expect("scalar vector") {
                    Value::VecScalar(fs) => fs
                        .iter()
                        .map(|f| native_scalar(&Value::Scalar(*f)))
                        .collect(),
                    v => panic!("expected scalar vector, got {v}"),
                }
            }
            fn groups(&mut self) -> Vec<NativeGroup> {
                match self.0.next().expect("group vector") {
                    Value::Vec(vs) => vs.iter().map(native_group).collect(),
                    Value::VecG1(gs) => gs.iter().map(|g| native_group(&Value::g1(*g))).collect(),
                    Value::VecG1Affine(gs) => gs
                        .iter()
                        .map(|g| native_group(&Value::g1_affine(*g)))
                        .collect(),
                    v => panic!("expected group vector, got {v}"),
                }
            }
            fn sumcheck(&mut self, m: usize) -> SumcheckProof {
                let (mut comm_polys, mut comm_evals, mut proofs) =
                    (Vec::new(), Vec::new(), Vec::new());
                for _ in 0..m {
                    comm_polys.push(self.group());
                    comm_evals.push(self.group());
                    proofs.push(DotProductProof {
                        delta: self.group(),
                        beta: self.group(),
                        z: self.scalars(),
                        z_delta: self.scalar(),
                        z_beta: self.scalar(),
                    });
                }
                SumcheckProof {
                    comm_polys,
                    comm_evals,
                    proofs,
                }
            }
        }

        fn points(m: usize) -> (Vec<NativeScalar>, Vec<NativeScalar>) {
            let mut seq = Challenges::default();
            let mut next = || native_scalar(&<Challenges as Challenger<C>>::challenge(&mut seq));
            for _ in 0..m {
                next();
            }
            let rx = (0..m)
                .map(|_| {
                    let r = next();
                    for _ in 0..3 {
                        next();
                    }
                    r
                })
                .collect();
            // Knowledge, product and equality proofs, then the A/B/C coefficients.
            for _ in 0..6 {
                next();
            }
            let ry = (0..m)
                .map(|_| {
                    let r = next();
                    for _ in 0..3 {
                        next();
                    }
                    r
                })
                .collect();
            (rx, ry)
        }

        fn as_native(messages: &[V], m: usize) -> NativeNizk {
            let mut r = Messages(messages.iter());
            let comm_vars = PolyCommitment { C: r.groups() };
            let sc_proof_phase1 = r.sumcheck(m);
            let c = r.group();
            let know = KnowledgeProof {
                alpha: r.group(),
                z1: r.scalar(),
                z2: r.scalar(),
            };
            let (a, b, prod) = (r.group(), r.group(), r.group());
            let product = ProductProof {
                alpha: r.group(),
                beta: r.group(),
                delta: r.group(),
                z: std::array::from_fn(|_| r.scalar()),
            };
            let proof_eq_sc_phase1 = EqualityProof {
                alpha: r.group(),
                z: r.scalar(),
            };
            let sc_proof_phase2 = r.sumcheck(m);
            let comm_vars_at_ry = r.group();
            let (mut ls, mut rs) = (Vec::new(), Vec::new());
            for _ in 0..m - 1 - (m - 1) / 2 {
                ls.push(r.group());
                rs.push(r.group());
            }
            let proof_eval_vars_at_ry = PolyEvalProof {
                proof: DotProductProofLog {
                    bullet_reduction_proof: BulletReductionProof {
                        L_vec: ls,
                        R_vec: rs,
                    },
                    delta: r.group(),
                    beta: r.group(),
                    z1: r.scalar(),
                    z2: r.scalar(),
                },
            };
            let proof_eq_sc_phase2 = EqualityProof {
                alpha: r.group(),
                z: r.scalar(),
            };
            assert!(r.0.next().is_none(), "unconsumed Zippel proof messages");
            NativeNizk {
                r1cs_sat_proof: R1csProof {
                    comm_vars,
                    sc_proof_phase1,
                    claims_phase2: (a, b, c, prod),
                    pok_claims_phase2: (know, product),
                    proof_eq_sc_phase1,
                    sc_proof_phase2,
                    comm_vars_at_ry,
                    proof_eval_vars_at_ry,
                    proof_eq_sc_phase2,
                },
                r: points(m),
            }
        }

        #[test]
        fn native_prove_then_zippel_verify() {
            cross_verify(Direction::NativeToZippel);
        }
        #[test]
        fn zippel_prove_then_native_verify() {
            cross_verify(Direction::ZippelToNative);
        }

        fn cross_verify(direction: Direction) {
            for m in [3usize, 4, 5] {
                let (mut inputs, products) = super::super::make_inputs::<C>(m);
                let (inst, gens, vars, io) = setup(m, &mut inputs, &products);
                let (prover, verifier) = crate::cross::compile::<C>("spartan", &[("M", m)]);
                let [az, bz, cz] = products.products();
                for (name, v) in [("az", az), ("bz", bz), ("cz", cz)] {
                    inputs.insert(Vid::from(name), Value::vec_scalar(v));
                }
                match direction {
                    Direction::NativeToZippel => {
                        let native =
                            NativeNizk::prove(&inst, vars, &io, &gens, &mut Challenges::default());
                        assert!(
                            native
                                .verify(&inst, &io, &mut Challenges::default(), &gens)
                                .is_ok()
                        );
                        let proof = as_zippel(&native);
                        assert!(
                            verifier
                                .verify_with(
                                    proof.clone(),
                                    crate::lend(&inputs),
                                    &mut SpartanChallenges::new(m)
                                )
                                .unwrap(),
                            "M={m}: Zippel rejects native proof"
                        );
                        let mut wrong = proof;
                        super::corrupt_response(&mut wrong);
                        assert!(
                            !verifier
                                .verify_with(
                                    wrong,
                                    crate::lend(&inputs),
                                    &mut SpartanChallenges::new(m)
                                )
                                .unwrap(),
                            "M={m}: Zippel accepts corrupted native proof"
                        );
                    }
                    Direction::ZippelToNative => {
                        let proof = prover
                            .prove_with(crate::lend(&inputs), &mut SpartanChallenges::new(m))
                            .unwrap();
                        let native = as_native(&proof, m);
                        assert!(
                            native
                                .verify(&inst, &io, &mut Challenges::default(), &gens)
                                .is_ok(),
                            "M={m}: native rejects Zippel proof"
                        );
                        let mut wrong = proof;
                        super::corrupt_response(&mut wrong);
                        assert!(
                            as_native(&wrong, m)
                                .verify(&inst, &io, &mut Challenges::default(), &gens)
                                .is_err(),
                            "M={m}: native accepts corrupted Zippel proof"
                        );
                    }
                }
            }
        }
    }
}
