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
use std::time::Instant;
use zippel::{ZippelArgs, ZippelHandler, check_verification, proof_size_bytes};

pub const DEFAULT_M: usize = 8;

pub fn hyrax_split(m: usize) -> (usize, usize) {
    let nw = m - 1;
    let l = nw / 2;
    let m_h = nw - l;
    (l, m_h)
}

pub struct ZippelTiming {
    pub prove: std::time::Duration,
    pub verify: std::time::Duration,
    pub proof_bytes: usize,
    pub passed: bool,
}

pub struct Setup {
    m: usize,
    handler: ZippelHandler<ArkCurve25519>,
    inputs: Ctx<Vid, Value<ArkCurve25519>>,
    compile_time: std::time::Duration,
}

impl Setup {
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

        let compile_start = Instant::now();
        let args = ZippelArgs::new(zippel_path);
        let mut handler: ZippelHandler<ArkCurve25519> = ZippelHandler::new(args);
        let mut sizes = Ctx::new();
        sizes.insert(&Tid::new("M"), &m);
        handler.compile(&sizes);
        let compile_time = compile_start.elapsed();

        Setup {
            m,
            handler,
            inputs,
            compile_time,
        }
    }

    pub fn compile_time(&self) -> std::time::Duration {
        self.compile_time
    }

    pub fn time_protocol(&mut self) -> ZippelTiming {
        let mut prove_sum = std::time::Duration::ZERO;
        let mut last_proof = None;
        for _ in 0..*crate::PROVER_SAMPLES {
            let inputs_c = self.inputs.clone();
            let t = Instant::now();
            let proof = self
                .handler
                .run_prover(&inputs_c)
                .expect("zippel spartan prover failed");
            prove_sum += t.elapsed();
            last_proof = Some(proof);
        }
        let prove = prove_sum / *crate::PROVER_SAMPLES;
        let proof = last_proof.expect("PROVER_SAMPLES > 0");
        let proof_bytes = proof_size_bytes::<ArkCurve25519>(&proof);
        let mut verify_sum = std::time::Duration::ZERO;
        let mut last_result = None;
        for _ in 0..crate::VERIFY_SAMPLES {
            let proof_c = proof.clone();
            let t = Instant::now();
            let verifier_result = self
                .handler
                .run_verifier(&proof_c, &self.inputs)
                .expect("zippel spartan verifier failed");
            verify_sum += t.elapsed();
            last_result = Some(verifier_result);
        }
        let verify = verify_sum / crate::VERIFY_SAMPLES;
        let passed = check_verification(&last_result.expect("VERIFY_SAMPLES > 0"));

        ZippelTiming {
            prove,
            verify,
            proof_bytes,
            passed,
        }
    }

    pub fn timing(&mut self) -> Timing {
        let t = self.time_protocol();
        Timing {
            prove: t.prove,
            verify: t.verify,
        }
    }

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

        let az_i: F = a_cols.iter().zip(a_vals.iter()).map(|(c, v)| z[*c] * *v).sum();
        let bz_i: F = b_cols.iter().zip(b_vals.iter()).map(|(c, v)| z[*c] * *v).sum();
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

fn prover_create_inputs(m: usize) -> Ctx<Vid, Value<ArkCurve25519>> {
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
        assert_eq!(az[i] * bz[i], cz[i], "row {i} of synthetic R1CS is unsatisfied");
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

    Ctx::<Vid, Value<ArkCurve25519>>::from_iter([
        (Vid("mat_a_t".to_string()), mat_a_t),
        (Vid("mat_b_t".to_string()), mat_b_t),
        (Vid("mat_c_t".to_string()), mat_c_t),
        (Vid("io".to_string()), Value::VecScalar(r1cs.io)),
        (Vid("w".to_string()), Value::VecScalar(r1cs.w)),
        (Vid("az".to_string()), Value::VecScalar(az)),
        (Vid("bz".to_string()), Value::VecScalar(bz)),
        (Vid("cz".to_string()), Value::VecScalar(cz)),
        (Vid("g_vec_w".to_string()), Value::VecG1Affine(g_vec_aff)),
        (Vid("g_base_w".to_string()), Value::G1(g_base_w)),
        (Vid("h_base_w".to_string()), Value::G1(h_base_w)),
        (Vid("g_evs_d3".to_string()), Value::VecG1Affine(g_evs_d3_aff)),
        (Vid("g_evs_d2".to_string()), Value::VecG1Affine(g_evs_d2_aff)),
        (Vid("h_evs".to_string()), Value::G1(h_evs)),
        (Vid("placeholder_tau".to_string()), Value::VecScalar(placeholder_tau)),
        (Vid("f_one".to_string()), Value::Scalar(one)),
    ])
}
