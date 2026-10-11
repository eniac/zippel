use ark_ff::{Field, Zero};
use ark_std::UniformRand;
use backend::{ArkConfig, ArkCurve25519, PolyVariant, Value, VirtualPolynomial};
use lang::id::{Tid, Vid};
use rand::Rng;
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

use crate::common;

/// Spartan-NIZK with 2^M R1CS constraints
#[derive(clap::Args)]
pub struct Args {
    /// Log2 of the number of constraints (M >= 3)
    #[arg(value_name = "M", default_value_t = 3, value_parser = parse_m)]
    m: usize,
}

fn parse_m(value: &str) -> Result<usize, String> {
    let m = value.parse().map_err(|_| "M must be an integer")?;
    if m < 3 {
        return Err("M must be >= 3 (Hyrax needs M-1 >= 2 to split L,M_h both >= 1)".into());
    }
    Ok(m)
}

pub fn run(args: &Args, _opts: &common::RunOptions) {
    let m = args.m;
    println!("=== Spartan-NIZK (PIOP + Hyrax PCS, ArkCurve25519, M={m}) ===");
    let zippel_args = ZippelArgs::new(PathBuf::from("examples/spartan/spartan.zippel"));
    let mut handler: ZippelHandler<ArkCurve25519> = ZippelHandler::new(zippel_args);
    let mut sizes = Ctx::new();
    sizes.insert(&Tid::new("M"), &m);
    handler.compile(&sizes);

    common::run_prover_and_verify(&mut handler, prover_create_inputs(m));
}

const fn hyrax_split(m: usize) -> (usize, usize) {
    let nw = m - 1;
    let l = nw / 2;
    let m_h = nw - l;
    (l, m_h)
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
    const K_NNZ_PER_ROW: usize = 1;
    let num_vars = w.len() + io.len() + 1;
    assert_eq!(num_vars, m, "z = w ++ io ++ [1] must have length m");

    let mut z = Vec::with_capacity(m);
    z.extend_from_slice(w);
    z.extend_from_slice(io);
    z.push(F::from(1u64));

    let const_col = m - 1;
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

fn prover_create_inputs(m: usize) -> Ctx<Vid, Value<ArkCurve25519>> {
    type F = <ArkCurve25519 as ArkConfig>::F;
    type G1 = <ArkCurve25519 as ArkConfig>::G1;
    use ark_ec::CurveGroup;

    let num_cons = 1usize << m;
    let witness_len = 1usize << (m - 1);
    let io_len = witness_len - 1;
    let (_l, m_h) = hyrax_split(m);
    let ncols = 1usize << m_h;

    let mut rng = rand::rngs::OsRng;
    let one = F::from(1u64);

    let witness: Vec<F> = (0..witness_len).map(|_| F::rand(&mut rng)).collect();
    let instance: Vec<F> = (0..io_len).map(|_| F::rand(&mut rng)).collect();

    let r1cs = random_r1cs::<F, _>(&mut rng, num_cons, &witness, &instance);

    let mut z: Vec<F> = Vec::with_capacity(num_cons);
    z.extend_from_slice(&witness);
    z.extend_from_slice(&instance);
    z.push(one);

    let mut az: Vec<F> = vec![F::from(0u64); num_cons];
    let mut bz: Vec<F> = vec![F::from(0u64); num_cons];
    let mut cz: Vec<F> = vec![F::from(0u64); num_cons];
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
            "row {i} of random R1CS is unsatisfied"
        );
    }

    let triples_to_mle_evals = |triples: &[(usize, usize, F)]| -> Vec<(usize, F)> {
        triples
            .iter()
            .filter(|(_, _, v)| !v.is_zero())
            .map(|(i, c, v)| (c * num_cons + i, *v))
            .collect()
    };
    let two_m_vars = 2 * m;
    let mk_sparse_mle = |evals: Vec<(usize, F)>| {
        Value::poly(VirtualPolynomial::from_poly(PolyVariant::SparseMle {
            num_vars: two_m_vars,
            evals,
        }))
    };
    let mat_a_t = mk_sparse_mle(triples_to_mle_evals(&r1cs.mat_a));
    let mat_b_t = mk_sparse_mle(triples_to_mle_evals(&r1cs.mat_b));
    let mat_c_t = mk_sparse_mle(triples_to_mle_evals(&r1cs.mat_c));

    let g_vec_proj: Vec<G1> = (0..ncols).map(|_| G1::rand(&mut rng)).collect();
    let g_vec_aff = G1::normalize_batch(&g_vec_proj);
    let g_base_w = G1::rand(&mut rng);
    let h_base_w = G1::rand(&mut rng);

    let g_evs_d3_proj: Vec<G1> = (0..4).map(|_| G1::rand(&mut rng)).collect();
    let g_evs_d3_aff = G1::normalize_batch(&g_evs_d3_proj);
    let g_evs_d2_proj: Vec<G1> = (0..3).map(|_| G1::rand(&mut rng)).collect();
    let g_evs_d2_aff = G1::normalize_batch(&g_evs_d2_proj);
    let h_evs = G1::rand(&mut rng);

    let placeholder_tau: Vec<F> = vec![F::from(0u64); m];

    Ctx::<Vid, Value<ArkCurve25519>>::from_iter([
        (Vid("mat_a_t".to_string()), mat_a_t),
        (Vid("mat_b_t".to_string()), mat_b_t),
        (Vid("mat_c_t".to_string()), mat_c_t),
        (Vid("io".to_string()), Value::vec_scalar(r1cs.io)),
        (Vid("w".to_string()), Value::vec_scalar(r1cs.w)),
        (Vid("az".to_string()), Value::vec_scalar(az)),
        (Vid("bz".to_string()), Value::vec_scalar(bz)),
        (Vid("cz".to_string()), Value::vec_scalar(cz)),
        (Vid("g_vec_w".to_string()), Value::vec_g1_affine(g_vec_aff)),
        (Vid("g_base_w".to_string()), Value::g1(g_base_w)),
        (Vid("h_base_w".to_string()), Value::g1(h_base_w)),
        (
            Vid("g_evs_d3".to_string()),
            Value::vec_g1_affine(g_evs_d3_aff),
        ),
        (
            Vid("g_evs_d2".to_string()),
            Value::vec_g1_affine(g_evs_d2_aff),
        ),
        (Vid("h_evs".to_string()), Value::g1(h_evs)),
        (
            Vid("placeholder_tau".to_string()),
            Value::vec_scalar(placeholder_tau),
        ),
    ])
}
