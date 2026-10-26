use ark_ff::{Field, One, UniformRand, Zero};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_std::test_rng;
use backend::{ArkBls12_381, Backend, Value};
use lang::id::Vid;
use share::Ctx;

use crate::common;
use crate::common::size;

type C = ArkBls12_381;
type F = <C as Backend>::F;
type G1 = <C as Backend>::G1;
type G2 = <C as Backend>::G2;

fn make_inputs(sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<C>> {
    let n_size = size(sizes, "n");
    let b_size = size(sizes, "b");
    let l_chunk = size(sizes, "l_chunk");
    let h_deg = (b_size - 1) * n_size;

    let mut rng = test_rng();

    // 1. Setup generators & trapdoors
    let gen_g1 = G1::rand(&mut rng);
    let gen_g2 = G2::rand(&mut rng);
    let tau = F::rand(&mut rng);
    let xi = F::rand(&mut rng);

    let srs_g2_tau = gen_g2 * tau;
    let srs_g2_xi = gen_g2 * xi;
    let xi_g1 = gen_g1 * xi;

    // 2. SRS in G1: monomial [τ^i]_1 for the quotients, Lagrange [ℓ_i(τ)]_1
    //    over the size-(n+1) domain for the commitments to f and the digits.
    let domain_s = GeneralEvaluationDomain::<F>::new(n_size + 1).unwrap();
    let tau_pows: Vec<F> = (0..=n_size).map(|i| tau.pow([i as u64])).collect();
    let srs_g1_lagr_vec: Vec<G1> = domain_s
        .ifft(&tau_pows)
        .iter()
        .map(|l| gen_g1 * l)
        .collect();

    let mut srs_g1_h_vec = Vec::new();
    let mut current_tau = F::one();
    for _ in 0..=h_deg {
        srs_g1_h_vec.push(gen_g1 * current_tau);
        current_tau *= tau;
    }

    // Small radix-b digits keep witnesses in range without overflowing u64.
    let z_vals: Vec<u64> = (0..n_size).map(|i| (i % b_size) as u64).collect();
    let mut f_evals = vec![F::zero()];
    for z in &z_vals {
        f_evals.push(F::from(*z));
    }

    // Decompose values into radix-b digits (the prover blinds f_j(ω^0) itself)
    let mut chunks_bits = Vec::new();
    let mut remaining = z_vals;
    for _ in 0..l_chunk {
        let digits = remaining
            .iter_mut()
            .map(|z| {
                let digit = *z % b_size as u64;
                *z /= b_size as u64;
                F::from(digit)
            })
            .collect();
        chunks_bits.push(Value::vec_scalar(digits));
    }

    // Commitment randomness of the statement
    let rho = F::rand(&mut rng);

    // Range constants
    let mut b_pow = Vec::new();
    let mut current_pow = F::one();
    let b_scalar = F::from(b_size as u64);
    for _ in 0..l_chunk {
        b_pow.push(current_pow);
        current_pow *= b_scalar;
    }

    // 4. s0_commit commits to the Lagrange polynomial L_0: [ℓ_0(τ)]_1
    let s0_commit = srs_g1_lagr_vec[0];

    // 5. Statement: com_f = Σ_i f(ω^i)·[ℓ_i(τ)]_1 + ρ·[ξ]_1
    let mut com_f = xi_g1 * rho;
    for (v, g) in f_evals.iter().zip(srs_g1_lagr_vec.iter()) {
        com_f += *g * *v;
    }

    Ctx::<Vid, Value<C>>::from_iter([
        (Vid("f_evals".to_string()), Value::vec_scalar(f_evals)),
        (
            Vid("chunks_bits".to_string()),
            Value::Vec(chunks_bits.into()),
        ),
        (Vid("rho".to_string()), Value::Scalar(rho)),
        (Vid("com_f".to_string()), Value::g1(com_f)),
        (Vid("b_pow".to_string()), Value::vec_scalar(b_pow.clone())),
        (Vid("gen_g1".to_string()), Value::g1(gen_g1)),
        (Vid("gen_g2".to_string()), Value::g2(gen_g2)),
        (Vid("srs_g2_tau".to_string()), Value::g2(srs_g2_tau)),
        (Vid("srs_g2_xi".to_string()), Value::g2(srs_g2_xi)),
        (Vid("xi_g1".to_string()), Value::g1(xi_g1)),
        (Vid("s0_commit".to_string()), Value::g1(s0_commit)),
        (
            Vid("srs_g1_lagr".to_string()),
            Value::vec_g1(srs_g1_lagr_vec),
        ),
        (Vid("srs_g1_h".to_string()), Value::vec_g1(srs_g1_h_vec)),
        (
            Vid("v_star".to_string()),
            Value::vec_scalar(vec![F::one(); n_size + 1]),
        ),
    ])
}

pub fn spec() -> common::ExampleSpec<ArkBls12_381> {
    common::ExampleSpec {
        source: "examples/dekart/dekart.zippel",
        run_defaults: &[("n", 4095), ("b", 2), ("l_chunk", 16)],
        analysis_defaults: &[("n", 3), ("b", 2), ("l_chunk", 1)],
        validate: Some(|sizes, analysis| {
            if analysis {
                return Ok(());
            }
            let domain_size = size(sizes, "n")
                .checked_add(1)
                .ok_or("n+1 overflows the evaluation domain")?;
            if GeneralEvaluationDomain::<F>::new(domain_size)
                .is_none_or(|d| d.size() != domain_size)
            {
                return Err("n+1 must be an exact supported evaluation-domain size".into());
            }
            if size(sizes, "b") < 2 {
                return Err("b must be >= 2 for digit decomposition".into());
            }
            Ok(())
        }),
        make_inputs,
        analyses: &[common::Analysis::Completeness],
    }
}
