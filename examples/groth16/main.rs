use ark_ec::PrimeGroup;
use ark_ff::{Field, One, UniformRand};
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::{Tid, Vid};
use share::Ctx;

use crate::common::{self, size};

type C = ArkBls12_381;
type F = <C as ArkConfig>::F;

pub fn spec() -> common::ExampleSpec<C> {
    common::ExampleSpec {
        source: "examples/groth16/groth16.zippel",
        defaults: &[("M", 2), ("L", 3), ("H", 4)],
        validate: None,
        make_inputs,
        analyses: &[],
    }
}

// Sample the trusted-setup relation in groth16.zippel directly. Choosing the
// constant assignment first lets us solve one c evaluation for the QAP identity.
fn make_inputs(sizes: &Ctx<Tid, usize>) -> Ctx<Vid, Value<C>> {
    let mut rng = rand::rngs::OsRng;
    let (m, l, h) = (size(sizes, "M"), size(sizes, "L"), size(sizes, "H"));
    let mut nonzero = || loop {
        let x = F::rand(&mut rng);
        if let Some(inv) = x.inverse() {
            break (x, inv);
        }
    };
    let (gamma, gamma_inv) = nonzero();
    let (delta, delta_inv) = nonzero();
    let alpha = F::rand(&mut rng);
    let beta = F::rand(&mut rng);
    let tau = F::rand(&mut rng);
    let t = F::rand(&mut rng);
    let mut assignment: Vec<F> = (0..m + l).map(|_| F::rand(&mut rng)).collect();
    assignment[0] = F::one();
    let a: Vec<F> = (0..m + l).map(|_| F::rand(&mut rng)).collect();
    let b: Vec<F> = (0..m + l).map(|_| F::rand(&mut rng)).collect();
    let mut c: Vec<F> = (0..m + l).map(|_| F::rand(&mut rng)).collect();
    let h_coeffs: Vec<F> = (0..h).map(|_| F::rand(&mut rng)).collect();
    let dot = |xs: &[F], ys: &[F]| xs.iter().zip(ys).map(|(x, y)| *x * y).sum::<F>();
    let powers: Vec<F> = (0..h).map(|j| tau.pow([j as u64])).collect();
    c[0] = dot(&a, &assignment) * dot(&b, &assignment)
        - dot(&h_coeffs, &powers) * t
        - dot(&c[1..], &assignment[1..]);
    let g1 = <C as ArkConfig>::G1::generator();
    let g2 = <C as ArkConfig>::G2::generator();
    let combined: Vec<F> = (0..m + l)
        .map(|i| beta * a[i] + alpha * b[i] + c[i])
        .collect();
    [
        ("gen_g1", Value::g1(g1)),
        ("gen_g2", Value::g2(g2)),
        ("alpha_g1", Value::g1(g1 * alpha)),
        ("beta_g1", Value::g1(g1 * beta)),
        ("beta_g2", Value::g2(g2 * beta)),
        ("gamma_g2", Value::g2(g2 * gamma)),
        ("delta_g1", Value::g1(g1 * delta)),
        ("delta_g2", Value::g2(g2 * delta)),
        (
            "gamma_abc_g1",
            Value::vec_g1(
                combined[..m]
                    .iter()
                    .map(|x| g1 * (*x * gamma_inv))
                    .collect(),
            ),
        ),
        (
            "l_query",
            Value::vec_g1(
                combined[m..]
                    .iter()
                    .map(|x| g1 * (*x * delta_inv))
                    .collect(),
            ),
        ),
        ("a_query", Value::vec_g1(a.iter().map(|x| g1 * x).collect())),
        (
            "b_g1_query",
            Value::vec_g1(b.iter().map(|x| g1 * x).collect()),
        ),
        (
            "b_g2_query",
            Value::vec_g2(b.iter().map(|x| g2 * x).collect()),
        ),
        (
            "h_query",
            Value::vec_g1(powers.iter().map(|x| g1 * (*x * t * delta_inv)).collect()),
        ),
        (
            "instance_assignment",
            Value::vec_scalar(assignment[..m].to_vec()),
        ),
        (
            "witness_assignment",
            Value::vec_scalar(assignment[m..].to_vec()),
        ),
        ("h_coeffs", Value::vec_scalar(h_coeffs)),
    ]
    .into_iter()
    .map(|(name, value)| (Vid::new(name), value))
    .collect()
}
