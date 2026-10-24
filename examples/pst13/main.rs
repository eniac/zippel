use ark_std::One;
use ark_std::UniformRand;
use backend::{ArkBls12_381, Backend, Value};
use lang::id::Vid;
use share::Ctx;

use crate::common;
use crate::common::size;

fn make_inputs(sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkBls12_381>> {
    let n = size(sizes, "N");

    let mut rng = rand::rngs::OsRng;
    let size = 1usize << n;

    let gen_g = <ArkBls12_381 as Backend>::G1::rand(&mut rng);
    let gen_h = <ArkBls12_381 as Backend>::G2::rand(&mut rng);

    let one = <ArkBls12_381 as Backend>::F::one();
    let alpha: Vec<_> = (0..n)
        .map(|_| <ArkBls12_381 as Backend>::F::rand(&mut rng))
        .collect();
    let one_m_alpha: Vec<_> = alpha.iter().map(|a| one - a).collect();

    let ck_n_scalars: Vec<_> = (0..size)
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
    let ck_n = Value::vec_g1(ck_n_scalars.iter().map(|s| gen_g * s).collect());

    let p_scalars: Vec<_> = (0..size)
        .map(|_| <ArkBls12_381 as Backend>::F::rand(&mut rng))
        .collect();
    let p = Value::vec_scalar(p_scalars.clone());

    let z_scalars: Vec<_> = (0..n)
        .map(|_| <ArkBls12_381 as Backend>::F::rand(&mut rng))
        .collect();
    let z = Value::vec_scalar(z_scalars.clone());

    let y_val = (0..size).fold(<ArkBls12_381 as Backend>::F::from(0u64), |acc, i| {
        let eq_z_i = (0..n).fold(one, |prod, j| {
            let bit = (i >> (n - 1 - j)) & 1;
            if bit == 1 {
                prod * z_scalars[j]
            } else {
                prod * (one - z_scalars[j])
            }
        });
        acc + p_scalars[i] * eq_z_i
    });
    let y = Value::Scalar(y_val);

    let alpha_h = Value::vec_g2(alpha.iter().map(|a| gen_h * a).collect());

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("p".to_string()), p),
        (Vid("z".to_string()), z),
        (Vid("y".to_string()), y),
        (Vid("ck_N".to_string()), ck_n),
        (Vid("g_gen".to_string()), Value::g1(gen_g)),
        (Vid("h_gen".to_string()), Value::g2(gen_h)),
        (Vid("alpha_H".to_string()), alpha_h),
        (Vid("alpha".to_string()), Value::vec_scalar(alpha)),
    ])
}

pub fn spec() -> common::ExampleSpec<ArkBls12_381> {
    common::ExampleSpec {
        source: "examples/pst13/pst13.zippel",
        defaults: &[("N", 2)],
        validate: Some(|sizes, _analysis| {
            common::check_power_of_two(sizes, "N")?;
            Ok(())
        }),
        make_inputs,
        analyses: &[
            common::Analysis::Completeness,
            common::Analysis::Zk,
            common::Analysis::Soundness(&[2]),
        ],
    }
}
