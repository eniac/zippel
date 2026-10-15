use ark_ff::fields::Field;
use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;

use crate::common;
use crate::common::size;

fn make_inputs(sizes: &Ctx<lang::id::Tid, usize>) -> Ctx<Vid, Value<ArkBls12_381>> {
    let n_size = size(sizes, "N");
    let m_size = size(sizes, "M");

    assert!(n_size >= 2, "n_size must be at least 2");
    assert!(m_size >= 1, "m_size must be at least 1");
    let mut rng = rand::rngs::OsRng;
    let s_size = size(sizes, "S");

    let g_input = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);
    let g: Value<ArkBls12_381> = Value::g1(g_input);

    let h_input = <ArkBls12_381 as ArkConfig>::G2::rand(&mut rng);
    let h: Value<ArkBls12_381> = Value::g2(h_input);

    let tau_input = <ArkBls12_381 as ArkConfig>::F::rand(&mut rng);

    // SRS G1 up to size S
    let ss_g: Value<ArkBls12_381> = Value::vec_g1((0..s_size).map(|_| g_input).collect());
    let ss_index = Value::vec_scalar((0..s_size).map(|i| tau_input.pow([i as u64])).collect());
    let ss = ss_g * ss_index;

    // SRS G2_s
    let h_val: Value<ArkBls12_381> = Value::g2(h_input * tau_input);

    // Set S of size M (choose 0, 1, 2, ..., M-1)
    let s_val = Value::vec_scalar(
        (0..m_size)
            .map(|i| <ArkBls12_381 as ArkConfig>::F::from(i as u64))
            .collect(),
    );

    // f_coeffs. Constant term must be one of the elements of S (we choose S[0] which is 0).
    let mut f_coeffs_vec = vec![<ArkBls12_381 as ArkConfig>::F::from(0u64)];
    for _ in 1..n_size {
        f_coeffs_vec.push(<ArkBls12_381 as ArkConfig>::F::rand(&mut rng));
    }
    let f_coeffs = Value::vec_scalar(f_coeffs_vec);

    Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("f_coeffs".to_string()), f_coeffs),
        (Vid("s".to_string()), s_val),
        (Vid("gen_g1".to_string()), g),
        (Vid("gen_g2".to_string()), h),
        (Vid("srs_g1".to_string()), ss),
        (Vid("srs_g2_s".to_string()), h_val),
    ])
}

pub fn spec() -> common::ExampleSpec<ArkBls12_381> {
    common::ExampleSpec {
        source: "examples/membership/membership.zippel",
        defaults: &[("N", 2), ("M", 2), ("S", 2)],
        validate: Some(|sizes, _analysis| {
            if size(sizes, "N") < 2
                || size(sizes, "M") < 1
                || size(sizes, "S")
                    < size(sizes, "N").max((size(sizes, "N") - 1).saturating_mul(size(sizes, "M")))
            {
                return Err("N must be >= 2, M >= 1, and S >= max(N, (N-1)*M)".into());
            }
            Ok(())
        }),
        make_inputs,
        analyses: &[common::Analysis::Completeness, common::Analysis::Zk],
    }
}
