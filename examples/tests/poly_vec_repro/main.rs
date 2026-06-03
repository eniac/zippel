use ark_std::UniformRand;
use backend::{ArkBls12_381, ArkConfig, Value};
use lang::id::Vid;
use share::Ctx;
use std::path::PathBuf;
use zippel::*;

fn main() {
    let args = ZippelArgs::new(PathBuf::from("examples/tests/poly_vec_repro/repro.zippel"));
    let mut handler: zippel::ZippelHandler<ArkBls12_381> = ZippelHandler::new(args);

    // Compile with empty size environment since there are no size parameters
    handler.compile(&Ctx::new());

    let mut rng = rand::rngs::OsRng;
    let g_input = <ArkBls12_381 as ArkConfig>::G1::rand(&mut rng);

    let zero = <ArkBls12_381 as ArkConfig>::F::from(0u64);
    let one = <ArkBls12_381 as ArkConfig>::F::from(1u64);

    let inputs = Ctx::<Vid, Value<ArkBls12_381>>::from_iter([
        (Vid("coeffs".to_string()), Value::VecScalar(vec![zero, one])),
        (Vid("s".to_string()), Value::VecScalar(vec![zero, one])),
        (Vid("g".to_string()), Value::G1(g_input)),
    ]);

    let prover_scheduled = handler.default_schedule_prover();
    handler.run_prover(prover_scheduled, inputs).unwrap();
    println!("Example repro ran successfully!");
}
