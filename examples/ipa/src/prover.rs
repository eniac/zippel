use zippel::{
    Value,
    ATyp,
    Ctx,
    Vid,
    unwrap,
    UModule,
    UDags,
    ArkConfig,
};
use cli::compile;

fn main() {
    compile("examples/ipa/prover.zippel");
}