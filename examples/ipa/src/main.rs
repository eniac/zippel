use cli::*;
use std::path::PathBuf;
use backend::ArkBls12_381;

fn main() {
    test();
    let path = PathBuf::from("../ipa.zippel");
    let args = CliArgs { file_path: path, pdf_path_opt: None, subgraph: None };
    let g = compile::<ArkBls12_381>(args);
    // get_graph::<ArkBls12_381>(&g, PathBuf::from("../../examples/ipa/ipa.zippel"), None, None);
    println!("testing");
}