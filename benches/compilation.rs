use backend::{ArkBls12_381, ArkCurve25519, ArkSecp256k1};
use lang::id::Tid;
use share::Ctx;
use std::path::PathBuf;
use std::time::Instant;
use zippel::*;

fn compile_protocol<C: backend::ArkConfig + backend::HasOpFactory>(
    name: &str,
    zippel_path: PathBuf,
    sizes: &Ctx<Tid, usize>,
) -> f64 {
    let start_total = Instant::now();
    let args = ZippelArgs::new(zippel_path);
    let mut handler: ZippelHandler<C> = ZippelHandler::new(args);
    handler.compile(sizes);

    let elapsed = start_total.elapsed().as_secs_f64();
    println!("Compiled {:<25} in {:.4} seconds", name, elapsed);
    elapsed
}

fn main() {
    println!("=========================================");
    println!("ZIPPEL 2^18 COMPILATION TIMING SUITE");
    println!("=========================================");

    let mut timings = Vec::new();
    let target_m = 18;

    // 1. Sumcheck (NUM_VARS_CONST = 18, MAX_DEGREE_CONST = 2)
    let mut sizes_sumcheck = Ctx::new();
    sizes_sumcheck.insert(&Tid::new("NUM_VARS_CONST"), &target_m);
    sizes_sumcheck.insert(&Tid::new("MAX_DEGREE_CONST"), &2);
    let t_sumcheck = compile_protocol::<ArkBls12_381>(
        "Sumcheck (2^18 vars)",
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/sumcheck/sumcheck.zippel"),
        &sizes_sumcheck,
    );
    timings.push(("Sumcheck", t_sumcheck));

    // 2. Bulletproofs (IPA) (S = 18)
    let mut sizes_ipa = Ctx::new();
    sizes_ipa.insert(&Tid::new("S"), &target_m);
    let t_ipa = compile_protocol::<ArkSecp256k1>(
        "Bulletproofs (IPA) (2^18 elements)",
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/ipa/ipa.zippel"),
        &sizes_ipa,
    );
    timings.push(("Bulletproofs (IPA)", t_ipa));

    // 3. KZG (N = 2^18)
    let mut sizes_kzg = Ctx::new();
    sizes_kzg.insert(&Tid::new("N"), &262_144);
    let t_kzg = compile_protocol::<ArkBls12_381>(
        "KZG (2^18 coefficients)",
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/kzg/kzg.zippel"),
        &sizes_kzg,
    );
    timings.push(("KZG", t_kzg));

    // 4. Pari (M = 18, N = 1, KMN = 2^18 - 2)
    let mut sizes_pari = Ctx::new();
    sizes_pari.insert(&Tid::new("M"), &target_m);
    sizes_pari.insert(&Tid::new("N"), &1);
    sizes_pari.insert(&Tid::new("KMN"), &262_142);
    let t_pari = compile_protocol::<ArkBls12_381>(
        "Pari (2^18 constraints)",
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/pari/pari.zippel"),
        &sizes_pari,
    );
    timings.push(("Pari", t_pari));

    // 5. Groth16 (M = 33, L = 2^18, H = 2^18)
    let mut sizes_groth16 = Ctx::new();
    sizes_groth16.insert(&Tid::new("M"), &33);
    sizes_groth16.insert(&Tid::new("L"), &262_144);
    sizes_groth16.insert(&Tid::new("H"), &262_144);
    let t_groth16 = compile_protocol::<ArkBls12_381>(
        "Groth16 (2^18 constraints)",
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/groth16/groth16.zippel"),
        &sizes_groth16,
    );
    timings.push(("Groth16", t_groth16));

    // 6. PST13 (N = 18)
    let mut sizes_pst13 = Ctx::new();
    sizes_pst13.insert(&Tid::new("N"), &target_m);
    let t_pst13 = compile_protocol::<ArkBls12_381>(
        "PST13 (2^18 coefficients)",
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/pst13/pst13.zippel"),
        &sizes_pst13,
    );
    timings.push(("PST13", t_pst13));

    // 7. Hyrax (using hyrax_ipa component, S = 18)
    let mut sizes_hyrax = Ctx::new();
    sizes_hyrax.insert(&Tid::new("S"), &target_m);
    let t_hyrax = compile_protocol::<ArkBls12_381>(
        "Hyrax (2^18 elements)",
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/hyrax_ipa/hyrax_ipa.zippel"),
        &sizes_hyrax,
    );
    timings.push(("Hyrax (IPA)", t_hyrax));

    // 8. Spartan (M = 18)
    let mut sizes_spartan = Ctx::new();
    sizes_spartan.insert(&Tid::new("M"), &target_m);
    let t_spartan = compile_protocol::<ArkCurve25519>(
        "Spartan (2^18 constraints)",
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/spartan/spartan.zippel"),
        &sizes_spartan,
    );
    timings.push(("Spartan", t_spartan));

    println!("=========================================");
    if let Some(min_t) = timings.iter().min_by(|a, b| a.1.partial_cmp(&b.1).unwrap()) {
        println!("Min time: {} ({:.4}s)", min_t.0, min_t.1);
    }
    if let Some(max_t) = timings.iter().max_by(|a, b| a.1.partial_cmp(&b.1).unwrap()) {
        println!("Max time: {} ({:.4}s)", max_t.0, max_t.1);
    }
    println!("=========================================");
}
