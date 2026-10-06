//! Non-comment source line counts (NCLOC) for each benchmarked system: its
//! `.zippel` source and each native baseline's Rust code. Every count is
//! computed from the source files themselves, included at compile time;
//! external crates' sources are located by build.rs.

/// Every (system, native baseline) pair the benchmarks time. Most systems
/// have one baseline named after the system; spartan has two.
pub const BASELINES: [(&str, &str); 14] = [
    ("schnorr", "schnorr"),
    ("sumcheck", "sumcheck"),
    ("ipa", "ipa"),
    ("kzg", "kzg"),
    ("pari", "pari"),
    ("groth16", "groth16"),
    ("pst13", "pst13"),
    ("hyrax", "hyrax"),
    ("spartan", "spartan"),
    ("spartan", "ark-spartan"),
    ("dekart", "dekart"),
    ("kzh", "kzh"),
    ("dory", "dory"),
    ("hyperplonk", "hyperplonk"),
];

const ZIPPEL_SCHNORR: &str = include_str!("../../examples/schnorr/schnorr.zippel");
const ZIPPEL_SUMCHECK: &str = include_str!("../../examples/sumcheck/sumcheck.zippel");
const ZIPPEL_IPA: &str = include_str!("../../examples/ipa/ipa.zippel");
const ZIPPEL_KZG: &str = include_str!("../../examples/kzg/kzg.zippel");
const ZIPPEL_PARI: &str = include_str!("../../examples/pari/pari.zippel");
const ZIPPEL_GROTH16: &str = include_str!("../../examples/groth16/groth16.zippel");
const ZIPPEL_PST13: &str = include_str!("../../examples/pst13/pst13.zippel");
const ZIPPEL_HYRAX: &str = include_str!("../../examples/hyrax_pcs/hyrax_pcs.zippel");
const ZIPPEL_SPARTAN: &str = include_str!("../../examples/spartan/spartan.zippel");
const ZIPPEL_DEKART: &str = include_str!("../../examples/dekart/dekart.zippel");
const ZIPPEL_KZH: &str = include_str!("../../examples/kzh/kzh.zippel");
const ZIPPEL_DORY: &str = include_str!("../../examples/dory_pcs/dory_pcs.zippel");
const ZIPPEL_HYPERPLONK: &str =
    include_str!("../../examples/hyperplonk_snark/hyperplonk_snark.zippel");

const NATIVE_IPA_RS: &str = include_str!("ipa.rs");
// DeKART native baseline is vendored from aptos-dkg's dekart_univariate_v2
// (+ the hiding-KZG / sigma-protocol / FS helpers it uses), flattened into
// one file (see src/dekart_upstream/). NCLOC excludes its `#[cfg(test)]`
// module, which sits at the end of the file.
const NATIVE_DEKART_MOD_RS: &str = include_str!("dekart_upstream/mod.rs");
const NATIVE_KZH_MOD_RS: &str = include_str!("kzh_upstream/mod.rs");
const NATIVE_DORY_MOD_RS: &str = include_str!("dory_upstream/mod.rs");
const NATIVE_HYPERPLONK_PCS_RS: &str = include_str!("hyperplonk_upstream/pcs.rs");
const NATIVE_HYPERPLONK_PIOP_RS: &str = include_str!("hyperplonk_upstream/piop.rs");
const NATIVE_HYPERPLONK_SNARK_RS: &str = include_str!("hyperplonk_upstream/snark.rs");
// Upstream PARI baseline: vendored from alireza-shirzad/garuda-pari (commit
// 3db79ad). NCLOC sums prover + verifier + generator + data_structures +
// utils + the bit of `shared-utils` Pari actually uses (the transcript and
// two inlined helpers in pari_upstream/mod.rs).
const NATIVE_PARI_MOD_RS: &str = include_str!("pari_upstream/mod.rs");
const NATIVE_PARI_GEN_RS: &str = include_str!("pari_upstream/generator.rs");
const NATIVE_PARI_PROVER_RS: &str = include_str!("pari_upstream/prover.rs");
const NATIVE_PARI_VERIFIER_RS: &str = include_str!("pari_upstream/verifier.rs");
const NATIVE_PARI_DS_RS: &str = include_str!("pari_upstream/data_structures.rs");
const NATIVE_PARI_UTILS_RS: &str = include_str!("pari_upstream/utils.rs");
const NATIVE_PARI_TRANSCRIPT_RS: &str = include_str!("pari_upstream/transcript/mod.rs");
const NATIVE_PARI_TRANSCRIPT_ERR_RS: &str = include_str!("pari_upstream/transcript/errors.rs");

// PST13 native baseline is vendored + patched (see src/pst13_upstream/).
// NCLOC counts mod.rs + data_structures.rs of our vendored version,
// reflecting what code actually runs in the bench.
const NATIVE_PST13_MOD_RS: &str = include_str!("pst13_upstream/mod.rs");
const NATIVE_PST13_DS_RS: &str = include_str!("pst13_upstream/data_structures.rs");

// Hyrax native baseline is vendored + patched (see src/hyrax_upstream/).
// Replaces upstream `Matrix<F>` (Vec<Vec<F>>) with flat row-major
// storage and rewrites `row_mul` as a SAXPY accumulation — eliminates
// the per-column 16KB temp Vec and the cache-hostile column gathers.
const NATIVE_HYRAX_MOD_RS: &str = include_str!("hyrax_upstream/mod.rs");

// Sumcheck native baseline, vendored from hyperplonk (ported to ark 0.6):
// src/sumcheck_upstream/{arithmetic,poly_iop,transcript}/*.rs.
const NATIVE_SUMCHECK_RS: [&str; 13] = [
    include_str!("sumcheck_upstream/arithmetic/errors.rs"),
    include_str!("sumcheck_upstream/arithmetic/mod.rs"),
    include_str!("sumcheck_upstream/arithmetic/multilinear_polynomial.rs"),
    include_str!("sumcheck_upstream/arithmetic/util.rs"),
    include_str!("sumcheck_upstream/arithmetic/virtual_polynomial.rs"),
    include_str!("sumcheck_upstream/poly_iop/errors.rs"),
    include_str!("sumcheck_upstream/poly_iop/mod.rs"),
    include_str!("sumcheck_upstream/poly_iop/structs.rs"),
    include_str!("sumcheck_upstream/poly_iop/sum_check/mod.rs"),
    include_str!("sumcheck_upstream/poly_iop/sum_check/prover.rs"),
    include_str!("sumcheck_upstream/poly_iop/sum_check/verifier.rs"),
    include_str!("sumcheck_upstream/transcript/errors.rs"),
    include_str!("sumcheck_upstream/transcript/mod.rs"),
];

// Systems delegating to external crates: native = prover + verifier code in
// the crate version `Cargo.lock` resolves, located by build.rs.
const NATIVE_SCHNORR_RS: &str = include_str!(concat!(
    env!("ARK_CRYPTO_PRIMITIVES_SRC_DIR"),
    "/src/signature/schnorr/mod.rs"
));
const NATIVE_KZG_RS: &str = include_str!(concat!(
    env!("ARK_POLY_COMMIT_SRC_DIR"),
    "/src/kzg10/mod.rs"
));
const NATIVE_GROTH16_RS: [&str; 3] = [
    include_str!(concat!(env!("ARK_GROTH16_SRC_DIR"), "/src/prover.rs")),
    include_str!(concat!(env!("ARK_GROTH16_SRC_DIR"), "/src/verifier.rs")),
    include_str!(concat!(env!("ARK_GROTH16_SRC_DIR"), "/src/r1cs_to_qap.rs")),
];
const NATIVE_SPARTAN_RS: [&str; 4] = [
    include_str!(concat!(env!("SPARTAN_SRC_DIR"), "/src/r1csproof.rs")),
    include_str!(concat!(env!("SPARTAN_SRC_DIR"), "/src/sumcheck.rs")),
    include_str!(concat!(env!("SPARTAN_SRC_DIR"), "/src/nizk/mod.rs")),
    include_str!(concat!(env!("SPARTAN_SRC_DIR"), "/src/nizk/bullet.rs")),
];

// ark-spartan's NCLOC, same scope as NATIVE_SPARTAN_RS but over the
// vendored ark-spartan port.
const ARK_SPARTAN_R1CSPROOF_RS: &str = include_str!("ark_spartan_upstream/r1csproof.rs");
const ARK_SPARTAN_SUMCHECK_RS: &str = include_str!("ark_spartan_upstream/sumcheck.rs");
const ARK_SPARTAN_NIZK_MOD_RS: &str = include_str!("ark_spartan_upstream/nizk/mod.rs");
const ARK_SPARTAN_NIZK_BULLET_RS: &str = include_str!("ark_spartan_upstream/nizk/bullet.rs");

fn count_ncloc_line_comments(src: &str) -> usize {
    src.lines()
        .filter(|l| {
            let t = l.trim();
            !t.is_empty() && !t.starts_with("//")
        })
        .count()
}

fn count_ncloc_rust(src: &str) -> usize {
    let mut count = 0usize;
    let mut in_block = false;
    for line in src.lines() {
        let trimmed = line.trim();
        if in_block {
            if let Some(after) = trimmed.split_once("*/") {
                in_block = false;
                let rest = after.1.trim();
                if !rest.is_empty() && !rest.starts_with("//") {
                    count += 1;
                }
            }
            continue;
        }
        if trimmed.is_empty() || trimmed.starts_with("//") {
            continue;
        }
        if trimmed.starts_with("/*") && !trimmed.contains("*/") {
            in_block = true;
            continue;
        }
        count += 1;
    }
    count
}

fn sum_ncloc_rust(srcs: &[&str]) -> usize {
    srcs.iter().map(|s| count_ncloc_rust(s)).sum()
}

fn extract_braced_block<'a>(src: &'a str, header: &str) -> &'a str {
    let Some(start) = src.find(header) else {
        return "";
    };
    let after = &src[start..];
    let Some(brace) = after.find('{') else {
        return "";
    };
    let mut depth: i32 = 1;
    let body = &after[brace + 1..];
    for (i, c) in body.char_indices() {
        match c {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    return &body[..i];
                }
            }
            _ => {}
        }
    }
    body
}

/// Non-comment source lines of `sys`'s `.zippel` file, or 0 for an
/// unknown system.
pub fn zippel_ncloc(sys: &str) -> usize {
    match sys {
        "schnorr" => count_ncloc_line_comments(ZIPPEL_SCHNORR),
        "sumcheck" => count_ncloc_line_comments(ZIPPEL_SUMCHECK),
        "ipa" => count_ncloc_line_comments(ZIPPEL_IPA),
        "kzg" => count_ncloc_line_comments(ZIPPEL_KZG),
        "pari" => count_ncloc_line_comments(ZIPPEL_PARI),
        "groth16" => count_ncloc_line_comments(ZIPPEL_GROTH16),
        "pst13" => count_ncloc_line_comments(ZIPPEL_PST13),
        "hyrax" => count_ncloc_line_comments(ZIPPEL_HYRAX),
        "spartan" => count_ncloc_line_comments(ZIPPEL_SPARTAN),
        "dekart" => count_ncloc_line_comments(ZIPPEL_DEKART),
        "kzh" => count_ncloc_line_comments(ZIPPEL_KZH),
        "dory" => count_ncloc_line_comments(ZIPPEL_DORY),
        "hyperplonk" => count_ncloc_line_comments(ZIPPEL_HYPERPLONK),
        _ => 0,
    }
}

/// Non-comment source lines of a native baseline's Rust code (`baseline`
/// is a [`BASELINES`] name), or 0 for an unknown one.
pub fn native_ncloc(baseline: &str) -> usize {
    match baseline {
        "schnorr" => count_ncloc_rust(NATIVE_SCHNORR_RS),
        "sumcheck" => sum_ncloc_rust(&NATIVE_SUMCHECK_RS),
        "kzg" => count_ncloc_rust(NATIVE_KZG_RS),
        "groth16" => sum_ncloc_rust(&NATIVE_GROTH16_RS),
        "pst13" => count_ncloc_rust(NATIVE_PST13_MOD_RS) + count_ncloc_rust(NATIVE_PST13_DS_RS),
        "spartan" => sum_ncloc_rust(&NATIVE_SPARTAN_RS),
        "ark-spartan" => {
            count_ncloc_rust(ARK_SPARTAN_R1CSPROOF_RS)
                + count_ncloc_rust(ARK_SPARTAN_SUMCHECK_RS)
                + count_ncloc_rust(ARK_SPARTAN_NIZK_MOD_RS)
                + count_ncloc_rust(ARK_SPARTAN_NIZK_BULLET_RS)
        }
        "ipa" => count_ncloc_rust(extract_braced_block(NATIVE_IPA_RS, "pub mod native_side")),
        "hyrax" => count_ncloc_rust(NATIVE_HYRAX_MOD_RS),
        // The SNARK layers plus the vendored sumcheck stack they run on.
        "hyperplonk" => {
            sum_ncloc_rust(&NATIVE_SUMCHECK_RS)
                + count_ncloc_rust(NATIVE_HYPERPLONK_PCS_RS)
                + count_ncloc_rust(NATIVE_HYPERPLONK_PIOP_RS)
                + count_ncloc_rust(NATIVE_HYPERPLONK_SNARK_RS)
        }
        "dory" => count_ncloc_rust(
            NATIVE_DORY_MOD_RS
                .split("#[cfg(test)]")
                .next()
                .unwrap_or(NATIVE_DORY_MOD_RS),
        ),
        "kzh" => count_ncloc_rust(
            NATIVE_KZH_MOD_RS
                .split("#[cfg(test)]")
                .next()
                .unwrap_or(NATIVE_KZH_MOD_RS),
        ),
        "dekart" => count_ncloc_rust(
            NATIVE_DEKART_MOD_RS
                .split("#[cfg(test)]")
                .next()
                .unwrap_or(NATIVE_DEKART_MOD_RS),
        ),
        "pari" => {
            count_ncloc_rust(NATIVE_PARI_MOD_RS)
                + count_ncloc_rust(NATIVE_PARI_GEN_RS)
                + count_ncloc_rust(NATIVE_PARI_PROVER_RS)
                + count_ncloc_rust(NATIVE_PARI_VERIFIER_RS)
                + count_ncloc_rust(NATIVE_PARI_DS_RS)
                + count_ncloc_rust(NATIVE_PARI_UTILS_RS)
                + count_ncloc_rust(NATIVE_PARI_TRANSCRIPT_RS)
                + count_ncloc_rust(NATIVE_PARI_TRANSCRIPT_ERR_RS)
        }
        _ => 0,
    }
}
