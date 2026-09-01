//! Shared test helpers for formatter integration tests.
//!
//! Every assertion checks both correctness (output matches expected) and
//! idempotency (formatting the output again yields the same result).
//!
//! `#[allow(dead_code)]` is needed because each test file is compiled as a
//! separate crate — not every file uses every helper.

#![allow(dead_code)]

use fmt::{Style, format_source, format_source_with_style};

/// Format source with the default style, panicking on parse error.
#[track_caller]
pub fn fmt(src: &str) -> String {
    format_source(src).expect("parse error")
}

/// Assert that `src` formats to `expected` and that the output is idempotent.
#[track_caller]
pub fn assert_ok(src: &str, expected: &str) {
    let out = fmt(src);
    assert_eq!(out, expected, "first format mismatch");
    assert_eq!(fmt(&out), out, "not idempotent");
}

/// Format source with a custom style, panicking on parse error.
#[track_caller]
fn fmt_with_style(src: &str, style: &Style) -> String {
    format_source_with_style(src, style).expect("parse error")
}

/// Assert that `src` formats to `expected` under `style` and is idempotent.
#[track_caller]
pub fn assert_ok_with_style(src: &str, expected: &str, style: &Style) {
    let out = fmt_with_style(src, style);
    assert_eq!(out, expected, "first format mismatch");
    assert_eq!(fmt_with_style(&out, style), out, "not idempotent");
}

/// Every `.zippel` file under `../examples`, sorted for deterministic order.
pub fn zippel_examples() -> Vec<std::path::PathBuf> {
    let mut out = Vec::new();
    for entry in std::fs::read_dir("../examples").unwrap() {
        let dir = entry.unwrap().path();
        if !dir.is_dir() {
            continue;
        }
        for file in std::fs::read_dir(&dir).unwrap() {
            let path = file.unwrap().path();
            if path.extension().is_some_and(|e| e == "zippel") {
                out.push(path);
            }
        }
    }
    out.sort();
    out
}
