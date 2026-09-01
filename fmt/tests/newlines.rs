//! Line-ending tolerance. The formatter's canonical output is LF, but Windows
//! checkouts (`core.autocrlf=true`) materialize sources with CRLF. `check`
//! must accept those unchanged, and formatting must not depend on the style.

mod common;

use common::zippel_examples;
use std::borrow::Cow;

#[test]
fn crlf_source_is_accepted_by_check() {
    let mut count = 0;
    for path in zippel_examples() {
        let src = std::fs::read_to_string(&path).unwrap();
        let canonical = fmt::format_source(&src).expect("parse error");
        let crlf = canonical.replace('\n', "\r\n");

        assert!(
            fmt::check(&crlf).unwrap(),
            "{}: CRLF form rejected by check",
            path.display()
        );
        assert_eq!(
            fmt::format_source(&crlf).unwrap(),
            canonical,
            "{}: CRLF input changed formatter output",
            path.display()
        );
        count += 1;
    }
    assert!(count > 0, "no examples found");
}

#[test]
fn normalize_newlines_converts_and_borrows() {
    assert!(matches!(
        fmt::normalize_newlines("a\nb\n"),
        Cow::Borrowed(_)
    ));
    assert_eq!(fmt::normalize_newlines("a\r\nb\r\n"), "a\nb\n");
    assert_eq!(fmt::normalize_newlines("a\rb\r"), "a\nb\n");
}
