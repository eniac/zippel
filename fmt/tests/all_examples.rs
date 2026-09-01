mod common;

use common::{fmt, zippel_examples};

/// Parse source, format it, parse the output, format again, check idempotency.
fn round_trip_check(name: &str, src: &str) {
    let out1 = fmt(src);
    let out2 = fmt(&out1);
    assert_eq!(out1, out2, "{}: not idempotent", name);
}

#[test]
fn all_examples_round_trip() {
    let mut count = 0;
    let mut failures = Vec::new();

    for path in zippel_examples() {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let src = std::fs::read_to_string(&path).unwrap();
        count += 1;

        // Use a separate test result collector so we can report all failures
        match std::panic::catch_unwind(|| {
            round_trip_check(&name, &src);
        }) {
            Ok(()) => {}
            Err(_) => {
                failures.push(name);
            }
        }
    }

    assert!(count > 0, "no examples found");
    if !failures.is_empty() {
        panic!(
            "{} of {} examples failed round-trip:\n  {}",
            failures.len(),
            count,
            failures.join("\n  ")
        );
    }
}
