//! `Display` prints source syntax: printing a parsed module and parsing the text again must
//! give the same module (spans aside), on one line (`{}`) and on several (`{:#}`).

use std::path::Path;

use lang::ast::module::UModule;

fn parse(src: &str, what: &str) -> UModule {
    let (module, diags) = UModule::parse(src);
    let errors: Vec<_> = diags
        .iter()
        .filter(|d| d.severity == lang::diagnostic::Severity::Error)
        .map(|d| &d.summary)
        .collect();
    assert!(
        errors.is_empty(),
        "{what} does not parse: {errors:?}\n{src}"
    );
    module.unwrap_or_else(|| panic!("{what} produced no module"))
}

/// The protocol body of `src`, printed on one line.
fn printed_body(src: &str) -> String {
    let module = parse(src, "test source");
    let printed = format!("{module}");
    let start = printed.find(" { ").expect("protocol has a body") + 3;
    printed[start..printed.len() - 2].to_string()
}

/// The protocol body of `src`, printed with depth limit `depth`.
fn body_at_depth(src: &str, depth: usize) -> String {
    let module = parse(src, "test source");
    let (_, body) = module.iter().next().expect("one declaration");
    let lang::ast::Body::Proto {
        body: Some(body), ..
    } = body
    else {
        panic!("expected a protocol with a body")
    };
    format!("{:.*}", depth, body.node)
}

#[test]
fn printed_examples_parse_back_to_the_same_module() {
    let examples = Path::new(env!("CARGO_MANIFEST_DIR")).join("../examples");
    let mut checked = 0;
    for dir in std::fs::read_dir(&examples).unwrap() {
        let dir = dir.unwrap().path();
        if !dir.is_dir() {
            continue;
        }
        for file in std::fs::read_dir(&dir).unwrap() {
            let file = file.unwrap().path();
            if file.extension().is_none_or(|e| e != "zippel") {
                continue;
            }
            let name = file.display().to_string();
            let module = parse(&std::fs::read_to_string(&file).unwrap(), &name);
            for printed in [format!("{module}"), format!("{module:#}")] {
                let reparsed = parse(&printed, &format!("printed {name}"));
                assert!(
                    reparsed == module,
                    "{name}: printing and re-parsing changed the module\n{printed}"
                );
            }
            checked += 1;
        }
    }
    assert!(checked > 0, "no examples found");
}

#[test]
fn negation_of_a_looser_operator_keeps_its_parentheses() {
    let src = "proto p<F: Field>(instance a: F, instance b: F) where a == a {\n    verify(-(a + b) == -a + b)\n}\n";
    assert_eq!(printed_body(src), "verify(-(a + b) == -a + b)");
}

#[test]
fn reduce_prints_its_operator_as_written() {
    let src = "proto p<F: Field>(instance v: [F; 2]) where v == v {\n    verify(reduce(+, v) == v[0])\n}\n";
    assert_eq!(printed_body(src), "verify(reduce(+, v) == v[0])");
}

#[test]
fn depth_limit_elides_deep_subexpressions() {
    let src = "proto p<F: Field>(instance v: [F; 4], instance x: F) where x == x {\n    verify(reduce(+, [v[i] * x + v[i] * x * x for i in 0..4]) == x)\n}\n";
    assert_eq!(body_at_depth(src, 3), "verify(reduce(+, …) == x)");
    assert_eq!(
        body_at_depth(src, 5),
        "verify(reduce(+, [… + … for i in 0..4]) == x)"
    );
    // Variables, literals, and ranges print in full at any depth.
    assert_eq!(body_at_depth(src, 2), "verify(… == x)");
}

#[test]
fn depth_limit_shortens_long_lists() {
    let src = "proto p<F: Field>(instance a: F) where a == a {\n    verify([a, a, a, a, a, a] == [a, a])\n}\n";
    assert_eq!(body_at_depth(src, 10), "verify([a, a, a, a, …] == [a, a])");
}
