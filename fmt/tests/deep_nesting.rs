#[test]
fn deep_format_on_small_stack() {
    std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(|| {
            let depth = 50_000;
            let negation = format!("{}r", "- ".repeat(depth));
            // A deep body exercises document destruction; an argument also exercises the
            // document clone used to build the flat and broken forms of a delimited list.
            for value in [negation.clone(), format!("g({negation})")] {
                let src = format!("fn f<F: Field>(instance r: F) -> F {{ {value} }}");
                let formatted = fmt::format_source(&src).expect("formats deep negation");
                let parse = |src: &str| lang::parser::parse_decls(src).0;
                assert!(
                    parse(&src) == parse(&formatted),
                    "formatting changes the AST"
                );
                assert_eq!(
                    fmt::format_source(&formatted).expect("formats again"),
                    formatted
                );
            }
        })
        .expect("spawns a small-stack thread")
        .join()
        .expect("deep formatting finishes on a small stack");
}

#[test]
fn deep_types_and_sizes_format_on_small_stack() {
    std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(|| {
            // Each fails without `format_typ`'s and `format_size`'s guards from about 1,000 and
            // 2,000 levels.
            let depth = 4_000;
            let src = |arg: &str| format!("fn f<F: Field>(instance a: {arg}) -> F {{ r }}");
            // A deep type breaks one level per line, so its output is quadratic in the depth;
            // it is only formatted once.
            let typ = format!("{}F{}", "[".repeat(depth), "; 1]".repeat(depth));
            fmt::format_source(&src(&typ)).expect("formats a deep type");
            let size = src(&format!("[F; {}]", vec!["1"; depth].join(" + ")));
            let formatted = fmt::format_source(&size).expect("formats a deep size");
            assert_eq!(
                fmt::format_source(&formatted).expect("formats again"),
                formatted
            );
        })
        .expect("spawns a small-stack thread")
        .join()
        .expect("deep formatting finishes on a small stack");
}
