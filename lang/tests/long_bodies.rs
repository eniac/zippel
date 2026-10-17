//! Long `let`/`<-`/`;` chains: stack use must not grow with statement count (issue #252).

use lang::ast::{Body, Exp, UExpr, UModule};
use share::Ctx;

/// A Schnorr-shaped proto whose body binds `a0..an` before the protocol messages.
fn long_proto(n: usize) -> String {
    let mut src = String::from(
        "proto chain<G: Group, F: Scalar<G>>(witness x: F, instance g: G, instance h: G) \
         where h == g * x {\n    let r = random<F>;\n    let a0 = r;\n",
    );
    for i in 1..=n {
        src += &format!("    let a{i} = a{} + r;\n", i - 1);
    }
    src += &format!(
        "    u <- g * a{n};\n    c <- challenge<F>;\n    z <- a{n} + x * c;\n    \
         verify(g * z == u + h * c)\n}}\n"
    );
    src
}

#[test]
fn long_body_checks_on_small_stack() {
    // Parsing, concretization and type checking each walk the body; on a 2 MiB stack none of
    // them may recurse once per statement.
    std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(|| {
            let (module, diags) = UModule::parse(&long_proto(1000));
            assert!(diags.is_empty(), "{diags:?}");
            let module = module
                .expect("parses")
                .concretize(&Ctx::new())
                .expect("concretizes");
            let diags = module.typecheck();
            assert!(diags.is_empty(), "{diags:?}");
        })
        .unwrap()
        .join()
        .unwrap();
}

/// The body of the only declaration in `src`.
fn body(src: &str) -> UExpr {
    let (module, diags) = UModule::parse(src);
    assert!(diags.is_empty(), "{diags:?}");
    let module = module.expect("parses");
    let (_, body) = module.iter().next().expect("one declaration");
    match body {
        Body::Proto { body, .. } => body.clone().expect("non-empty body"),
        _ => panic!("expected a proto"),
    }
}

#[test]
fn block_and_statement_spans() {
    // A block spans its statements and value; each statement spans its tokens through `;`.
    // (source, each statement's text in order, the block's value if any)
    let cases: [(&str, &[&str], Option<&str>); 2] = [
        (
            "proto p<F: Field>(instance x: F) where x == x { let a = x; b <- a; verify(a == x); verify(a == b) }",
            &["let a = x;", "b <- a;", "verify(a == x);"],
            Some("verify(a == b)"),
        ),
        (
            "proto p<F: Field>(instance x: F) where x == x { let a = x; b <- a; verify(a == b); }",
            &["let a = x;", "b <- a;", "verify(a == b);"],
            None,
        ),
    ];
    let range = |src: &str, text: &str| {
        let start = src.find(text).unwrap();
        start..start + text.len()
    };
    for (src, texts, value) in cases {
        let block = body(src);
        let Exp::Block(stmts, tail) = block.node() else {
            panic!("expected a block, got {:?}", block.node());
        };
        let end = value.map_or_else(
            || range(src, texts[texts.len() - 1]).end,
            |v| range(src, v).end,
        );
        assert_eq!(block.span(), &(range(src, texts[0]).start..end), "{src}");
        let spans: Vec<_> = stmts.iter().map(|s| block.exprs.span(s).clone()).collect();
        let expected: Vec<_> = texts.iter().map(|t| range(src, t)).collect();
        assert_eq!(spans, expected, "{src}");
        assert_eq!(
            tail.map(|t| block.exprs.span(t).clone()),
            value.map(|v| range(src, v)),
            "{src}"
        );
    }
}
