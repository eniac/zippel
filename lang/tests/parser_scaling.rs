//! Manual scaling benchmark: `cargo test -p lang --release --test parser_scaling -- --ignored --nocapture`.

use std::hint::black_box;
use std::time::Instant;

use lang::ast::{Exp, Exprs, Size};
use lang::parser::parse_decls;

#[test]
#[ignore = "manual scaling benchmark"]
fn many_small_declarations() {
    for count in [4_000, 16_000, 64_000] {
        let src: String = (0..count)
            .map(|i| format!("fn f{i}<>() {{ 0 }}\n"))
            .collect();
        let start = Instant::now();
        let (decls, errors) = parse_decls(black_box(&src));
        assert!(errors.is_empty(), "{errors:?}");
        assert_eq!(decls.len(), count);
        println!("parse {count}: {:?}", start.elapsed());
    }
}

#[test]
#[ignore = "manual scaling benchmark"]
fn extract_small_bodies() {
    for count in [4_000, 16_000, 64_000] {
        let mut exprs = Exprs::<Size>::new();
        let roots: Vec<_> = (0..count).map(|_| exprs.push(Exp::Unit, 0..0)).collect();
        let start = Instant::now();
        for root in roots {
            black_box(exprs.extract(black_box(root)));
        }
        println!("extract {count}: {:?}", start.elapsed());
    }
}

#[test]
#[ignore = "manual scaling benchmark"]
fn one_large_body() {
    for count in [4_000, 16_000, 64_000] {
        let mut src = String::from("fn f<>() { ");
        for i in 0..count {
            src += &format!("let x{i} = 0; ");
        }
        src += "0 }";
        let start = Instant::now();
        let (decls, errors) = parse_decls(black_box(&src));
        assert!(errors.is_empty(), "{errors:?}");
        assert_eq!(decls.len(), 1);
        println!("large body {count}: {:?}", start.elapsed());
    }
}
