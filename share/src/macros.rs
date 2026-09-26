/// `assert_eq!` for types that implement [`Display`](std::fmt::Display) but not
/// [`Debug`](std::fmt::Debug).
///
/// Most compiler IR types (`Typ`, `Exp`, `Dag`, `Value`) have a readable
/// `Display` and a useless or absent `Debug`, so the standard
/// macro is either unusable or unreadable on them.
///
/// # Panics
/// Panics when the two operands compare unequal, printing both with `Display`
/// plus the optional trailing format message.
#[macro_export]
macro_rules! assert_deq {
    ($left:expr, $right:expr $(,)?) => {{
        let left_val = &$left;
        let right_val = &$right;
        if left_val != right_val {
            panic!(
                "assertion failed: `(left == right)`\n  left: `{}`\n right: `{}`",
                left_val, right_val
            );
        }
    }};
    ($left:expr, $right:expr, $($arg:tt)+) => {{
        let left_val = &$left;
        let right_val = &$right;
        if left_val != right_val {
            panic!(
                "assertion failed: `(left == right)`\n  left: `{}`\n right: `{}`: {}",
                left_val, right_val, format_args!($($arg)+)
            );
        }
    }};
}

/// Unwraps a `Result`, panicking with the error's [`Display`](std::fmt::Display)
/// rendering instead of its `Debug` one.
///
/// Intended for tests and binaries over the workspace error enums, whose
/// `Display` impls pretty-print the offending typing judgement while `Debug`
/// dumps the whole captured context.
///
/// # Panics
/// Panics if the expression is `Err`.
#[macro_export]
macro_rules! unwrap {
    ($result:expr) => {
        match $result {
            Ok(value) => value,
            Err(err) => panic!("{}", err),
        }
    };
}
