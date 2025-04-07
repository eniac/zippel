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
