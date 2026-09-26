use std::fmt;

/// This is for no-type annotations and no principals
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Copy, Clone)]
pub struct Nothing;

impl fmt::Display for Nothing {
    fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_nothing_display() {
        let nothing = Nothing;
        assert_eq!(nothing.to_string(), "");
    }
}
