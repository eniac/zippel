mod error;
pub use error::InputError;

use pest_derive::Parser;
use pest::Parser as PestParser;
use std::sync::Once;

static INIT_PEST_ERROR_DETAIL: Once = Once::new();

/// Initialize pest parser to provide detailed error messages
#[inline]
fn init_pest_error_detail() {
    INIT_PEST_ERROR_DETAIL.call_once(|| {
        pest::set_error_detail(true);
    });
}

/// Pest parser for zippel
#[derive(Parser)]
#[grammar = "parser/zippel.pest"] // relative to src
pub struct ZippelParser;

impl ZippelParser {
    /// Parse with automatic initialization of enhanced error details
    pub fn parse<'i>(
        rule: crate::parser::Rule,
        input: &'i str,
    ) -> Result<pest::iterators::Pairs<'i, crate::parser::Rule>, pest::error::Error<crate::parser::Rule>> {
        init_pest_error_detail();
        <Self as PestParser<crate::parser::Rule>>::parse(rule, input)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Rule;

    #[test]
    fn test_pest_error_detail_initialization() {
        // This test verifies that pest error detail is initialized when parsing
        // We don't need to check the actual value since pest::set_error_detail is global
        // and we just need to ensure our initialization code runs without errors
        let result = ZippelParser::parse(Rule::id, "validId");
        assert!(result.is_ok());
        
        // Attempt to parse invalid input to trigger error path (which should have detailed errors)
        let result = ZippelParser::parse(Rule::id, "");
        assert!(result.is_err());
    }
}

