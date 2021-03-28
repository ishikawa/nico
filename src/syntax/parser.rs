use super::errors::ParseError;
use super::tree::ModuleNode;
use crate::tokenizer::Tokenizer;

#[derive(Debug)]
pub struct Parser<'a> {
    tokenizer: &'a Tokenizer<'a>,
}

impl<'a> Parser<'a> {
    pub fn new(tokenizer: &'a Tokenizer<'a>) -> Self {
        Self { tokenizer }
    }
}

impl Parser<'_> {
    pub fn parse(&mut self) -> Result<ModuleNode, ParseError> {
        Err(ParseError::syntax_error(
            self.tokenizer.current_position(),
            "Fail",
        ))
    }
}
