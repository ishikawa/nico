use crate::tokenizer::{Position, Token, TokenError, TokenErrorKind};
use std::fmt;
use thiserror::Error;

#[derive(Debug, Error, PartialEq, Eq)]
#[error("{kind} at {position}")]
pub struct ParseError {
    pub position: Position,
    pub kind: ParseErrorKind,
}

impl ParseError {
    pub fn syntax_error<S: Into<String>>(position: Position, message: S) -> Self {
        Self {
            position,
            kind: ParseErrorKind::SyntaxError(message.into()),
        }
    }

    pub fn mismatch_token<S: AsRef<str>>(token: &Token, expected: S) -> Self {
        Self::syntax_error(
            token.range.start,
            format!("Expected {}, but found {}", expected.as_ref(), token.kind),
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseErrorKind {
    SyntaxError(String), // Genetic error
}

impl fmt::Display for ParseErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseErrorKind::SyntaxError(message) => write!(f, "Syntax error: {}", message),
        }
    }
}

impl From<&TokenError> for ParseError {
    fn from(err: &TokenError) -> Self {
        match &err.kind {
            TokenErrorKind::Error(message) => ParseError {
                position: err.position,
                kind: ParseErrorKind::SyntaxError(message.clone()),
            },
        }
    }
}
impl From<TokenError> for ParseError {
    fn from(err: TokenError) -> Self {
        Self::from(&err)
    }
}
