pub mod cli;
pub use cli::Command;
mod backend_2021_spring;
mod backend_2021_summer;

use crate::syntax::ParseError;
use std::io;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum CompilerError {
    #[error("invalid option: {0}")]
    InvalidOption(String),

    #[error(transparent)]
    InputSourceError(#[from] io::Error),

    #[error(transparent)]
    ParseError(#[from] ParseError),
}

impl From<String> for CompilerError {
    fn from(message: String) -> Self {
        CompilerError::InvalidOption(message)
    }
}
