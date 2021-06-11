use thiserror::Error;

#[derive(Error, Debug)]
pub enum SemanticError {
    #[error("Expected {expected} arguments, found {found}")]
    ArgumentCountMismatch { expected: usize, found: usize },
}
