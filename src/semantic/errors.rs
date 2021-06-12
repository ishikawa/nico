use thiserror::Error;

use super::TypeKind;

#[derive(Error, Debug)]
pub enum SemanticError<'a> {
    #[error("Expected {expected} arguments, found {found}")]
    ArgumentCountMismatch { expected: usize, found: usize },
    #[error("Expected callable function, found {callee_type}")]
    CalleeIsNotCallable { callee_type: TypeKind<'a> },
}
