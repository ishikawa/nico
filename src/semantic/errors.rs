use super::TypeKind;
use std::fmt::Display;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum SemanticError<'a> {
    #[error("Expected {expected} arguments, found {found}")]
    ArgumentCountMismatch { expected: usize, found: usize },
    #[error("Expected callable function, found {callee_type}")]
    CalleeIsNotCallable { callee_type: TypeKind<'a> },
    #[error("Callee is not subscriptable, found {callee_type}")]
    CalleeIsNotSubscriptable { callee_type: TypeKind<'a> },
    #[error("Cannot find type `{0}` in this scope")]
    UndefinedType(String),
    #[error("{0}")]
    TypeError(TypeError<'a>),
}

#[derive(Error, Debug, Clone, Copy, PartialEq)]
pub enum TypeError<'a> {
    TypeMismatchError(TypeMismatchError<'a>),
}

impl Display for TypeError<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeError::TypeMismatchError(err) => err.fmt(f),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct TypeMismatchError<'a> {
    expected_type: TypeKind<'a>,
    actual_type: TypeKind<'a>,
}

impl<'a> TypeMismatchError<'a> {
    pub fn new(expected_type: TypeKind<'a>, actual_type: TypeKind<'a>) -> Self {
        Self {
            expected_type,
            actual_type,
        }
    }

    pub fn expected_type(&self) -> TypeKind<'a> {
        self.expected_type
    }

    pub fn actual_type(&self) -> TypeKind<'a> {
        self.actual_type
    }
}

impl Display for TypeMismatchError<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "mismatched types")?;
        write!(f, "expected ")?;
        writeln!(f, "`{}`", self.expected_type())?;
        write!(f, "   found ")?;
        write!(f, "`{}`", self.actual_type())
    }
}
