mod types;
use crate::sem;
use crate::syntax::{
    FunctionDefinition, FunctionParameter, NodeKind, StructDefinition, VariablePattern,
};
use std::cell::RefCell;
use std::rc::Rc;

use self::types::TypeKind;

#[derive(Debug)]
pub struct SemanticValue<'a> {
    r#type: TypeKind<'a>,
    node: Option<NodeKind<'a>>,
}

impl<'a> SemanticValue<'a> {
    pub fn new(r#type: TypeKind<'a>, node: Option<NodeKind<'a>>) -> Self {
        Self { r#type, node }
    }

    pub fn r#type(&self) -> TypeKind<'a> {
        self.r#type
    }

    pub fn node(&self) -> Option<&NodeKind<'a>> {
        self.node.as_ref()
    }
}

/// `Builtin` is where a binding to "built-in" primitives/functions are defined.
/// It's not a part of an AST, so it doesn't have tokens.
#[derive(Debug)]
pub struct Builtin {
    name: String,
    r#type: Rc<RefCell<sem::Type>>,
}

impl Builtin {
    pub fn new<S: Into<String>>(name: S, r#type: &Rc<RefCell<sem::Type>>) -> Self {
        Self {
            name: name.into(),
            r#type: Rc::clone(r#type),
        }
    }

    pub fn name(&self) -> &str {
        self.name.as_str()
    }

    pub fn r#type(&self) -> &Rc<RefCell<sem::Type>> {
        &self.r#type
    }
}

#[derive(Debug, Clone)]
pub enum DefinitionKind<'a> {
    // Builtin functions, variables
    Builtin(Rc<Builtin>),
    // Declaration nodes
    StructDefinition(&'a StructDefinition<'a>),
    FunctionDefinition(&'a FunctionDefinition<'a>),
    FunctionParameter(&'a FunctionParameter<'a>),
    VariablePattern(&'a VariablePattern<'a>),
}

impl<'a> DefinitionKind<'a> {
    pub fn builtin(&self) -> Option<Rc<Builtin>> {
        if let DefinitionKind::Builtin(builtin) = self {
            Some(Rc::clone(builtin))
        } else {
            None
        }
    }

    pub fn struct_definition(&self) -> Option<&'a StructDefinition<'a>> {
        if let DefinitionKind::StructDefinition(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn function_definition(&self) -> Option<&'a FunctionDefinition<'a>> {
        if let DefinitionKind::FunctionDefinition(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn function_parameter(&self) -> Option<&'a FunctionParameter<'a>> {
        if let DefinitionKind::FunctionParameter(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn variable_pattern(&self) -> Option<&'a VariablePattern<'a>> {
        if let DefinitionKind::VariablePattern(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn is_builtin(&self) -> bool {
        matches!(self, Self::Builtin(..))
    }

    pub fn is_struct_definition(&self) -> bool {
        matches!(self, Self::StructDefinition(..))
    }

    pub fn is_function_definition(&self) -> bool {
        matches!(self, Self::FunctionDefinition(..))
    }

    pub fn is_function_parameter(&self) -> bool {
        matches!(self, Self::FunctionParameter(..))
    }

    pub fn is_pattern(&self) -> bool {
        matches!(self, Self::VariablePattern(..))
    }

    pub fn ptr_eq(&self, other: &DefinitionKind<'a>) -> bool {
        if let DefinitionKind::Builtin(ref definition1) = self {
            if let DefinitionKind::Builtin(ref definition2) = other {
                return std::ptr::eq(definition1.as_ref(), definition2.as_ref());
            }
        }

        if let DefinitionKind::StructDefinition(definition1) = self {
            if let DefinitionKind::StructDefinition(definition2) = other {
                return std::ptr::eq(*definition1, *definition2);
            }
        }

        if let DefinitionKind::FunctionDefinition(definition1) = self {
            if let DefinitionKind::FunctionDefinition(definition2) = other {
                return std::ptr::eq(*definition1, *definition2);
            }
        }

        if let DefinitionKind::FunctionParameter(definition1) = self {
            if let DefinitionKind::FunctionParameter(definition2) = other {
                return std::ptr::eq(*definition1, *definition2);
            }
        }

        if let DefinitionKind::VariablePattern(definition1) = self {
            if let DefinitionKind::VariablePattern(definition2) = other {
                return std::ptr::eq(*definition1, *definition2);
            }
        }

        false
    }
}
