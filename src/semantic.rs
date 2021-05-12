use crate::syntax::{self, NodeId};
use crate::{sem::Type, util::wrap};
use std::{cell::RefCell, rc::Rc};

#[derive(Debug)]
pub struct SemanticValue {
    kind: SemanticValueKind,

    /// The node id for a node where this value is defined. `None` for builtin values.
    /// - `Function` - syntax::FunctionDefinition
    /// - `Struct` - syntax::StructDefinition
    /// - `Variable` - syntax::Identifier
    node_id: Option<NodeId>, // syntax::FunctionDefinition. None for builtin.
    r#type: Option<Rc<RefCell<Type>>>,
}

impl SemanticValue {
    pub fn new(
        kind: SemanticValueKind,
        node_id: Option<NodeId>,
        r#type: Option<Rc<RefCell<Type>>>,
    ) -> Self {
        Self {
            kind,
            node_id,
            r#type,
        }
    }

    pub fn define_function<S: Into<String>>(
        name: S,
        parameters: &[(&str, Type)],
        return_type: Type,
    ) -> Self {
        let function_type = Type::Function {
            params: parameters.iter().map(|(_, ty)| wrap(*ty)).collect(),
            return_type: wrap(return_type),
        };
        let name = name.into();
        let parameters = parameters
            .iter()
            .map(|(param, _)| param.to_string())
            .collect();
        let ty = wrap(function_type);
        let fun = Function::new(name, parameters, None, Some(Rc::clone(&ty)));

        Self::new(SemanticValueKind::Function(fun), None, Some(Rc::clone(&ty)))
    }

    pub fn kind(&self) -> &SemanticValueKind {
        &self.kind
    }

    pub fn node_id(&self) -> Option<NodeId> {
        self.node_id
    }

    pub fn r#type(&self) -> Option<&Rc<RefCell<Type>>> {
        self.r#type.as_ref()
    }

    pub fn name(&self) -> Option<&str> {
        match self.kind {
            SemanticValueKind::Function(function) => Some(function.name()),
            SemanticValueKind::Struct(r#struct) => Some(r#struct.name()),
            SemanticValueKind::Variable(variable) => Some(variable.name()),
            _ => None,
        }
    }
}

#[derive(Debug)]
pub enum SemanticValueKind {
    Function(Function),
    Struct(Struct),
    Variable(Variable),
}

impl SemanticValueKind {
    pub fn function(&self) -> Option<&Function> {
        if let SemanticValueKind::Function(function) = self {
            Some(function)
        } else {
            None
        }
    }

    pub fn r#struct(&self) -> Option<&Struct> {
        if let SemanticValueKind::Struct(value) = self {
            Some(value)
        } else {
            None
        }
    }

    pub fn variable(&self) -> Option<&Variable> {
        if let SemanticValueKind::Variable(value) = self {
            Some(value)
        } else {
            None
        }
    }

    pub fn is_function(&self) -> bool {
        matches!(self, SemanticValueKind::Function(_))
    }

    pub fn is_struct(&self) -> bool {
        matches!(self, SemanticValueKind::Struct(_))
    }

    pub fn is_variable(&self) -> bool {
        matches!(self, SemanticValueKind::Variable(_))
    }
}

#[derive(Debug)]
pub struct Function {
    name: String,
    parameters: Vec<String>,
    node_id: Option<NodeId>, // syntax::FunctionDefinition. None for builtin.
    r#type: Option<Rc<RefCell<Type>>>,
}

impl Function {
    pub fn new(
        name: String,
        parameters: Vec<String>,
        node_id: Option<NodeId>,
        r#type: Option<Rc<RefCell<Type>>>,
    ) -> Self {
        Self {
            name,
            parameters,
            node_id,
            r#type,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn function_definition<'a>(
        &self,
        tree: &'a syntax::AST,
    ) -> Option<&'a syntax::FunctionDefinition> {
        self.node_id
            .map(|node_id| tree.get(node_id).unwrap().function_definition().unwrap())
    }
}

#[derive(Debug)]
pub struct Struct {
    name: String,
    fields: Vec<String>,
}

impl Struct {
    pub fn new(name: String, fields: Vec<String>) -> Self {
        Self { name, fields }
    }

    pub fn name(&self) -> &str {
        &self.name
    }
}

#[derive(Debug)]
pub struct Variable {
    name: String,
}

impl Variable {
    pub fn new(name: String) -> Self {
        Self { name }
    }

    pub fn name(&self) -> &str {
        &self.name
    }
}
