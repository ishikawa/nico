use crate::sem;
use crate::syntax::NodeId;
use std::{cell::RefCell, rc::Rc};

#[derive(Debug)]
pub struct SemanticValue {
    kind: SemanticValueKind,

    /// The node id for a node where this value is defined. `None` for builtin values.
    /// - `Function` - syntax::FunctionDefinition
    /// - `Struct` - syntax::StructDefinition
    /// - `Variable` - syntax::Identifier
    node_id: Option<NodeId>, // syntax::FunctionDefinition. None for builtin.
    r#type: Option<Rc<RefCell<sem::Type>>>,
}

impl SemanticValue {
    pub fn new(
        kind: SemanticValueKind,
        node_id: Option<NodeId>,
        r#type: Option<&Rc<RefCell<sem::Type>>>,
    ) -> Self {
        Self {
            kind,
            node_id,
            r#type: r#type.map(Rc::clone),
        }
    }

    pub fn kind(&self) -> &SemanticValueKind {
        &self.kind
    }

    pub fn node_id(&self) -> Option<NodeId> {
        self.node_id
    }

    pub fn r#type(&self) -> Option<&Rc<RefCell<sem::Type>>> {
        self.r#type.as_ref()
    }
}

#[derive(Debug)]
pub enum SemanticValueKind {
    Function(Function),
    Struct(Struct),
    Variable(Variable),
}

#[derive(Debug)]
pub struct Function {
    name: String,
    parameters: Vec<String>,
}

impl Function {
    pub fn new(name: String, parameters: Vec<String>) -> Self {
        Self { name, parameters }
    }
}

#[derive(Debug)]
pub struct Struct {
    name: String,
    fields: Vec<String>,
}

#[derive(Debug)]
pub struct Variable {
    name: String,
}
