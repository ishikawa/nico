use crate::sem;
use crate::syntax::NodeId;
use std::{cell::RefCell, rc::Rc};

#[derive(Debug)]
pub struct Function {
    name: Option<String>,
    parameters: Vec<String>,
    r#type: Option<Rc<RefCell<sem::Type>>>,
    node: Option<NodeId>, // syntax::FunctionDefinition
}

#[derive(Debug)]
pub struct Struct {
    name: Option<String>,
    fields: Vec<String>,
    r#type: Option<Rc<RefCell<sem::Type>>>,
    node: Option<NodeId>, // syntax::StructDefinition
}
