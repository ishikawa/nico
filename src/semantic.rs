use crate::syntax::{self, NodeId};
use crate::{sem::Type, util::wrap};
use std::{
    cell::{Ref, RefCell},
    ops::Deref,
    rc::Rc,
};

#[derive(Debug, Clone)]
pub enum SemanticValueKind {
    Function(Rc<RefCell<Function>>),
    Struct(Rc<RefCell<Struct>>),
    Variable(Rc<RefCell<Variable>>),
}

impl SemanticValueKind {
    pub fn node_id(&self) -> Option<NodeId> {
        match self {
            SemanticValueKind::Function(function) => function.borrow().node_id(),
            SemanticValueKind::Struct(r#struct) => r#struct.borrow().node_id(),
            SemanticValueKind::Variable(variable) => variable.borrow().node_id(),
            _ => None,
        }
    }

    pub fn r#type(&self) -> Option<impl Deref<Target = Rc<RefCell<Type>>> + '_> {
        match self {
            SemanticValueKind::Function(function) => {
                let fun = function.borrow();

                if fun.r#type.is_none() {
                    None
                } else {
                    Some(Ref::map(fun, |f| f.r#type.as_ref().unwrap()))
                }
            }
            SemanticValueKind::Struct(r#struct) => {
                let borrowed = r#struct.borrow();

                if borrowed.r#type.is_none() {
                    None
                } else {
                    Some(Ref::map(borrowed, |f| f.r#type.as_ref().unwrap()))
                }
            }
            SemanticValueKind::Variable(variable) => {
                let borrowed = variable.borrow();

                if borrowed.r#type.is_none() {
                    None
                } else {
                    Some(Ref::map(borrowed, |f| f.r#type.as_ref().unwrap()))
                }
            }
            _ => None,
        }
    }

    pub fn name(&self) -> Option<&str> {
        match self {
            SemanticValueKind::Function(function) => Some(function.borrow().name()),
            SemanticValueKind::Struct(r#struct) => Some(r#struct.borrow().name()),
            SemanticValueKind::Variable(variable) => Some(variable.borrow().name()),
            _ => None,
        }
    }

    pub fn ptr_eq(&self, other: Self) -> bool {
        match self {
            SemanticValueKind::Function(fun) => {
                if let Some(other) = other.function() {
                    return std::ptr::eq(fun, other);
                }
            }
            SemanticValueKind::Struct(r#struct) => {
                if let Some(other) = other.r#struct() {
                    return std::ptr::eq(r#struct, other);
                }
            }
            SemanticValueKind::Variable(variable) => {
                if let Some(other) = other.variable() {
                    return std::ptr::eq(variable, other);
                }
            }
            _ => {}
        };

        false
    }

    pub fn function(&self) -> Option<&Rc<RefCell<Function>>> {
        if let SemanticValueKind::Function(function) = self {
            Some(function)
        } else {
            None
        }
    }

    pub fn r#struct(&self) -> Option<&Rc<RefCell<Struct>>> {
        if let SemanticValueKind::Struct(value) = self {
            Some(value)
        } else {
            None
        }
    }

    pub fn variable(&self) -> Option<&Rc<RefCell<Variable>>> {
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

        Self::new(name, parameters, None, Some(wrap(function_type)))
    }

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

    pub fn node_id(&self) -> Option<NodeId> {
        self.node_id
    }

    pub fn r#type(&self) -> Option<&Rc<RefCell<Type>>> {
        self.r#type.as_ref()
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
    node_id: Option<NodeId>, // syntax::StrutDefinition. None for builtin.
    r#type: Option<Rc<RefCell<Type>>>,
}

impl Struct {
    pub fn new(
        name: String,
        fields: Vec<String>,
        node_id: Option<NodeId>,
        r#type: Option<Rc<RefCell<Type>>>,
    ) -> Self {
        Self {
            name,
            fields,
            node_id,
            r#type,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn node_id(&self) -> Option<NodeId> {
        self.node_id
    }

    pub fn r#type(&self) -> Option<&Rc<RefCell<Type>>> {
        self.r#type.as_ref()
    }

    pub fn get_field_type(&self, field: &str) -> Option<&Rc<RefCell<Type>>> {
        let ty = self.r#type()?;
        let struct_type = ty.borrow().struct_type()?;

        struct_type.fields().get(field)
    }
}

#[derive(Debug)]
pub struct Variable {
    name: String,
    node_id: Option<NodeId>, // syntax::Identifier. None for builtin.
    r#type: Option<Rc<RefCell<Type>>>,
}

impl Variable {
    pub fn new(name: String, node_id: Option<NodeId>, r#type: Option<Rc<RefCell<Type>>>) -> Self {
        Self {
            name,
            node_id,
            r#type,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn node_id(&self) -> Option<NodeId> {
        self.node_id
    }

    pub fn r#type(&self) -> Option<&Rc<RefCell<Type>>> {
        self.r#type.as_ref()
    }
}
