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
        }
    }

    pub fn r#type(&self) -> Option<impl Deref<Target = Rc<RefCell<Type>>> + '_> {
        match self {
            SemanticValueKind::Function(function) => {
                let borrowed = function.borrow();

                if borrowed.r#type.is_none() {
                    None
                } else {
                    Some(Ref::map(borrowed, |b| b.r#type.as_ref().unwrap()))
                }
            }
            SemanticValueKind::Struct(r#struct) => {
                let borrowed = r#struct.borrow();

                if borrowed.r#type.is_none() {
                    None
                } else {
                    Some(Ref::map(borrowed, |b| b.r#type.as_ref().unwrap()))
                }
            }
            SemanticValueKind::Variable(variable) => {
                let borrowed = variable.borrow();

                if borrowed.r#type.is_none() {
                    None
                } else {
                    Some(Ref::map(borrowed, |b| b.r#type.as_ref().unwrap()))
                }
            }
        }
    }

    pub fn name(&self) -> impl Deref<Target = str> + '_ {
        match self {
            SemanticValueKind::Function(value) => Ref::map(value.borrow(), |b| b.name()),
            SemanticValueKind::Struct(value) => Ref::map(value.borrow(), |b| b.name()),
            SemanticValueKind::Variable(value) => Ref::map(value.borrow(), |b| b.name()),
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

    pub fn is_function_parameter(&self) -> bool {
        todo!()
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
        parameters: Vec<(&str, Type)>,
        return_type: Type,
    ) -> Self {
        let (param_names, param_types): (Vec<_>, Vec<_>) = parameters.into_iter().unzip();

        let function_type = Type::Function {
            params: param_types.into_iter().map(wrap).collect(),
            return_type: wrap(return_type),
        };
        let name = name.into();
        Self::new(
            name,
            param_names.into_iter().map(String::from).collect(),
            None,
            Some(wrap(function_type)),
        )
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
        tree: &'a syntax::Ast,
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

    pub fn get_field_type(&self, field: &str) -> Option<Rc<RefCell<Type>>> {
        let ty = self.r#type()?.borrow();
        let struct_type = ty.struct_type()?;
        let field = struct_type.fields().get(field)?;

        Some(Rc::clone(field))
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
