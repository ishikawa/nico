use crate::syntax::{self, NodeId};
use crate::{sem::Type, util::wrap};
use std::{
    cell::{Ref, RefCell},
    ops::Deref,
    rc::Rc,
};

/// Semantic value variants.
#[derive(Debug, Clone)]
pub enum SemanticValueKind {
    Function(Rc<RefCell<Function>>),
    Struct(Rc<RefCell<Struct>>),
    Variable(Rc<RefCell<Variable>>),
    /// Typed value (e.g. Expression)
    Expression(Rc<RefCell<Expression>>),
    Undefined,
}

impl Default for SemanticValueKind {
    fn default() -> Self {
        Self::Undefined
    }
}

impl SemanticValueKind {
    pub fn node_id(&self) -> Option<NodeId> {
        match self {
            SemanticValueKind::Function(function) => function.borrow().node_id(),
            SemanticValueKind::Struct(r#struct) => r#struct.borrow().node_id(),
            SemanticValueKind::Variable(variable) => variable.borrow().node_id(),
            SemanticValueKind::Expression(expression) => Some(expression.borrow().node_id()),
            _ => None,
        }
    }

    pub fn r#type(&self) -> Option<Rc<RefCell<Type>>> {
        match self {
            SemanticValueKind::Function(function) => Some(Rc::clone(function.borrow().r#type())),
            SemanticValueKind::Struct(r#struct) => Some(Rc::clone(r#struct.borrow().r#type())),
            SemanticValueKind::Variable(variable) => Some(Rc::clone(variable.borrow().r#type())),
            SemanticValueKind::Expression(expression) => {
                Some(Rc::clone(expression.borrow().r#type()))
            }
            _ => None,
        }
    }

    pub fn name(&self) -> Option<impl Deref<Target = str> + '_> {
        match self {
            SemanticValueKind::Function(function) => {
                Some(Ref::map(function.borrow(), |b| b.name()))
            }
            SemanticValueKind::Struct(r#struct) => Some(Ref::map(r#struct.borrow(), |b| b.name())),
            SemanticValueKind::Variable(variable) => {
                Some(Ref::map(variable.borrow(), |b| b.name()))
            }
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
            SemanticValueKind::Expression(expression) => {
                if let Some(other) = other.expression() {
                    return std::ptr::eq(expression, other);
                }
            }
            SemanticValueKind::Undefined => {
                return false;
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

    pub fn expression(&self) -> Option<&Rc<RefCell<Expression>>> {
        if let SemanticValueKind::Expression(value) = self {
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

    pub fn is_expression(&self) -> bool {
        matches!(self, SemanticValueKind::Expression(_))
    }

    pub fn is_undefined(&self) -> bool {
        matches!(self, SemanticValueKind::Undefined)
    }

    pub fn is_function_parameter(&self) -> bool {
        self.variable()
            .filter(|v| v.borrow().is_function_parameter())
            .is_some()
    }
}

#[derive(Debug)]
pub struct Function {
    name: String,
    parameters: Vec<String>,
    node_id: Option<NodeId>, // syntax::FunctionDefinition. None for builtin.
    r#type: Rc<RefCell<Type>>,
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
            wrap(function_type),
        )
    }

    pub fn new(
        name: String,
        parameters: Vec<String>,
        node_id: Option<NodeId>,
        r#type: Rc<RefCell<Type>>,
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

    pub fn r#type(&self) -> &Rc<RefCell<Type>> {
        &self.r#type
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
    r#type: Rc<RefCell<Type>>,
}

impl Struct {
    pub fn new(
        name: String,
        fields: Vec<String>,
        node_id: Option<NodeId>,
        r#type: Rc<RefCell<Type>>,
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

    pub fn r#type(&self) -> &Rc<RefCell<Type>> {
        &self.r#type
    }

    pub fn get_field_type(&self, field: &str) -> Option<Rc<RefCell<Type>>> {
        let ty = self.r#type().borrow();
        let struct_type = ty.struct_type()?;
        let field = struct_type.fields().get(field)?;

        Some(Rc::clone(field))
    }
}

#[derive(Debug)]
pub struct Variable {
    name: String,
    is_function_parameter: bool,
    node_id: Option<NodeId>, // syntax::Identifier. None for builtin.
    r#type: Rc<RefCell<Type>>,
}

impl Variable {
    pub fn new(
        name: String,
        is_function_parameter: bool,
        node_id: Option<NodeId>,
        r#type: Rc<RefCell<Type>>,
    ) -> Self {
        Self {
            name,
            is_function_parameter,
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

    pub fn is_function_parameter(&self) -> bool {
        self.is_function_parameter
    }

    pub fn r#type(&self) -> &Rc<RefCell<Type>> {
        &self.r#type
    }
}

#[derive(Debug)]
pub struct Expression {
    node_id: NodeId, // syntax::Expression
    r#type: Rc<RefCell<Type>>,
}

impl Expression {
    pub fn new(node_id: NodeId, r#type: Rc<RefCell<Type>>) -> Self {
        Self { node_id, r#type }
    }

    pub fn node_id(&self) -> NodeId {
        self.node_id
    }

    pub fn r#type(&self) -> &Rc<RefCell<Type>> {
        &self.r#type
    }
}
