use crate::syntax::{self, NodeId};
use crate::{sem::Type, util::wrap};
use std::{cell::RefCell, fmt::Display, rc::Rc};

/// SemanticValue is a structure for storing the following data, separated from the abstract syntax tree
///
/// - Type and a node of the abstract syntax tree.
/// - The literals of the variables or structures and, in the case of patterns, the bindings to
///   which they refer. If the binding does not exist, it means that a name resolution error has occurred.
/// - In the case of patterns that introduce variables, store the variable name and the semantic
///   value that generated the value.
/// - For function definitions and declarations, function name and argument name
/// - For structure definitions and declarations, the structure and field names
#[derive(Debug)]
pub struct SemanticValue {
    /// The id of a syntax node where the semantic value was defined. `None` for built-ins.
    node_id: Option<NodeId>,
    r#type: Option<Rc<RefCell<Type>>>,
    /// Variants. `Undefined` for default value.
    kind: SemanticValueKind,
}

impl SemanticValue {
    pub fn builtin_function<S: Into<String>>(
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
        let value =
            FunctionDeclaration::new(name, param_names.into_iter().map(String::from).collect());

        Self::builtin(
            wrap(function_type),
            SemanticValueKind::FunctionDeclaration(value),
        )
    }

    pub fn builtin(r#type: Rc<RefCell<Type>>, kind: SemanticValueKind) -> Self {
        Self::new(None, Some(r#type), kind)
    }

    pub fn define(node_id: NodeId, r#type: Rc<RefCell<Type>>, kind: SemanticValueKind) -> Self {
        Self::new(Some(node_id), Some(r#type), kind)
    }

    pub fn new(
        node_id: Option<NodeId>,
        r#type: Option<Rc<RefCell<Type>>>,
        kind: SemanticValueKind,
    ) -> Self {
        Self {
            node_id,
            r#type,
            kind,
        }
    }

    pub fn node_id(&self) -> Option<NodeId> {
        self.node_id
    }

    /// Returns type. panic if the value is undefined.
    pub fn r#type(&self) -> &Rc<RefCell<Type>> {
        self.r#type.as_ref().expect("undefined value")
    }

    pub fn kind(&self) -> &SemanticValueKind {
        &self.kind
    }
}

impl Default for SemanticValue {
    fn default() -> Self {
        Self::new(None, None, SemanticValueKind::Undefined)
    }
}

/// Semantic value variants.
#[derive(Debug)]
pub enum SemanticValueKind {
    /// defined but no data
    Empty,
    /// Integer, string constant
    ConstantValue(ConstantValue),
    /// Function definition, built-in function
    FunctionDeclaration(FunctionDeclaration),
    /// Struct definition, built-in struct
    StructDeclaration(StructDeclaration),
    /// Let binding, patterns, function parameters
    VariableDeclaration(VariableDeclaration),
    /// Variable
    Binding(syntax::Binding),
    Undefined,
}

impl Default for SemanticValueKind {
    fn default() -> Self {
        Self::Undefined
    }
}

impl SemanticValueKind {
    pub fn constant_value(&self) -> Option<&ConstantValue> {
        if let SemanticValueKind::ConstantValue(value) = self {
            Some(value)
        } else {
            None
        }
    }

    pub fn function_declaration(&self) -> Option<&FunctionDeclaration> {
        if let SemanticValueKind::FunctionDeclaration(function) = self {
            Some(function)
        } else {
            None
        }
    }

    pub fn struct_declaration(&self) -> Option<&StructDeclaration> {
        if let SemanticValueKind::StructDeclaration(value) = self {
            Some(value)
        } else {
            None
        }
    }

    pub fn variable_declaration(&self) -> Option<&VariableDeclaration> {
        if let SemanticValueKind::VariableDeclaration(value) = self {
            Some(value)
        } else {
            None
        }
    }

    pub fn binding(&self) -> Option<&syntax::Binding> {
        if let SemanticValueKind::Binding(value) = self {
            Some(value)
        } else {
            None
        }
    }

    pub fn is_constant_value(&self) -> bool {
        matches!(self, SemanticValueKind::ConstantValue(_))
    }

    pub fn is_function_declaration(&self) -> bool {
        matches!(self, SemanticValueKind::FunctionDeclaration(_))
    }

    pub fn is_struct_declaration(&self) -> bool {
        matches!(self, SemanticValueKind::StructDeclaration(_))
    }

    pub fn is_variable_declaration(&self) -> bool {
        matches!(self, SemanticValueKind::VariableDeclaration(_))
    }

    pub fn is_binding(&self) -> bool {
        matches!(self, SemanticValueKind::Binding(_))
    }

    pub fn is_undefined(&self) -> bool {
        matches!(self, SemanticValueKind::Undefined)
    }

    pub fn is_function_parameter(&self) -> bool {
        self.variable_declaration()
            .filter(|v| v.is_function_parameter())
            .is_some()
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct ConstantValue {
    kind: ConstantValueKind,
}

impl ConstantValue {
    pub fn new(kind: ConstantValueKind) -> Self {
        Self { kind }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Clone)]
pub enum ConstantValueKind {
    Int32(i32),
    String(String),
}

impl Display for ConstantValueKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstantValueKind::Int32(value) => value.fmt(f),
            ConstantValueKind::String(value) => value.fmt(f),
        }
    }
}

#[derive(Debug)]
pub struct FunctionDeclaration {
    name: String,
    parameter_names: Vec<String>,
}

impl FunctionDeclaration {
    pub fn new(name: String, parameter_names: Vec<String>) -> Self {
        Self {
            name,
            parameter_names,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn parameter_names(&self) -> impl Iterator<Item = &str> {
        self.parameter_names.iter().map(AsRef::as_ref)
    }
}

#[derive(Debug)]
pub struct StructDeclaration {
    name: String,
    field_names: Vec<String>,
}

impl StructDeclaration {
    pub fn new(name: String, field_names: Vec<String>) -> Self {
        Self { name, field_names }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn field_names(&self) -> impl Iterator<Item = &str> {
        self.field_names.iter().map(AsRef::as_ref)
    }
}

#[derive(Debug)]
pub struct VariableDeclaration {
    name: String,
    is_function_parameter: bool,
}

impl VariableDeclaration {
    pub fn new(name: String, is_function_parameter: bool) -> Self {
        Self {
            name,
            is_function_parameter,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn is_function_parameter(&self) -> bool {
        self.is_function_parameter
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
