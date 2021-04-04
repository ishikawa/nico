use super::{SyntaxToken, Token};
use crate::sem;
use std::cell::RefCell;
use std::rc::Rc;
use std::slice;

#[derive(Debug)]
pub enum TopLevelKind {
    StructDefinition(Rc<StructDefinition>),
    FunctionDefinition(Rc<FunctionDefinition>),
    Statement(Rc<Statement>),
}

#[derive(Debug)]
pub enum NodeKind {
    Name(Rc<Name>),
    StructDefinition(Rc<StructDefinition>),
    FunctionDefinition(Rc<FunctionDefinition>),
    TypeField(Rc<TypeField>),
    TypeAnnotation(Rc<TypeAnnotation>),
    FunctionParameter(Rc<FunctionParameter>),
    Statement(Rc<Statement>),
    Expression(Rc<Expression>),
}

#[derive(Debug)]
pub enum CodeKind {
    NodeKind(NodeKind),
    SyntaxToken(SyntaxToken),
}

#[derive(Debug)]
pub struct Program {
    pub body: Vec<TopLevelKind>,
    code: Code,
}

impl Program {
    pub fn new(body: Vec<TopLevelKind>, code: Code) -> Self {
        Self { body, code }
    }
}

#[derive(Debug)]
pub struct Name {
    pub name: String,
    code: Code,
}

impl Name {
    pub fn new(name: String, code: Code) -> Self {
        Self { name, code }
    }
}

/// Types
/// -----
/// ```ignore
/// definition  := struct
/// struct      := "struct" name "{" fields "}"
/// fields      := field | fields ","
/// field       := name ":" type
/// type        := name
/// name        := IDENT
/// ```
///
#[derive(Debug)]
pub struct StructDefinition {
    pub name: Option<Rc<Name>>,
    pub fields: Vec<Rc<TypeField>>,
    code: Code,
}

impl StructDefinition {
    pub fn new(name: Option<Rc<Name>>, fields: Vec<Rc<TypeField>>, code: Code) -> Self {
        Self { name, fields, code }
    }
}

#[derive(Debug)]
pub struct TypeField {
    pub name: Option<Rc<Name>>,
    pub type_annotation: Option<Rc<TypeAnnotation>>,
    code: Code,
}

impl TypeField {
    pub fn new(
        name: Option<Rc<Name>>,
        type_annotation: Option<Rc<TypeAnnotation>>,
        code: Code,
    ) -> Self {
        Self {
            name,
            type_annotation,
            code,
        }
    }
}

#[derive(Debug)]
pub struct TypeAnnotation {
    pub name: Rc<Name>,
    pub r#type: Option<Rc<RefCell<sem::Type>>>,
}

impl TypeAnnotation {
    pub fn new(name: Rc<Name>) -> Self {
        Self { name, r#type: None }
    }
}

#[derive(Debug)]
pub struct FunctionDefinition {
    pub name: Option<Rc<Name>>,
    pub parameters: Vec<Rc<FunctionParameter>>,
    pub body: Vec<Rc<Statement>>,
    code: Code,
}

impl FunctionDefinition {
    pub fn new(
        name: Option<Rc<Name>>,
        parameters: Vec<Rc<FunctionParameter>>,
        body: Vec<Rc<Statement>>,
        code: Code,
    ) -> Self {
        Self {
            name,
            parameters,
            body,
            code,
        }
    }
}

#[derive(Debug)]
pub struct FunctionParameter {
    pub name: Rc<Name>,
    code: Code,
}

impl FunctionParameter {
    pub fn new(name: Rc<Name>, code: Code) -> Self {
        Self { name, code }
    }
}

#[derive(Debug)]
pub struct Statement {
    pub expression: Rc<Expression>,
}

impl Statement {
    pub fn new(expression: Rc<Expression>) -> Self {
        Self { expression }
    }
}

#[derive(Debug)]
pub struct Expression {
    pub kind: ExpressionKind,
    pub r#type: Rc<RefCell<sem::Type>>,
    code: Code,
}

impl Expression {
    pub fn new(kind: ExpressionKind, r#type: Rc<RefCell<sem::Type>>, code: Code) -> Self {
        Self { kind, r#type, code }
    }
}

impl Expression {
    pub fn unwrap_identifier(&self) -> &Identifier {
        if let ExpressionKind::Identifier(ref expr) = self.kind {
            expr
        } else {
            panic!("Expected identifier");
        }
    }

    pub fn unwrap_subscript_expression(&self) -> &SubscriptExpression {
        if let ExpressionKind::SubscriptExpression(ref expr) = self.kind {
            expr
        } else {
            panic!("Expected subscript expression");
        }
    }

    pub fn unwrap_binary_expression(&self) -> &BinaryExpression {
        if let ExpressionKind::BinaryExpression(ref expr) = self.kind {
            expr
        } else {
            panic!("Expected binary expression");
        }
    }

    pub fn unwrap_unary_expression(&self) -> &UnaryExpression {
        if let ExpressionKind::UnaryExpression(ref expr) = self.kind {
            expr
        } else {
            panic!("Expected unary expression");
        }
    }
}

#[derive(Debug)]
pub struct IntegerLiteral(pub i32);

#[derive(Debug)]
pub struct StringLiteral(pub Option<String>);

#[derive(Debug)]
pub struct Identifier(pub String);

#[derive(Debug)]
pub struct BinaryExpression {
    pub operator: BinaryOperator,
    pub lhs: Rc<Expression>,
    pub rhs: Option<Rc<Expression>>,
}

#[derive(Debug)]
pub struct SubscriptExpression {
    pub callee: Rc<Expression>,
    pub arguments: Vec<Rc<Expression>>,
}

#[derive(Debug)]
pub struct CallExpression {
    pub callee: Rc<Expression>,
    pub arguments: Vec<Rc<Expression>>,
}

#[derive(Debug)]
pub struct UnaryExpression {
    pub operator: UnaryOperator,
    pub operand: Option<Rc<Expression>>,
}

#[derive(Debug, Copy, Clone)]
pub enum BinaryOperator {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Lt,
    Gt,
    Le,
    Ge,
    Eq,
    Ne,
}

#[derive(Debug, Copy, Clone)]
pub enum UnaryOperator {
    Minus,
    Plus,
}

#[derive(Debug)]
pub enum ExpressionKind {
    IntegerLiteral(IntegerLiteral),
    StringLiteral(StringLiteral),
    Identifier(Identifier),
    BinaryExpression(BinaryExpression),
    UnaryExpression(UnaryExpression),
    SubscriptExpression(SubscriptExpression),
    CallExpression(CallExpression),
}

// Code
#[derive(Debug, Default)]
pub struct Code {
    code: Vec<CodeKind>,
}

impl Code {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_interpreted(token: Token) -> Self {
        Self {
            code: vec![CodeKind::SyntaxToken(SyntaxToken::Interpreted(token))],
        }
    }

    pub fn interpret(&mut self, token: Token) -> &mut Self {
        self.code
            .push(CodeKind::SyntaxToken(SyntaxToken::Interpreted(token)));
        self
    }

    pub fn missing(&mut self, token: Token) -> &mut Self {
        self.code
            .push(CodeKind::SyntaxToken(SyntaxToken::Missing(token)));
        self
    }

    pub fn skip<S: Into<String>>(&mut self, token: Token, expected: S) -> &mut Self {
        self.code.push(CodeKind::SyntaxToken(SyntaxToken::Skipped {
            token,
            expected: expected.into(),
        }));
        self
    }

    pub fn iter(&self) -> slice::Iter<CodeKind> {
        self.code.iter()
    }

    // children
    pub fn node(&mut self, node: NodeKind) -> &mut Self {
        self.code.push(CodeKind::NodeKind(node));
        self
    }

    pub fn name(&mut self, node: &Rc<Name>) -> &mut Self {
        self.node(NodeKind::Name(Rc::clone(node)))
    }

    pub fn struct_definition(&mut self, node: &Rc<StructDefinition>) -> &mut Self {
        self.node(NodeKind::StructDefinition(Rc::clone(node)))
    }

    pub fn function_definition(&mut self, node: &Rc<FunctionDefinition>) -> &mut Self {
        self.node(NodeKind::FunctionDefinition(Rc::clone(node)))
    }

    pub fn statement(&mut self, node: &Rc<Statement>) -> &mut Self {
        self.node(NodeKind::Statement(Rc::clone(node)))
    }

    pub fn expression(&mut self, node: &Rc<Expression>) -> &mut Self {
        self.node(NodeKind::Expression(Rc::clone(node)))
    }
}

pub trait CodeIterable {
    fn code(&self) -> slice::Iter<CodeKind>;
}

impl CodeIterable for Code {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.iter()
    }
}

impl CodeIterable for NodeKind {
    fn code(&self) -> slice::Iter<CodeKind> {
        match self {
            NodeKind::Name(node) => node.code(),
            NodeKind::StructDefinition(node) => node.code(),
            NodeKind::FunctionDefinition(node) => node.code(),
            NodeKind::TypeField(node) => node.code(),
            NodeKind::TypeAnnotation(node) => node.code(),
            NodeKind::FunctionParameter(node) => node.code(),
            NodeKind::Statement(node) => node.code(),
            NodeKind::Expression(node) => node.code(),
        }
    }
}

impl CodeIterable for Program {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.code()
    }
}

impl CodeIterable for Name {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.code()
    }
}

impl CodeIterable for StructDefinition {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.code()
    }
}

impl CodeIterable for TypeField {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.code()
    }
}

impl CodeIterable for TypeAnnotation {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.name.code()
    }
}

impl CodeIterable for FunctionDefinition {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.code()
    }
}

impl CodeIterable for FunctionParameter {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.code()
    }
}

impl CodeIterable for Statement {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.expression.code()
    }
}

impl CodeIterable for Expression {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.code()
    }
}
