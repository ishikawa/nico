use super::{SyntaxToken, Token};
use crate::sem;
use std::cell::RefCell;
use std::rc::Rc;
use std::slice;

#[derive(Debug)]
pub struct Node {
    kind: NodeKind,
    code: Code,
}

#[derive(Debug)]
pub enum NodeKind {
    Program(Program),
    Name(Name),
    StructDefinition(StructDefinition),
    FunctionDefinition(FunctionDefinition),
    TypeField(TypeField),
    TypeAnnotation(TypeAnnotation),
    FunctionParameter(FunctionParameter),
    Statement(Statement),
    Expression(Expression),
}

#[derive(Debug, Default)]
pub struct Code {
    code: Vec<CodeKind>,
}

#[derive(Debug)]
pub enum CodeKind {
    Node(Rc<Node>),
    SyntaxToken(SyntaxToken),
}

#[derive(Debug)]
pub struct Program {
    pub body: Vec<Rc<Node>>,
}

impl Program {
    pub fn new(body: Vec<Rc<Node>>) -> Self {
        Self { body }
    }
}

#[derive(Debug)]
pub struct Name {
    pub name: String,
}

impl Name {
    pub fn new(name: String) -> Self {
        Self { name }
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
    pub name: Option<Rc<Node>>,
    pub fields: Vec<Rc<Node>>,
}

impl StructDefinition {
    pub fn new(name: Option<Rc<Node>>, fields: Vec<Rc<Node>>) -> Self {
        Self { name, fields }
    }
}

#[derive(Debug)]
pub struct TypeField {
    pub name: Option<Rc<Node>>,
    pub type_annotation: Option<Rc<Node>>,
}

impl TypeField {
    pub fn new(name: Option<Rc<Node>>, type_annotation: Option<Rc<Node>>) -> Self {
        Self {
            name,
            type_annotation,
        }
    }
}

#[derive(Debug)]
pub struct TypeAnnotation {
    pub name: Rc<Node>,
    pub r#type: Option<Rc<RefCell<sem::Type>>>,
}

impl TypeAnnotation {
    pub fn new(name: Rc<Node>) -> Self {
        Self { name, r#type: None }
    }
}

#[derive(Debug)]
pub struct FunctionDefinition {
    pub name: Option<Rc<Node>>,
    pub parameters: Vec<Rc<Node>>,
    pub body: Vec<Rc<Node>>,
}

impl FunctionDefinition {
    pub fn new(name: Option<Rc<Node>>, parameters: Vec<Rc<Node>>, body: Vec<Rc<Node>>) -> Self {
        Self {
            name,
            parameters,
            body,
        }
    }

    pub fn name(&self) -> Option<&Name> {
        self.name.as_ref().map(|x| x.name().unwrap())
    }
}

#[derive(Debug)]
pub struct FunctionParameter {
    pub name: Rc<Node>,
}

impl FunctionParameter {
    pub fn new(name: Rc<Node>) -> Self {
        Self { name }
    }

    pub fn name(&self) -> &Name {
        self.name.name().unwrap()
    }
}

#[derive(Debug)]
pub struct Statement {
    pub expression: Rc<Node>,
}

impl Statement {
    pub fn new(expression: Rc<Node>) -> Self {
        Self { expression }
    }

    pub fn expression(&self) -> &Expression {
        self.expression.expression().unwrap()
    }
}

#[derive(Debug)]
pub struct Expression {
    pub kind: ExpressionKind,
    pub r#type: Rc<RefCell<sem::Type>>,
}

impl Expression {
    pub fn new(kind: ExpressionKind, r#type: Rc<RefCell<sem::Type>>) -> Self {
        Self { kind, r#type }
    }

    pub fn is_call_expression(&self) -> bool {
        matches!(self.kind, ExpressionKind::CallExpression(_))
    }
}

impl Expression {
    pub fn identifier(&self) -> Option<&Identifier> {
        if let ExpressionKind::Identifier(ref expr) = self.kind {
            Some(expr)
        } else {
            None
        }
    }

    pub fn subscript_expression(&self) -> Option<&SubscriptExpression> {
        if let ExpressionKind::SubscriptExpression(ref expr) = self.kind {
            Some(expr)
        } else {
            None
        }
    }

    pub fn binary_expression(&self) -> Option<&BinaryExpression> {
        if let ExpressionKind::BinaryExpression(ref expr) = self.kind {
            Some(expr)
        } else {
            None
        }
    }

    pub fn unary_expression(&self) -> Option<&UnaryExpression> {
        if let ExpressionKind::UnaryExpression(ref expr) = self.kind {
            Some(expr)
        } else {
            None
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
    pub lhs: Rc<Node>,
    pub rhs: Option<Rc<Node>>,
}

#[derive(Debug)]
pub struct SubscriptExpression {
    pub callee: Rc<Node>,
    pub arguments: Vec<Rc<Node>>,
}

#[derive(Debug)]
pub struct CallExpression {
    pub callee: Rc<Node>,
    pub arguments: Vec<Rc<Node>>,
}

#[derive(Debug)]
pub struct UnaryExpression {
    pub operator: UnaryOperator,
    pub operand: Option<Rc<Node>>,
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

impl Code {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_interpreted(token: Token) -> Self {
        Self {
            code: vec![CodeKind::SyntaxToken(SyntaxToken::Interpreted(token))],
        }
    }

    pub fn with_node(node: &Rc<Node>) -> Self {
        Self {
            code: vec![CodeKind::Node(Rc::clone(node))],
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
    pub fn node(&mut self, node: &Rc<Node>) -> &mut Self {
        self.code.push(CodeKind::Node(Rc::clone(node)));
        self
    }
}

impl Node {
    pub fn new(kind: NodeKind, code: Code) -> Self {
        Self { kind, code }
    }

    pub fn kind(&self) -> &NodeKind {
        &self.kind
    }

    pub fn code(&self) -> slice::Iter<CodeKind> {
        self.code.iter()
    }

    pub fn program(&self) -> Option<&Program> {
        if let NodeKind::Program(ref node) = self.kind {
            Some(node)
        } else {
            None
        }
    }

    pub fn statement(&self) -> Option<&Statement> {
        if let NodeKind::Statement(ref node) = self.kind {
            Some(node)
        } else {
            None
        }
    }

    pub fn name(&self) -> Option<&Name> {
        if let NodeKind::Name(ref node) = self.kind {
            Some(node)
        } else {
            None
        }
    }

    pub fn function_definition(&self) -> Option<&FunctionDefinition> {
        if let NodeKind::FunctionDefinition(ref node) = self.kind {
            Some(node)
        } else {
            None
        }
    }

    pub fn function_parameter(&self) -> Option<&FunctionParameter> {
        if let NodeKind::FunctionParameter(ref node) = self.kind {
            Some(node)
        } else {
            None
        }
    }

    pub fn expression(&self) -> Option<&Expression> {
        if let NodeKind::Expression(ref expr) = self.kind {
            Some(expr)
        } else {
            None
        }
    }

    pub fn identifier(&self) -> Option<&Identifier> {
        if let Some(expr) = self.expression() {
            expr.identifier()
        } else {
            None
        }
    }

    pub fn unary_expression(&self) -> Option<&UnaryExpression> {
        if let Some(expr) = self.expression() {
            expr.unary_expression()
        } else {
            None
        }
    }

    pub fn is_function_definition(&self) -> bool {
        matches!(self.kind, NodeKind::FunctionDefinition(_))
    }

    pub fn is_function_parameter(&self) -> bool {
        matches!(self.kind, NodeKind::FunctionParameter(_))
    }

    pub fn is_expression(&self) -> bool {
        matches!(self.kind, NodeKind::Expression(_))
    }

    pub fn is_call_expression(&self) -> bool {
        if let Some(expr) = self.expression() {
            expr.is_call_expression()
        } else {
            false
        }
    }
}
