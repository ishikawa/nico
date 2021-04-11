use super::{MissingTokenKind, Position, Scope, SyntaxToken, Token};
use crate::{sem, util::wrap};
use std::rc::Rc;
use std::slice;
use std::{cell::RefCell, fmt};

#[derive(Debug)]
pub struct Node {
    kind: NodeKind,
    code: Code,
}

#[derive(Debug)]
pub enum NodeKind {
    Program(Program),
    Block(Block),
    Identifier(Identifier),
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
    pub declarations: Rc<RefCell<Scope>>,
    pub main_scope: Rc<RefCell<Scope>>,
}

impl Program {
    pub fn new(body: Vec<Rc<Node>>) -> Self {
        let declarations = wrap(Scope::new());
        let main_scope = wrap(Scope::new());

        main_scope.borrow_mut().parent = Rc::downgrade(&declarations);

        Self {
            body,
            declarations,
            main_scope,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Identifier(String);

impl Identifier {
    pub fn new<S: Into<String>>(name: S) -> Self {
        Self(name.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
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

    pub fn name(&self) -> Option<&Identifier> {
        self.name.as_ref().map(|x| x.identifier().unwrap())
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
    pub body: Rc<Node>,
}

impl FunctionDefinition {
    pub fn new(name: Option<Rc<Node>>, parameters: Vec<Rc<Node>>, body: Rc<Node>) -> Self {
        Self {
            name,
            parameters,
            body,
        }
    }

    pub fn name(&self) -> Option<&Identifier> {
        self.name.as_ref().map(|x| x.identifier().unwrap())
    }

    pub fn body(&self) -> &Block {
        self.body.block().unwrap()
    }

    pub fn parameters(&self) -> FunctionParameters {
        FunctionParameters {
            iter: self.parameters.iter(),
            len: self.parameters.len(),
        }
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

    pub fn name(&self) -> &Identifier {
        self.name.identifier().unwrap()
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
pub struct Block {
    pub statements: Vec<Rc<Node>>,
    pub scope: Rc<RefCell<Scope>>,
}

impl Block {
    pub fn new(statements: Vec<Rc<Node>>) -> Self {
        Self {
            statements,
            scope: wrap(Scope::new()),
        }
    }

    pub fn statements(&self) -> Statements {
        Statements {
            iter: self.statements.iter(),
            len: self.statements.len(),
        }
    }
}

#[derive(Debug)]
pub struct Expression {
    pub kind: ExpressionKind,
    pub r#type: Rc<RefCell<sem::Type>>,
}

#[derive(Debug)]
pub struct IntegerLiteral(pub i32);

#[derive(Debug)]
pub struct StringLiteral(pub Option<String>);

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

impl SubscriptExpression {
    pub fn new(callee: Rc<Node>, arguments: Vec<Rc<Node>>) -> Self {
        Self { callee, arguments }
    }

    pub fn callee(&self) -> &Expression {
        self.callee.expression().unwrap()
    }

    pub fn arguments(&self) -> Arguments {
        Arguments {
            iter: self.arguments.iter(),
            len: self.arguments.len(),
        }
    }
}

#[derive(Debug)]
pub struct CallExpression {
    pub callee: Rc<Node>,
    pub arguments: Vec<Rc<Node>>,
}

impl CallExpression {
    pub fn new(callee: Rc<Node>, arguments: Vec<Rc<Node>>) -> Self {
        Self { callee, arguments }
    }

    pub fn callee(&self) -> &Expression {
        self.callee.expression().unwrap()
    }

    pub fn arguments(&self) -> Arguments {
        Arguments {
            iter: self.arguments.iter(),
            len: self.arguments.len(),
        }
    }
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
    VariableExpression(Identifier),
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

    pub fn missing(&mut self, position: Position, item: MissingTokenKind) -> &mut Self {
        self.code.push(CodeKind::SyntaxToken(SyntaxToken::Missing {
            position,
            item,
        }));
        self
    }

    pub fn skip(&mut self, token: Token, expected: MissingTokenKind) -> &mut Self {
        self.code.push(CodeKind::SyntaxToken(SyntaxToken::Skipped {
            token,
            expected,
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

    pub fn block(&self) -> Option<&Block> {
        if let NodeKind::Block(ref node) = self.kind {
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

    pub fn identifier(&self) -> Option<&Identifier> {
        if let NodeKind::Identifier(ref node) = self.kind {
            Some(node)
        } else {
            None
        }
    }

    pub fn struct_definition(&self) -> Option<&StructDefinition> {
        if let NodeKind::StructDefinition(ref node) = self.kind {
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

    pub fn variable_expression(&self) -> Option<&Identifier> {
        if let Some(expr) = self.expression() {
            expr.variable_expression()
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

    pub fn is_variable_expression(&self) -> bool {
        self.variable_expression().is_some()
    }

    pub fn is_call_expression(&self) -> bool {
        if let Some(expr) = self.expression() {
            expr.is_call_expression()
        } else {
            false
        }
    }
}

impl Expression {
    pub fn new(kind: ExpressionKind, r#type: Rc<RefCell<sem::Type>>) -> Self {
        Self { kind, r#type }
    }

    pub fn is_call_expression(&self) -> bool {
        matches!(self.kind, ExpressionKind::CallExpression(_))
    }

    pub fn variable_expression(&self) -> Option<&Identifier> {
        if let ExpressionKind::VariableExpression(ref expr) = self.kind {
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

// -- Iterators
#[derive(Debug, Clone)]
pub struct Arguments<'a> {
    iter: slice::Iter<'a, Rc<Node>>,
    len: usize,
}

impl<'a> Arguments<'a> {
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<'a> Iterator for Arguments<'a> {
    type Item = &'a Expression;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().as_ref().map(|x| x.expression().unwrap())
    }
}

#[derive(Debug, Clone)]
pub struct Statements<'a> {
    iter: slice::Iter<'a, Rc<Node>>,
    len: usize,
}

impl<'a> Statements<'a> {
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<'a> Iterator for Statements<'a> {
    type Item = &'a Statement;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().as_ref().map(|x| x.statement().unwrap())
    }
}

#[derive(Debug, Clone)]
pub struct FunctionParameters<'a> {
    iter: slice::Iter<'a, Rc<Node>>,
    len: usize,
}

impl<'a> FunctionParameters<'a> {
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<'a> Iterator for FunctionParameters<'a> {
    type Item = &'a FunctionParameter;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()
            .as_ref()
            .map(|x| x.function_parameter().unwrap())
    }
}

impl fmt::Display for NodeKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NodeKind::Program(_) => write!(f, "Program"),
            NodeKind::Block(_) => write!(f, "Block"),
            NodeKind::Identifier(_) => write!(f, "Identifier"),
            NodeKind::StructDefinition(_) => write!(f, "StructDefinition"),
            NodeKind::FunctionDefinition(_) => write!(f, "FunctionDefinition"),
            NodeKind::TypeField(_) => write!(f, "TypeField"),
            NodeKind::TypeAnnotation(_) => write!(f, "TypeAnnotation"),
            NodeKind::FunctionParameter(_) => write!(f, "FunctionParameter"),
            NodeKind::Statement(_) => write!(f, "Statement"),
            NodeKind::Expression(Expression { kind, .. }) => write!(f, "{}", kind),
        }
    }
}

impl fmt::Display for ExpressionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExpressionKind::IntegerLiteral(_) => write!(f, "IntegerLiteral"),
            ExpressionKind::StringLiteral(_) => write!(f, "StringLiteral"),
            ExpressionKind::VariableExpression(_) => write!(f, "VariableExpression"),
            ExpressionKind::BinaryExpression(_) => write!(f, "BinaryExpression"),
            ExpressionKind::UnaryExpression(_) => write!(f, "UnaryExpression"),
            ExpressionKind::SubscriptExpression(_) => write!(f, "SubscriptExpression"),
            ExpressionKind::CallExpression(_) => write!(f, "CallExpression"),
        }
    }
}
