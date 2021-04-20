use super::{EffectiveRange, MissingTokenKind, Scope, SyntaxToken, Token};
use crate::{sem, util::wrap};
use std::rc::Rc;
use std::slice;
use std::{cell::RefCell, fmt};

#[derive(Debug)]
pub enum NodeKind {
    Program(Rc<Program>),
    Block(Rc<Block>),
    Identifier(Rc<Identifier>),
    StructDefinition(Rc<StructDefinition>),
    FunctionDefinition(Rc<FunctionDefinition>),
    TypeField(Rc<TypeField>),
    TypeAnnotation(Rc<TypeAnnotation>),
    FunctionParameter(Rc<FunctionParameter>),
    Statement(Rc<Statement>),
    Expression(Rc<Expression>),
    Pattern(Rc<Pattern>),
    Unit, // ()
}

#[derive(Debug)]
pub enum TopLevelKind {
    StructDefinition(Rc<StructDefinition>),
    FunctionDefinition(Rc<FunctionDefinition>),
    Statement(Rc<Statement>),
}

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

    pub fn with_node(node: NodeKind) -> Self {
        Self {
            code: vec![CodeKind::Node(node)],
        }
    }

    pub fn interpret(&mut self, token: Token) -> &mut Self {
        self.code
            .push(CodeKind::SyntaxToken(SyntaxToken::Interpreted(token)));
        self
    }

    pub fn missing(&mut self, range: EffectiveRange, item: MissingTokenKind) -> &mut Self {
        self.code
            .push(CodeKind::SyntaxToken(SyntaxToken::Missing { range, item }));
        self
    }

    pub fn skip(&mut self, token: Token, expected: MissingTokenKind) -> &mut Self {
        self.code.push(CodeKind::SyntaxToken(SyntaxToken::Skipped {
            token,
            expected,
        }));
        self
    }

    pub fn iter(&self) -> CodeKinds {
        CodeKinds {
            iter: self.code.iter(),
            len: self.code.len(),
        }
    }

    // children
    pub fn node(&mut self, node: NodeKind) -> &mut Self {
        self.code.push(CodeKind::Node(node));
        self
    }
}

#[derive(Debug)]
pub enum CodeKind {
    Node(NodeKind),
    SyntaxToken(SyntaxToken),
}

#[derive(Debug)]
pub struct Program {
    pub body: Vec<TopLevelKind>,
    pub declarations: Rc<RefCell<Scope>>,
    pub main_scope: Rc<RefCell<Scope>>,
}

impl Program {
    pub fn new(body: Vec<TopLevelKind>) -> Self {
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
    pub name: Option<Rc<Identifier>>,
    pub fields: Vec<Rc<TypeField>>,
}

impl StructDefinition {
    pub fn new(name: Option<Rc<Identifier>>, fields: Vec<Rc<TypeField>>) -> Self {
        Self { name, fields }
    }

    pub fn name(&self) -> Option<&Identifier> {
        self.name.as_deref()
    }
}

#[derive(Debug)]
pub struct TypeField {
    pub name: Option<Rc<Identifier>>,
    pub type_annotation: Option<Rc<TypeAnnotation>>,
}

impl TypeField {
    pub fn new(name: Option<Rc<Identifier>>, type_annotation: Option<Rc<TypeAnnotation>>) -> Self {
        Self {
            name,
            type_annotation,
        }
    }
}

#[derive(Debug)]
pub struct TypeAnnotation {
    pub name: Rc<Identifier>,
    pub r#type: Option<Rc<RefCell<sem::Type>>>,
}

impl TypeAnnotation {
    pub fn new(name: Rc<Identifier>) -> Self {
        Self { name, r#type: None }
    }
}

#[derive(Debug)]
pub struct FunctionDefinition {
    pub name: Option<Rc<Identifier>>,
    pub parameters: Vec<Rc<FunctionParameter>>,
    pub body: Rc<Block>,
}

impl FunctionDefinition {
    pub fn new(
        name: Option<Rc<Identifier>>,
        parameters: Vec<Rc<FunctionParameter>>,
        body: Rc<Block>,
    ) -> Self {
        Self {
            name,
            parameters,
            body,
        }
    }

    pub fn name(&self) -> Option<&Identifier> {
        self.name.as_deref()
    }

    pub fn body(&self) -> &Block {
        self.body.as_ref()
    }

    pub fn parameters(&self) -> slice::Iter<Rc<FunctionParameter>> {
        self.parameters.iter()
    }
}

#[derive(Debug)]
pub struct FunctionParameter {
    pub name: Rc<Identifier>,
}

impl FunctionParameter {
    pub fn new(name: Rc<Identifier>) -> Self {
        Self { name }
    }

    pub fn name(&self) -> &Identifier {
        self.name.as_ref()
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

    pub fn expression(&self) -> &Expression {
        self.expression.as_ref()
    }
}

#[derive(Debug)]
pub struct Block {
    pub statements: Vec<Rc<Statement>>,
    pub scope: Rc<RefCell<Scope>>,
}

impl Block {
    pub fn new(statements: Vec<Rc<Statement>>) -> Self {
        Self {
            statements,
            scope: wrap(Scope::new()),
        }
    }

    pub fn statements(&self) -> slice::Iter<Rc<Statement>> {
        self.statements.iter()
    }
}

#[derive(Debug)]
pub struct Expression {
    kind: ExpressionKind,
    code: Code,
    r#type: Rc<RefCell<sem::Type>>,
}

impl Expression {
    pub fn new(kind: ExpressionKind, code: Code, r#type: Rc<RefCell<sem::Type>>) -> Self {
        Self { kind, code, r#type }
    }

    pub fn kind(&self) -> &ExpressionKind {
        &self.kind
    }

    pub fn r#type(&self) -> &Rc<RefCell<sem::Type>> {
        &self.r#type
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

    pub fn array_expression(&self) -> Option<&ArrayExpression> {
        if let ExpressionKind::ArrayExpression(ref expr) = self.kind {
            Some(expr)
        } else {
            None
        }
    }

    pub fn call_expression(&self) -> Option<&CallExpression> {
        if let ExpressionKind::CallExpression(ref expr) = self.kind {
            Some(expr)
        } else {
            None
        }
    }

    pub fn if_expression(&self) -> Option<&IfExpression> {
        if let ExpressionKind::IfExpression(ref expr) = self.kind {
            Some(expr)
        } else {
            None
        }
    }

    pub fn case_expression(&self) -> Option<&CaseExpression> {
        if let ExpressionKind::CaseExpression(ref expr) = self.kind {
            Some(expr)
        } else {
            None
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct IntegerLiteral(i32);

impl IntegerLiteral {
    pub fn new(value: i32) -> Self {
        Self(value)
    }

    pub fn value(&self) -> i32 {
        self.0
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct StringLiteral(Option<String>);

impl StringLiteral {
    pub fn new(value: Option<String>) -> Self {
        Self(value)
    }

    pub fn value(&self) -> Option<&str> {
        self.0.as_deref()
    }
}

#[derive(Debug)]
pub struct BinaryExpression {
    pub operator: BinaryOperator,
    pub lhs: Rc<Expression>,
    pub rhs: Option<Rc<Expression>>,
}

impl BinaryExpression {
    pub fn new(operator: BinaryOperator, lhs: Rc<Expression>, rhs: Option<Rc<Expression>>) -> Self {
        Self { operator, lhs, rhs }
    }

    pub fn lhs(&self) -> &Expression {
        self.lhs.as_ref()
    }

    pub fn rhs(&self) -> Option<&Expression> {
        self.rhs.as_deref()
    }
}

#[derive(Debug)]
pub struct UnaryExpression {
    pub operator: UnaryOperator,
    pub operand: Option<Rc<Expression>>,
}

impl UnaryExpression {
    pub fn new(operator: UnaryOperator, operand: Option<Rc<Expression>>) -> Self {
        Self { operator, operand }
    }

    pub fn operand(&self) -> Option<&Expression> {
        self.operand.as_deref()
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
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

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum UnaryOperator {
    Minus,
    Plus,
}

#[derive(Debug)]
pub struct SubscriptExpression {
    pub callee: Rc<Expression>,
    pub arguments: Vec<Rc<Expression>>,
}

impl SubscriptExpression {
    pub fn new(callee: Rc<Expression>, arguments: Vec<Rc<Expression>>) -> Self {
        Self { callee, arguments }
    }

    pub fn callee(&self) -> &Expression {
        self.callee.as_ref()
    }

    pub fn arguments(&self) -> slice::Iter<Rc<Expression>> {
        self.arguments.iter()
    }
}

#[derive(Debug)]
pub struct CallExpression {
    pub callee: Rc<Expression>,
    pub arguments: Vec<Rc<Expression>>,
}

impl CallExpression {
    pub fn new(callee: Rc<Expression>, arguments: Vec<Rc<Expression>>) -> Self {
        Self { callee, arguments }
    }

    pub fn callee(&self) -> &Expression {
        self.callee.as_ref()
    }

    pub fn arguments(&self) -> slice::Iter<Rc<Expression>> {
        self.arguments.iter()
    }
}

#[derive(Debug)]
pub struct ArrayExpression {
    pub elements: Vec<Rc<Expression>>,
}

impl ArrayExpression {
    pub fn new(elements: Vec<Rc<Expression>>) -> Self {
        Self { elements }
    }

    pub fn elements(&self) -> slice::Iter<Rc<Expression>> {
        self.elements.iter()
    }
}

#[derive(Debug)]
pub struct IfExpression {
    pub condition: Option<Rc<Expression>>,
    pub then_body: Rc<Block>,
    pub else_body: Option<Rc<Block>>,
}

impl IfExpression {
    pub fn new(
        condition: Option<Rc<Expression>>,
        then_body: Rc<Block>,
        else_body: Option<Rc<Block>>,
    ) -> Self {
        Self {
            condition,
            then_body,
            else_body,
        }
    }
}

#[derive(Debug)]
pub struct CaseExpression {
    pub head: Option<Rc<Expression>>,
    pub arms: Vec<CaseArm>,
    pub else_body: Option<Rc<Block>>,
}

impl CaseExpression {
    pub fn new(
        head: Option<Rc<Expression>>,
        arms: Vec<CaseArm>,
        else_body: Option<Rc<Block>>,
    ) -> Self {
        Self {
            head,
            arms,
            else_body,
        }
    }
}

#[derive(Debug)]
pub struct CaseArm {
    pub pattern: Option<Rc<Pattern>>,
    pub guard: Option<Rc<Expression>>,
    pub then_body: Rc<Block>,
}

impl CaseArm {
    pub fn new(
        pattern: Option<Rc<Pattern>>,
        guard: Option<Rc<Expression>>,
        then_body: Rc<Block>,
    ) -> Self {
        Self {
            pattern,
            guard,
            then_body,
        }
    }

    pub fn pattern(&self) -> Option<&Pattern> {
        self.pattern.as_deref()
    }
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
    ArrayExpression(ArrayExpression),
    IfExpression(IfExpression),
    CaseExpression(CaseExpression),
    Expression(Rc<Expression>),
}

#[derive(Debug)]
pub struct Pattern {
    pub kind: PatternKind,
}

impl Pattern {
    pub fn new(kind: PatternKind) -> Self {
        Self { kind }
    }
}

#[derive(Debug)]
pub struct ArrayPattern {
    pub elements: Vec<Rc<Pattern>>,
}

impl ArrayPattern {
    pub fn new(elements: Vec<Rc<Pattern>>) -> Self {
        Self { elements }
    }

    pub fn elements(&self) -> slice::Iter<Rc<Pattern>> {
        self.elements.iter()
    }
}

#[derive(Debug)]
pub enum PatternKind {
    IntegerPattern(IntegerLiteral),
    StringPattern(StringLiteral),
    VariablePattern(Identifier),
    ArrayPattern(ArrayPattern),
}

// -- Iterators
#[derive(Debug, Clone)]
pub struct CodeKinds<'a> {
    iter: slice::Iter<'a, CodeKind>,
    len: usize,
}

impl<'a> CodeKinds<'a> {
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<'a> Iterator for CodeKinds<'a> {
    type Item = &'a CodeKind;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
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
            NodeKind::Pattern(_) => write!(f, "Pattern"),
            NodeKind::Expression(expr) => {
                write!(f, "{}", expr.kind)
            }
            NodeKind::Unit => write!(f, "()"),
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
            ExpressionKind::ArrayExpression(_) => write!(f, "ArrayExpression"),
            ExpressionKind::IfExpression(_) => write!(f, "IfExpression"),
            ExpressionKind::CaseExpression(_) => write!(f, "CaseExpression"),
            ExpressionKind::Expression(expr) => write!(f, "({})", expr.kind()),
        }
    }
}
