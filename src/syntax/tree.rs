use super::{EffectiveRange, MissingTokenKind, Position, Scope, SyntaxToken, Token};
use crate::{sem, util::wrap};
use std::rc::Rc;
use std::slice;
use std::{cell::RefCell, fmt};

pub trait Node: fmt::Display {
    fn code(&self) -> slice::Iter<CodeKind>;

    /// Returns the effective range of this node.
    fn range(&self) -> EffectiveRange {
        let mut it = self.code();

        // node must be at least one token.
        let init = it.next().unwrap();
        it.fold(init.range(), |acc, kind| kind.range().union(&acc))
    }

    fn find_identifier_at(&self, position: Position) -> Option<&Identifier> {
        for code in self.code() {
            if let CodeKind::Node(node) = code {
                match node {
                    NodeKind::Identifier(id) => {
                        if id.range().contains(position) {
                            return Some(id);
                        }
                    }
                    _ => {
                        if let Some(id) = node.find_identifier_at(position) {
                            return Some(id);
                        }
                    }
                }
            }
        }

        None
    }
}

#[derive(Debug, Clone)]
pub enum NodeKind {
    Program(Rc<Program>),
    Block(Rc<Block>),
    Identifier(Rc<Identifier>),
    StructDefinition(Rc<StructDefinition>),
    FunctionDefinition(Rc<FunctionDefinition>),
    FunctionParameter(Rc<FunctionParameter>),
    TypeField(Rc<TypeField>),
    TypeAnnotation(Rc<TypeAnnotation>),
    StructField(Rc<StructField>),
    StructFieldPattern(Rc<StructFieldPattern>),
    Statement(Rc<Statement>),
    VariableDeclaration(Rc<VariableDeclaration>),
    Expression(Rc<Expression>),
    CaseArm(Rc<CaseArm>),
    Pattern(Rc<Pattern>),
}

impl NodeKind {
    pub fn program(&self) -> Option<Rc<Program>> {
        if let NodeKind::Program(program) = self {
            Some(Rc::clone(program))
        } else {
            None
        }
    }

    pub fn struct_definition(&self) -> Option<Rc<StructDefinition>> {
        if let NodeKind::StructDefinition(node) = self {
            Some(Rc::clone(node))
        } else {
            None
        }
    }

    pub fn function_definition(&self) -> Option<Rc<FunctionDefinition>> {
        if let NodeKind::FunctionDefinition(node) = self {
            Some(Rc::clone(node))
        } else {
            None
        }
    }

    pub fn function_parameter(&self) -> Option<Rc<FunctionParameter>> {
        if let NodeKind::FunctionParameter(node) = self {
            Some(Rc::clone(node))
        } else {
            None
        }
    }

    pub fn variable_declaration(&self) -> Option<Rc<VariableDeclaration>> {
        if let NodeKind::VariableDeclaration(node) = self {
            Some(Rc::clone(node))
        } else {
            None
        }
    }

    pub fn block(&self) -> Option<Rc<Block>> {
        if let NodeKind::Block(block) = self {
            Some(Rc::clone(block))
        } else {
            None
        }
    }

    pub fn identifier(&self) -> Option<Rc<Identifier>> {
        if let NodeKind::Identifier(node) = self {
            Some(Rc::clone(node))
        } else {
            None
        }
    }

    pub fn type_field(&self) -> Option<Rc<TypeField>> {
        if let NodeKind::TypeField(node) = self {
            Some(Rc::clone(node))
        } else {
            None
        }
    }

    pub fn type_annotation(&self) -> Option<Rc<TypeAnnotation>> {
        if let NodeKind::TypeAnnotation(node) = self {
            Some(Rc::clone(node))
        } else {
            None
        }
    }

    pub fn case_arm(&self) -> Option<Rc<CaseArm>> {
        if let NodeKind::CaseArm(node) = self {
            Some(Rc::clone(node))
        } else {
            None
        }
    }

    pub fn pattern(&self) -> Option<Rc<Pattern>> {
        if let NodeKind::Pattern(node) = self {
            Some(Rc::clone(node))
        } else {
            None
        }
    }

    pub fn struct_field(&self) -> Option<Rc<StructField>> {
        if let NodeKind::StructField(node) = self {
            Some(Rc::clone(node))
        } else {
            None
        }
    }

    pub fn struct_field_pattern(&self) -> Option<Rc<StructFieldPattern>> {
        if let NodeKind::StructFieldPattern(node) = self {
            Some(Rc::clone(node))
        } else {
            None
        }
    }

    pub fn statement(&self) -> Option<Rc<Statement>> {
        if let NodeKind::Statement(stmt) = self {
            Some(Rc::clone(stmt))
        } else {
            None
        }
    }

    pub fn expression(&self) -> Option<Rc<Expression>> {
        if let NodeKind::Expression(node) = self {
            Some(Rc::clone(node))
        } else {
            None
        }
    }

    pub fn struct_literal(&self) -> Option<&StructLiteral> {
        if let NodeKind::Expression(node) = self {
            return node.struct_literal();
        }
        None
    }

    pub fn variable_expression(&self) -> Option<&Identifier> {
        if let NodeKind::Expression(node) = self {
            return node.variable_expression();
        }
        None
    }

    pub fn member_expression(&self) -> Option<&MemberExpression> {
        if let NodeKind::Expression(node) = self {
            return node.member_expression();
        }
        None
    }

    pub fn is_block(&self) -> bool {
        matches!(self, NodeKind::Block(..))
    }

    pub fn is_statement(&self) -> bool {
        matches!(self, NodeKind::Statement(..))
    }

    pub fn is_struct_definition(&self) -> bool {
        matches!(self, NodeKind::StructDefinition(..))
    }

    pub fn is_struct_field(&self) -> bool {
        matches!(self, NodeKind::StructField(..))
    }

    pub fn is_function_definition(&self) -> bool {
        matches!(self, NodeKind::FunctionDefinition(..))
    }

    pub fn is_function_parameter(&self) -> bool {
        matches!(self, NodeKind::FunctionParameter(..))
    }

    pub fn is_expression(&self) -> bool {
        matches!(self, NodeKind::Expression(..))
    }

    pub fn is_struct_literal(&self) -> bool {
        self.struct_literal().is_some()
    }

    pub fn is_variable_expression(&self) -> bool {
        self.variable_expression().is_some()
    }

    pub fn is_member_expression(&self) -> bool {
        self.member_expression().is_some()
    }
}

impl Node for NodeKind {
    fn code(&self) -> slice::Iter<CodeKind> {
        match self {
            NodeKind::Program(kind) => kind.code(),
            NodeKind::Block(kind) => kind.code(),
            NodeKind::Identifier(kind) => kind.code(),
            NodeKind::StructDefinition(kind) => kind.code(),
            NodeKind::FunctionDefinition(kind) => kind.code(),
            NodeKind::TypeField(kind) => kind.code(),
            NodeKind::StructField(kind) => kind.code(),
            NodeKind::StructFieldPattern(kind) => kind.code(),
            NodeKind::TypeAnnotation(kind) => kind.code(),
            NodeKind::FunctionParameter(kind) => kind.code(),
            NodeKind::Statement(kind) => kind.code(),
            NodeKind::VariableDeclaration(kind) => kind.code(),
            NodeKind::Expression(kind) => kind.code(),
            NodeKind::CaseArm(kind) => kind.code(),
            NodeKind::Pattern(kind) => kind.code(),
        }
    }
}

#[derive(Debug)]
pub enum TopLevelKind {
    StructDefinition(Rc<StructDefinition>),
    FunctionDefinition(Rc<FunctionDefinition>),
    Statement(Rc<Statement>),
    VariableDeclaration(Rc<VariableDeclaration>),
}

impl TopLevelKind {
    pub fn statement(&self) -> Option<Rc<Statement>> {
        if let TopLevelKind::Statement(stmt) = self {
            Some(Rc::clone(stmt))
        } else {
            None
        }
    }
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

    pub fn iter(&self) -> slice::Iter<CodeKind> {
        self.code.iter()
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

impl CodeKind {
    pub fn range(&self) -> EffectiveRange {
        match self {
            CodeKind::Node(kind) => kind.range(),
            CodeKind::SyntaxToken(token) => token.range(),
        }
    }
}

#[derive(Debug)]
pub struct Program {
    pub body: Vec<TopLevelKind>,
    declarations: Rc<RefCell<Scope>>,
    main_scope: Rc<RefCell<Scope>>,
    code: Code,
}

impl Program {
    pub fn new(body: Vec<TopLevelKind>, code: Code) -> Self {
        let declarations = wrap(Scope::prelude());
        let main_scope = wrap(Scope::new());

        Self {
            body,
            declarations,
            main_scope,
            code,
        }
    }

    pub fn declarations_scope(&self) -> &Rc<RefCell<Scope>> {
        &self.declarations
    }

    pub fn main_scope(&self) -> &Rc<RefCell<Scope>> {
        &self.main_scope
    }
}

impl Node for Program {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.iter()
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Program")
    }
}

#[derive(Debug)]
pub struct Identifier {
    pub id: String,
    code: Code,
}

impl Identifier {
    pub fn new<S: Into<String>>(name: S, code: Code) -> Self {
        Self {
            id: name.into(),
            code,
        }
    }

    pub fn as_str(&self) -> &str {
        &self.id
    }
}

impl Node for Identifier {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.iter()
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.id.fmt(f)
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
    code: Code,
}

impl StructDefinition {
    pub fn new(name: Option<Rc<Identifier>>, fields: Vec<Rc<TypeField>>, code: Code) -> Self {
        Self { name, fields, code }
    }

    pub fn name(&self) -> Option<&Identifier> {
        self.name.as_deref()
    }
}

impl Node for StructDefinition {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.iter()
    }
}

impl fmt::Display for StructDefinition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(name) = self.name() {
            write!(f, "StructDefinition({})", name.to_string())
        } else {
            write!(f, "StructDefinition")
        }
    }
}

#[derive(Debug)]
pub struct TypeField {
    pub name: Option<Rc<Identifier>>,
    pub type_annotation: Option<Rc<TypeAnnotation>>,
    code: Code,
}

impl TypeField {
    pub fn new(
        name: Option<Rc<Identifier>>,
        type_annotation: Option<Rc<TypeAnnotation>>,
        code: Code,
    ) -> Self {
        Self {
            name,
            type_annotation,
            code,
        }
    }

    pub fn name(&self) -> Option<&Identifier> {
        self.name.as_deref()
    }
}

impl Node for TypeField {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.iter()
    }
}

impl fmt::Display for TypeField {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(name) = self.name() {
            write!(f, "TypeField({})", name.to_string())
        } else {
            write!(f, "TypeField")
        }
    }
}

#[derive(Debug)]
pub struct TypeAnnotation {
    pub r#type: Rc<RefCell<sem::Type>>,
    code: Code,
}

impl TypeAnnotation {
    pub fn new(r#type: Rc<RefCell<sem::Type>>, code: Code) -> Self {
        Self { r#type, code }
    }
}

impl Node for TypeAnnotation {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.iter()
    }
}

impl fmt::Display for TypeAnnotation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TypeAnnotation({:?})", self.r#type)
    }
}

#[derive(Debug)]
pub struct FunctionDefinition {
    pub name: Option<Rc<Identifier>>,
    pub parameters: Vec<Rc<FunctionParameter>>,
    pub body: Rc<Block>,
    code: Code,
}

impl FunctionDefinition {
    pub fn new(
        name: Option<Rc<Identifier>>,
        parameters: Vec<Rc<FunctionParameter>>,
        body: Rc<Block>,
        code: Code,
    ) -> Self {
        Self {
            name,
            parameters,
            body,
            code,
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

impl Node for FunctionDefinition {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.iter()
    }
}

impl fmt::Display for FunctionDefinition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(name) = self.name() {
            write!(f, "FunctionDefinition({})", name.to_string())
        } else {
            write!(f, "FunctionDefinition")
        }
    }
}

#[derive(Debug)]
pub struct FunctionParameter {
    pub name: Rc<Identifier>,
    code: Code,
}

impl FunctionParameter {
    pub fn new(name: Rc<Identifier>, code: Code) -> Self {
        Self { name, code }
    }

    pub fn name(&self) -> &Identifier {
        self.name.as_ref()
    }
}

impl Node for FunctionParameter {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.iter()
    }
}

impl fmt::Display for FunctionParameter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FunctionParameter({})", self.name().to_string())
    }
}

#[derive(Debug)]
pub struct VariableDeclaration {
    pub pattern: Option<Rc<Pattern>>,
    pub init: Option<Rc<Expression>>,
    code: Code,
}

impl VariableDeclaration {
    pub fn new(pattern: Option<Rc<Pattern>>, init: Option<Rc<Expression>>, code: Code) -> Self {
        Self {
            pattern,
            init,
            code,
        }
    }
}

impl Node for VariableDeclaration {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.iter()
    }
}

impl fmt::Display for VariableDeclaration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "VariableDeclaration")
    }
}

#[derive(Debug)]
pub struct Statement {
    pub kind: StatementKind,
    code: Code,
}

#[derive(Debug)]
pub enum StatementKind {
    Expression(Rc<Expression>),
    VariableDeclaration(Rc<VariableDeclaration>),
}

impl Statement {
    pub fn new(kind: StatementKind, code: Code) -> Self {
        Self { kind, code }
    }

    pub fn expression(&self) -> Option<&Expression> {
        if let StatementKind::Expression(ref expr) = self.kind {
            Some(expr.as_ref())
        } else {
            None
        }
    }

    pub fn variable_declaration(&self) -> Option<&VariableDeclaration> {
        if let StatementKind::VariableDeclaration(ref decl) = self.kind {
            Some(decl.as_ref())
        } else {
            None
        }
    }
}

impl Node for Statement {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.iter()
    }
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Statement")
    }
}

#[derive(Debug)]
pub struct Block {
    statements: Vec<Rc<Statement>>,
    scope: Rc<RefCell<Scope>>,
    code: Code,
}

impl Block {
    pub fn new(statements: Vec<Rc<Statement>>, code: Code) -> Self {
        Self {
            statements,
            scope: wrap(Scope::new()),
            code,
        }
    }

    pub fn scope(&self) -> &Rc<RefCell<Scope>> {
        &self.scope
    }

    pub fn statements(&self) -> slice::Iter<Rc<Statement>> {
        self.statements.iter()
    }
}

impl Node for Block {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.iter()
    }
}

impl fmt::Display for Block {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Block")
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

    pub fn struct_literal(&self) -> Option<&StructLiteral> {
        if let ExpressionKind::StructLiteral(ref expr) = self.kind {
            Some(expr)
        } else {
            None
        }
    }

    pub fn variable_expression(&self) -> Option<&Identifier> {
        if let ExpressionKind::VariableExpression(ref id) = self.kind {
            Some(id)
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

    pub fn member_expression(&self) -> Option<&MemberExpression> {
        if let ExpressionKind::MemberExpression(ref expr) = self.kind {
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

    pub fn is_struct_literal(&self) -> bool {
        matches!(self.kind, ExpressionKind::StructLiteral(..))
    }

    pub fn is_member_expression(&self) -> bool {
        matches!(self.kind, ExpressionKind::MemberExpression(..))
    }

    pub fn is_variable_expression(&self) -> bool {
        matches!(self.kind, ExpressionKind::VariableExpression(..))
    }
}

impl Node for Expression {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.iter()
    }
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

#[derive(Debug)]
pub struct StructLiteral {
    pub name: Rc<Identifier>,
    pub fields: Vec<Rc<StructField>>,
}

impl StructLiteral {
    pub fn new(name: Rc<Identifier>, fields: Vec<Rc<StructField>>) -> Self {
        Self { name, fields }
    }

    pub fn name(&self) -> &Identifier {
        self.name.as_ref()
    }
}

#[derive(Debug)]
pub struct StructField {
    pub name: Rc<Identifier>,
    pub value: Option<Rc<Expression>>,
    pub code: Code,
}

impl StructField {
    pub fn new(name: Rc<Identifier>, value: Option<Rc<Expression>>, code: Code) -> Self {
        Self { name, value, code }
    }

    pub fn name(&self) -> &Identifier {
        self.name.as_ref()
    }
}

impl Node for StructField {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.iter()
    }
}

impl fmt::Display for StructField {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "StructField({})", self.name().to_string())
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
pub struct MemberExpression {
    pub object: Rc<Expression>,
    pub field: Option<Rc<Identifier>>,
}

impl MemberExpression {
    pub fn new(object: Rc<Expression>, field: Option<Rc<Identifier>>) -> Self {
        Self { object, field }
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
    pub arms: Vec<Rc<CaseArm>>,
    pub else_body: Option<Rc<Block>>,
}

impl CaseExpression {
    pub fn new(
        head: Option<Rc<Expression>>,
        arms: Vec<Rc<CaseArm>>,
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

    // `CaseArm` is the only syntactic element other than Program and Block that introduces
    // a new scope. This scope is necessary to use the variables introduced in each arm in
    // the guard clause.
    scope: Rc<RefCell<Scope>>,
    code: Code,
}

impl CaseArm {
    pub fn new(
        pattern: Option<Rc<Pattern>>,
        guard: Option<Rc<Expression>>,
        then_body: Rc<Block>,
        code: Code,
    ) -> Self {
        Self {
            pattern,
            guard,
            then_body,
            scope: wrap(Scope::new()),
            code,
        }
    }

    pub fn scope(&self) -> &Rc<RefCell<Scope>> {
        &self.scope
    }

    pub fn pattern(&self) -> Option<&Pattern> {
        self.pattern.as_deref()
    }
}

impl Node for CaseArm {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.iter()
    }
}

impl fmt::Display for CaseArm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CaseArm")
    }
}

#[derive(Debug)]
pub enum ExpressionKind {
    IntegerLiteral(i32),
    StringLiteral(Option<String>),
    StructLiteral(StructLiteral),
    VariableExpression(Rc<Identifier>),
    BinaryExpression(BinaryExpression),
    UnaryExpression(UnaryExpression),
    SubscriptExpression(SubscriptExpression),
    CallExpression(CallExpression),
    ArrayExpression(ArrayExpression),
    MemberExpression(MemberExpression),
    IfExpression(IfExpression),
    CaseExpression(CaseExpression),
    Expression(Option<Rc<Expression>>),
}

#[derive(Debug)]
pub struct Pattern {
    pub kind: PatternKind,
    pub code: Code,
}

impl Pattern {
    pub fn new(kind: PatternKind, code: Code) -> Self {
        Self { kind, code }
    }
}

impl Node for Pattern {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.iter()
    }
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Pattern")
    }
}

#[derive(Debug)]
pub struct ArrayPattern {
    elements: Vec<Rc<Pattern>>,
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
pub struct RestPattern {
    pub id: Option<Rc<Identifier>>,
}

impl RestPattern {
    pub fn new(id: Option<Rc<Identifier>>) -> Self {
        Self { id }
    }
}

#[derive(Debug)]
pub struct StructPattern {
    pub name: Rc<Identifier>,
    fields: Vec<Rc<StructFieldPattern>>,
}

impl StructPattern {
    pub fn new(name: Rc<Identifier>, fields: Vec<Rc<StructFieldPattern>>) -> Self {
        Self { name, fields }
    }

    pub fn fields(&self) -> slice::Iter<Rc<StructFieldPattern>> {
        self.fields.iter()
    }
}

#[derive(Debug)]
pub struct StructFieldPattern {
    pub name: Rc<Identifier>,
    pub value: Option<Rc<Pattern>>,
    pub code: Code,
}

impl StructFieldPattern {
    pub fn new(name: Rc<Identifier>, value: Option<Rc<Pattern>>, code: Code) -> Self {
        Self { name, value, code }
    }
}

impl Node for StructFieldPattern {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.iter()
    }
}

impl fmt::Display for StructFieldPattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "StructFieldPattern")
    }
}

#[derive(Debug)]
pub enum PatternKind {
    IntegerPattern(i32),
    StringPattern(Option<String>),
    VariablePattern(Rc<Identifier>),
    ArrayPattern(ArrayPattern),
    RestPattern(RestPattern),
    StructPattern(StructPattern),
}

impl fmt::Display for NodeKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NodeKind::Program(program) => program.fmt(f),
            NodeKind::Block(block) => block.fmt(f),
            NodeKind::Identifier(id) => write!(f, "Identifier({})", id),
            NodeKind::StructDefinition(definition) => definition.fmt(f),
            NodeKind::FunctionDefinition(definition) => definition.fmt(f),
            NodeKind::TypeField(field) => field.fmt(f),
            NodeKind::TypeAnnotation(ty) => ty.fmt(f),
            NodeKind::StructField(field) => field.fmt(f),
            NodeKind::StructFieldPattern(pattern) => pattern.fmt(f),
            NodeKind::FunctionParameter(param) => param.fmt(f),
            NodeKind::Statement(stmt) => stmt.fmt(f),
            NodeKind::VariableDeclaration(declaration) => declaration.fmt(f),
            NodeKind::Pattern(pattern) => pattern.fmt(f),
            NodeKind::CaseArm(arm) => arm.fmt(f),
            NodeKind::Expression(expr) => expr.fmt(f),
        }
    }
}

impl fmt::Display for ExpressionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExpressionKind::IntegerLiteral(i) => write!(f, "IntegerLiteral({})", i),
            ExpressionKind::StringLiteral(_) => write!(f, "StringLiteral"),
            ExpressionKind::VariableExpression(_) => write!(f, "VariableExpression"),
            ExpressionKind::BinaryExpression(_) => write!(f, "BinaryExpression"),
            ExpressionKind::UnaryExpression(_) => write!(f, "UnaryExpression"),
            ExpressionKind::SubscriptExpression(_) => write!(f, "SubscriptExpression"),
            ExpressionKind::CallExpression(_) => write!(f, "CallExpression"),
            ExpressionKind::ArrayExpression(_) => write!(f, "ArrayExpression"),
            ExpressionKind::IfExpression(_) => write!(f, "IfExpression"),
            ExpressionKind::CaseExpression(_) => write!(f, "CaseExpression"),
            ExpressionKind::MemberExpression(_) => write!(f, "MemberExpression"),
            ExpressionKind::StructLiteral(_) => write!(f, "StructLiteral"),
            ExpressionKind::Expression(Some(expr)) => write!(f, "({})", expr.kind()),
            ExpressionKind::Expression(None) => write!(f, "()"),
        }
    }
}
