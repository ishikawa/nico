use super::{EffectiveRange, MissingTokenKind, Scope, SyntaxToken, Token};
use crate::{sem, util::wrap};
use bumpalo::{self, collections};
use std::rc::Rc;
use std::slice;
use std::{cell::RefCell, fmt};

#[derive(Debug, Default)]
pub struct Ast {
    arena: bumpalo::Bump,
}

impl Ast {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn arena(&self) -> &bumpalo::Bump {
        &self.arena
    }

    pub fn alloc<T>(&self, val: T) -> &mut T {
        self.arena.alloc(val)
    }
}

pub trait Node<'a>: fmt::Display {
    fn code(&self) -> slice::Iter<'_, CodeKind<'a>>;

    /// Returns the effective range of this node.
    fn range(&self) -> EffectiveRange {
        let mut it = self.code();

        // node must be at least one token.
        let init = it.next().unwrap();
        it.fold(init.range(), |acc, kind| kind.range().union(&acc))
    }
}

#[derive(Debug, Clone)]
pub enum NodeKind<'a> {
    Program(&'a Program<'a>),
    Block(&'a Block<'a>),
    Identifier(&'a Identifier<'a>),
    StructDefinition(&'a StructDefinition<'a>),
    FunctionDefinition(&'a FunctionDefinition<'a>),
    FunctionParameter(&'a FunctionParameter<'a>),
    TypeField(&'a TypeField<'a>),
    TypeAnnotation(&'a TypeAnnotation<'a>),
    ValueField(&'a ValueField<'a>),
    ValueFieldPattern(&'a ValueFieldPattern<'a>),
    Statement(&'a Statement<'a>),
    VariableDeclaration(&'a VariableDeclaration<'a>),
    Expression(&'a Expression<'a>),
    CaseArm(&'a CaseArm<'a>),
    Pattern(&'a Pattern<'a>),
}

impl<'a> NodeKind<'a> {
    pub fn program(&self) -> Option<&Program<'a>> {
        if let NodeKind::Program(program) = self {
            Some(program)
        } else {
            None
        }
    }

    pub fn struct_definition(&self) -> Option<&'a StructDefinition<'a>> {
        if let NodeKind::StructDefinition(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn function_definition(&self) -> Option<&'a FunctionDefinition<'a>> {
        if let NodeKind::FunctionDefinition(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn function_parameter(&self) -> Option<&'a FunctionParameter<'a>> {
        if let NodeKind::FunctionParameter(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn variable_declaration(&self) -> Option<&'a VariableDeclaration<'a>> {
        if let NodeKind::VariableDeclaration(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn block(&self) -> Option<&'a Block<'a>> {
        if let NodeKind::Block(block) = self {
            Some(block)
        } else {
            None
        }
    }

    pub fn identifier(&self) -> Option<&'a Identifier<'a>> {
        if let NodeKind::Identifier(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn type_field(&self) -> Option<&'a TypeField<'a>> {
        if let NodeKind::TypeField(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn type_annotation(&self) -> Option<&'a TypeAnnotation<'a>> {
        if let NodeKind::TypeAnnotation(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn case_arm(&self) -> Option<&'a CaseArm<'a>> {
        if let NodeKind::CaseArm(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn pattern(&self) -> Option<&'a Pattern<'a>> {
        if let NodeKind::Pattern(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn struct_field(&self) -> Option<&'a ValueField<'a>> {
        if let NodeKind::ValueField(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn struct_field_pattern(&self) -> Option<&'a ValueFieldPattern<'a>> {
        if let NodeKind::ValueFieldPattern(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn statement(&self) -> Option<&'a Statement<'a>> {
        if let NodeKind::Statement(stmt) = self {
            Some(stmt)
        } else {
            None
        }
    }

    pub fn expression(&self) -> Option<&'a Expression<'a>> {
        if let NodeKind::Expression(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn struct_literal(&self) -> Option<&'a StructLiteral<'a>> {
        if let NodeKind::Expression(node) = self {
            return node.struct_literal();
        }
        None
    }

    pub fn variable_expression(&self) -> Option<&'a Identifier<'a>> {
        if let NodeKind::Expression(node) = self {
            return node.variable_expression();
        }
        None
    }

    pub fn member_expression(&self) -> Option<&'a MemberExpression<'a>> {
        if let NodeKind::Expression(node) = self {
            return node.member_expression();
        }
        None
    }

    pub fn is_block(&self) -> bool {
        matches!(self, Self::Block(..))
    }

    pub fn is_statement(&self) -> bool {
        matches!(self, Self::Statement(..))
    }

    pub fn is_struct_definition(&self) -> bool {
        matches!(self, Self::StructDefinition(..))
    }

    pub fn is_struct_field(&self) -> bool {
        matches!(self, Self::ValueField(..))
    }

    pub fn is_function_definition(&self) -> bool {
        matches!(self, Self::FunctionDefinition(..))
    }

    pub fn is_function_parameter(&self) -> bool {
        matches!(self, Self::FunctionParameter(..))
    }

    pub fn is_expression(&self) -> bool {
        matches!(self, Self::Expression(..))
    }

    pub fn is_pattern(&self) -> bool {
        matches!(self, Self::Pattern(..))
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

impl<'a> Node<'a> for NodeKind<'a> {
    fn code(&self) -> slice::Iter<'_, CodeKind<'a>> {
        match self {
            NodeKind::Program(kind) => kind.code(),
            NodeKind::Block(kind) => kind.code(),
            NodeKind::Identifier(kind) => kind.code(),
            NodeKind::StructDefinition(kind) => kind.code(),
            NodeKind::FunctionDefinition(kind) => kind.code(),
            NodeKind::TypeField(kind) => kind.code(),
            NodeKind::ValueField(kind) => kind.code(),
            NodeKind::ValueFieldPattern(kind) => kind.code(),
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
pub enum TopLevelKind<'a> {
    StructDefinition(&'a StructDefinition<'a>),
    FunctionDefinition(&'a FunctionDefinition<'a>),
    Statement(&'a Statement<'a>),
    VariableDeclaration(&'a VariableDeclaration<'a>),
}

impl<'a> TopLevelKind<'a> {
    pub fn statement(&self) -> Option<&'a Statement<'a>> {
        if let TopLevelKind::Statement(stmt) = self {
            Some(stmt)
        } else {
            None
        }
    }
}

/// `Builtin` is where a binding to "built-in" primitives/functions are defined.
/// It's not a part of an AST, so it doesn't have tokens.
#[derive(Debug)]
pub struct Builtin {
    name: String,
    r#type: Rc<RefCell<sem::Type>>,
}

impl Builtin {
    pub fn new<S: Into<String>>(name: S, r#type: &Rc<RefCell<sem::Type>>) -> Self {
        Self {
            name: name.into(),
            r#type: Rc::clone(r#type),
        }
    }

    pub fn name(&self) -> &str {
        self.name.as_str()
    }

    pub fn r#type(&self) -> &Rc<RefCell<sem::Type>> {
        &self.r#type
    }
}

#[derive(Debug, Clone)]
pub enum DefinitionKind<'a> {
    // Builtin functions, variables
    Builtin(Rc<Builtin>),
    // Declaration nodes
    StructDefinition(&'a StructDefinition<'a>),
    FunctionDefinition(&'a FunctionDefinition<'a>),
    FunctionParameter(&'a FunctionParameter<'a>),
    Pattern(&'a Pattern<'a>),
}

impl<'a> DefinitionKind<'a> {
    pub fn builtin(&self) -> Option<Rc<Builtin>> {
        if let DefinitionKind::Builtin(builtin) = self {
            Some(Rc::clone(builtin))
        } else {
            None
        }
    }

    pub fn struct_definition(&self) -> Option<&'a StructDefinition<'a>> {
        if let DefinitionKind::StructDefinition(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn function_definition(&self) -> Option<&'a FunctionDefinition<'a>> {
        if let DefinitionKind::FunctionDefinition(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn function_parameter(&self) -> Option<&'a FunctionParameter<'a>> {
        if let DefinitionKind::FunctionParameter(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn pattern(&self) -> Option<&'a Pattern<'a>> {
        if let DefinitionKind::Pattern(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn is_builtin(&self) -> bool {
        matches!(self, Self::Builtin(..))
    }

    pub fn is_struct_definition(&self) -> bool {
        matches!(self, Self::StructDefinition(..))
    }

    pub fn is_function_definition(&self) -> bool {
        matches!(self, Self::FunctionDefinition(..))
    }

    pub fn is_function_parameter(&self) -> bool {
        matches!(self, Self::FunctionParameter(..))
    }

    pub fn is_pattern(&self) -> bool {
        matches!(self, Self::Pattern(..))
    }

    pub fn ptr_eq(&self, other: &DefinitionKind<'a>) -> bool {
        if let DefinitionKind::Builtin(ref definition1) = self {
            if let DefinitionKind::Builtin(ref definition2) = other {
                return std::ptr::eq(definition1.as_ref(), definition2.as_ref());
            }
        }

        if let DefinitionKind::StructDefinition(definition1) = self {
            if let DefinitionKind::StructDefinition(definition2) = other {
                return std::ptr::eq(definition1, definition2);
            }
        }

        if let DefinitionKind::FunctionDefinition(definition1) = self {
            if let DefinitionKind::FunctionDefinition(definition2) = other {
                return std::ptr::eq(definition1, definition2);
            }
        }

        if let DefinitionKind::FunctionParameter(definition1) = self {
            if let DefinitionKind::FunctionParameter(definition2) = other {
                return std::ptr::eq(definition1, definition2);
            }
        }

        if let DefinitionKind::Pattern(definition1) = self {
            if let DefinitionKind::Pattern(definition2) = other {
                return std::ptr::eq(definition1, definition2);
            }
        }

        false
    }
}

#[derive(Debug)]
pub struct Code<'a> {
    code: collections::Vec<'a, CodeKind<'a>>,
}

impl<'a> Code<'a> {
    pub fn new(tree: &'a Ast) -> Self {
        Self {
            code: collections::Vec::new_in(&tree.arena),
        }
    }

    pub fn with_interpreted(tree: &'a Ast, token: Token) -> Self {
        Self {
            code: bumpalo::vec![in tree.arena(); CodeKind::SyntaxToken(SyntaxToken::Interpreted(token))],
        }
    }

    pub fn with_node(tree: &'a Ast, node: NodeKind<'a>) -> Code<'a> {
        Code {
            code: bumpalo::vec![in tree.arena(); CodeKind::Node(node)],
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

    pub fn iter(&self) -> slice::Iter<'_, CodeKind<'a>> {
        self.code.iter()
    }

    // children
    pub fn node(&mut self, node: NodeKind<'a>) -> &mut Code<'a> {
        self.code.push(CodeKind::Node(node));
        self
    }
}

#[derive(Debug)]
pub enum CodeKind<'a> {
    Node(NodeKind<'a>),
    SyntaxToken(SyntaxToken),
}

impl CodeKind<'_> {
    pub fn range(&self) -> EffectiveRange {
        match self {
            CodeKind::Node(kind) => kind.range(),
            CodeKind::SyntaxToken(token) => token.range(),
        }
    }
}

#[derive(Debug)]
pub struct Program<'a> {
    pub body: Vec<TopLevelKind<'a>>,
    declarations: Rc<RefCell<Scope>>,
    main_scope: Rc<RefCell<Scope>>,
    code: Code<'a>,
}

impl<'a> Program<'a> {
    pub fn new(body: Vec<TopLevelKind<'a>>, code: Code<'a>) -> Program<'a> {
        let declarations = wrap(Scope::prelude());
        let main_scope = wrap(Scope::new());

        Program {
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

impl<'a> Node<'a> for Program<'a> {
    fn code(&self) -> slice::Iter<'_, CodeKind<'a>> {
        self.code.iter()
    }
}

impl fmt::Display for Program<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Program")
    }
}

#[derive(Debug)]
pub struct Identifier<'a> {
    pub id: String,
    code: Code<'a>,
}

impl<'a> Identifier<'a> {
    pub fn new<S: Into<String>>(name: S, code: Code<'a>) -> Self {
        Self {
            id: name.into(),
            code,
        }
    }

    pub fn as_str(&self) -> &str {
        &self.id
    }
}

impl<'a> Node<'a> for Identifier<'a> {
    fn code(&self) -> slice::Iter<'_, CodeKind<'a>> {
        self.code.iter()
    }
}

impl fmt::Display for Identifier<'_> {
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
pub struct StructDefinition<'a> {
    pub name: Option<&'a Identifier<'a>>,
    pub fields: Vec<&'a TypeField<'a>>,
    r#type: Rc<RefCell<sem::Type>>,
    code: Code<'a>,
}

impl<'a> StructDefinition<'a> {
    pub fn new(
        name: Option<&'a Identifier<'a>>,
        fields: Vec<&'a TypeField<'a>>,
        code: Code<'a>,
    ) -> Self {
        Self {
            name,
            fields,
            code,
            r#type: wrap(sem::Type::Unknown),
        }
    }

    pub fn name(&self) -> Option<&'a Identifier<'a>> {
        self.name
    }

    pub fn r#type(&self) -> &Rc<RefCell<sem::Type>> {
        &self.r#type
    }

    pub fn get_field_type(&self, name: &str) -> Option<Rc<RefCell<sem::Type>>> {
        self.fields
            .iter()
            .find(|f| {
                f.name()
                    .map_or(false, |field_name| field_name.as_str() == name)
            })
            .and_then(|f| f.type_annotation.clone())
            .map(|annotation| Rc::clone(&annotation.r#type))
    }
}

impl<'a> Node<'a> for StructDefinition<'a> {
    fn code(&self) -> slice::Iter<'_, CodeKind<'a>> {
        self.code.iter()
    }
}

impl fmt::Display for StructDefinition<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(name) = self.name() {
            write!(f, "StructDefinition({})", name.as_str())
        } else {
            write!(f, "StructDefinition")
        }
    }
}

#[derive(Debug)]
pub struct TypeField<'a> {
    pub name: Option<&'a Identifier<'a>>,
    pub type_annotation: Option<&'a TypeAnnotation<'a>>,
    code: Code<'a>,
}

impl<'a> TypeField<'a> {
    pub fn new(
        name: Option<&'a Identifier<'a>>,
        type_annotation: Option<&'a TypeAnnotation<'a>>,
        code: Code<'a>,
    ) -> Self {
        Self {
            name,
            type_annotation,
            code,
        }
    }

    pub fn name(&self) -> Option<&'a Identifier<'a>> {
        self.name
    }
}

impl<'a> Node<'a> for TypeField<'a> {
    fn code(&self) -> slice::Iter<'_, CodeKind<'a>> {
        self.code.iter()
    }
}

impl fmt::Display for TypeField<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(name) = self.name() {
            write!(f, "TypeField({})", name.as_str())
        } else {
            write!(f, "TypeField")
        }
    }
}

#[derive(Debug)]
pub struct TypeAnnotation<'a> {
    pub r#type: Rc<RefCell<sem::Type>>,
    code: Code<'a>,
}

impl<'a> TypeAnnotation<'a> {
    pub fn new(r#type: Rc<RefCell<sem::Type>>, code: Code<'a>) -> Self {
        Self { r#type, code }
    }
}

impl<'a> Node<'a> for TypeAnnotation<'a> {
    fn code(&self) -> slice::Iter<'_, CodeKind<'a>> {
        self.code.iter()
    }
}

impl fmt::Display for TypeAnnotation<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TypeAnnotation({:?})", self.r#type)
    }
}

#[derive(Debug)]
pub struct FunctionDefinition<'a> {
    pub name: Option<&'a Identifier<'a>>,
    pub parameters: Vec<&'a FunctionParameter<'a>>,
    pub body: &'a Block<'a>,
    code: Code<'a>,
}

impl<'a> FunctionDefinition<'a> {
    pub fn new(
        name: Option<&'a Identifier<'a>>,
        parameters: Vec<&'a FunctionParameter<'a>>,
        body: &'a Block<'a>,
        code: Code<'a>,
    ) -> Self {
        Self {
            name,
            parameters,
            body,
            code,
        }
    }

    pub fn name(&self) -> Option<&'a Identifier<'a>> {
        self.name
    }

    pub fn body(&self) -> &'a Block<'a> {
        self.body
    }

    pub fn parameters(&self) -> slice::Iter<'_, &FunctionParameter<'a>> {
        self.parameters.iter()
    }
}

impl<'a> Node<'a> for FunctionDefinition<'a> {
    fn code(&self) -> slice::Iter<'_, CodeKind<'a>> {
        self.code.iter()
    }
}

impl fmt::Display for FunctionDefinition<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(name) = self.name() {
            write!(f, "FunctionDefinition({})", name.as_str())
        } else {
            write!(f, "FunctionDefinition")
        }
    }
}

#[derive(Debug)]
pub struct FunctionParameter<'a> {
    pub name: &'a Identifier<'a>,
    code: Code<'a>,
}

impl<'a> FunctionParameter<'a> {
    pub fn new(name: &'a Identifier<'a>, code: Code<'a>) -> Self {
        Self { name, code }
    }

    pub fn name(&self) -> &Identifier<'a> {
        self.name
    }
}

impl<'a> Node<'a> for FunctionParameter<'a> {
    fn code(&self) -> slice::Iter<'_, CodeKind<'a>> {
        self.code.iter()
    }
}

impl fmt::Display for FunctionParameter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FunctionParameter({})", self.name().as_str())
    }
}

#[derive(Debug)]
pub struct VariableDeclaration<'a> {
    pub pattern: Option<&'a Pattern<'a>>,
    pub init: Option<&'a Expression<'a>>,
    code: Code<'a>,
}

impl<'a> VariableDeclaration<'a> {
    pub fn new(
        pattern: Option<&'a Pattern<'a>>,
        init: Option<&'a Expression<'a>>,
        code: Code<'a>,
    ) -> Self {
        Self {
            pattern,
            init,
            code,
        }
    }
}

impl<'a> Node<'a> for VariableDeclaration<'a> {
    fn code(&self) -> slice::Iter<'_, CodeKind<'a>> {
        self.code.iter()
    }
}

impl fmt::Display for VariableDeclaration<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "VariableDeclaration")
    }
}

#[derive(Debug)]
pub struct Statement<'a> {
    pub kind: StatementKind<'a>,
    code: Code<'a>,
}

#[derive(Debug)]
pub enum StatementKind<'a> {
    Expression(&'a Expression<'a>),
    VariableDeclaration(&'a VariableDeclaration<'a>),
}

impl<'a> Statement<'a> {
    pub fn new(kind: StatementKind<'a>, code: Code<'a>) -> Self {
        Self { kind, code }
    }

    pub fn expression(&self) -> Option<&'a Expression<'a>> {
        if let StatementKind::Expression(ref expr) = self.kind {
            Some(expr)
        } else {
            None
        }
    }

    pub fn variable_declaration(&self) -> Option<&'a VariableDeclaration<'a>> {
        if let StatementKind::VariableDeclaration(ref decl) = self.kind {
            Some(decl)
        } else {
            None
        }
    }
}

impl<'a> Node<'a> for Statement<'a> {
    fn code(&self) -> slice::Iter<'_, CodeKind<'a>> {
        self.code.iter()
    }
}

impl fmt::Display for Statement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Statement")
    }
}

#[derive(Debug)]
pub struct Block<'a> {
    statements: Vec<&'a Statement<'a>>,
    scope: Rc<RefCell<Scope>>,
    code: Code<'a>,
}

impl<'a> Block<'a> {
    pub fn new(statements: Vec<&'a Statement<'a>>, code: Code<'a>) -> Self {
        Self {
            statements,
            scope: wrap(Scope::new()),
            code,
        }
    }

    pub fn scope(&self) -> &Rc<RefCell<Scope>> {
        &self.scope
    }

    pub fn statements(&self) -> slice::Iter<'_, &Statement<'a>> {
        self.statements.iter()
    }
}

impl<'a> Node<'a> for Block<'a> {
    fn code(&self) -> slice::Iter<'_, CodeKind<'a>> {
        self.code.iter()
    }
}

impl fmt::Display for Block<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Block")
    }
}

#[derive(Debug)]
pub struct Expression<'a> {
    kind: ExpressionKind<'a>,
    code: Code<'a>,
    r#type: Rc<RefCell<sem::Type>>,
}

impl<'a> Expression<'a> {
    pub fn new(kind: ExpressionKind<'a>, code: Code<'a>) -> Self {
        Self {
            kind,
            code,
            r#type: wrap(sem::Type::Unknown),
        }
    }

    pub fn kind(&self) -> &ExpressionKind<'a> {
        &self.kind
    }

    pub fn r#type(&self) -> &Rc<RefCell<sem::Type>> {
        &self.r#type
    }

    pub fn replace_type(&mut self, ty: &Rc<RefCell<sem::Type>>) {
        self.r#type = Rc::clone(ty);
    }

    pub fn variable_expression(&self) -> Option<&'a Identifier<'a>> {
        if let ExpressionKind::VariableExpression(id) = self.kind {
            Some(id)
        } else {
            None
        }
    }

    pub fn struct_literal(&self) -> Option<&StructLiteral<'a>> {
        if let ExpressionKind::StructLiteral(ref expr) = self.kind {
            Some(expr)
        } else {
            None
        }
    }

    pub fn subscript_expression(&self) -> Option<&SubscriptExpression<'a>> {
        if let ExpressionKind::SubscriptExpression(ref expr) = self.kind {
            Some(expr)
        } else {
            None
        }
    }

    pub fn binary_expression(&self) -> Option<&BinaryExpression<'a>> {
        if let ExpressionKind::BinaryExpression(ref expr) = self.kind {
            Some(expr)
        } else {
            None
        }
    }

    pub fn unary_expression(&self) -> Option<&UnaryExpression<'a>> {
        if let ExpressionKind::UnaryExpression(ref expr) = self.kind {
            Some(expr)
        } else {
            None
        }
    }

    pub fn array_expression(&self) -> Option<&ArrayExpression<'a>> {
        if let ExpressionKind::ArrayExpression(ref expr) = self.kind {
            Some(expr)
        } else {
            None
        }
    }

    pub fn call_expression(&self) -> Option<&CallExpression<'a>> {
        if let ExpressionKind::CallExpression(ref expr) = self.kind {
            Some(expr)
        } else {
            None
        }
    }

    pub fn member_expression(&self) -> Option<&MemberExpression<'a>> {
        if let ExpressionKind::MemberExpression(ref expr) = self.kind {
            Some(expr)
        } else {
            None
        }
    }

    pub fn if_expression(&self) -> Option<&IfExpression<'a>> {
        if let ExpressionKind::IfExpression(ref expr) = self.kind {
            Some(expr)
        } else {
            None
        }
    }

    pub fn case_expression(&self) -> Option<&CaseExpression<'a>> {
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

impl<'a> Node<'a> for Expression<'a> {
    fn code(&self) -> slice::Iter<'_, CodeKind<'a>> {
        self.code.iter()
    }
}

impl fmt::Display for Expression<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

#[derive(Debug)]
pub struct StructLiteral<'a> {
    pub name: &'a Identifier<'a>,
    pub fields: collections::Vec<'a, &'a ValueField<'a>>,
}

impl<'a> StructLiteral<'a> {
    pub fn new<I: IntoIterator<Item = &'a ValueField<'a>>>(
        tree: &'a Ast,
        name: &'a Identifier<'a>,
        fields: I,
    ) -> Self {
        Self {
            name,
            fields: collections::Vec::from_iter_in(fields, tree.arena()),
        }
    }

    pub fn name(&self) -> &'a Identifier<'a> {
        self.name
    }

    pub fn fields(&self) -> impl ExactSizeIterator<Item = &'a ValueField<'a>> + '_ {
        self.fields.iter().copied()
    }
}

#[derive(Debug)]
pub struct ValueField<'a> {
    pub name: &'a Identifier<'a>,
    pub value: Option<&'a Expression<'a>>,
    pub code: Code<'a>,
}

impl<'a> ValueField<'a> {
    pub fn new(
        name: &'a Identifier<'a>,
        value: Option<&'a Expression<'a>>,
        code: Code<'a>,
    ) -> Self {
        Self { name, value, code }
    }

    pub fn name(&self) -> &Identifier<'_> {
        self.name
    }
}

impl<'a> Node<'a> for ValueField<'a> {
    fn code(&self) -> slice::Iter<'_, CodeKind<'a>> {
        self.code.iter()
    }
}

impl fmt::Display for ValueField<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ValueField({})", self.name().as_str())
    }
}

#[derive(Debug)]
pub struct BinaryExpression<'a> {
    pub operator: BinaryOperator,
    pub lhs: &'a Expression<'a>,
    pub rhs: Option<&'a Expression<'a>>,
}

impl<'a> BinaryExpression<'a> {
    pub fn new(
        operator: BinaryOperator,
        lhs: &'a Expression<'a>,
        rhs: Option<&'a Expression<'a>>,
    ) -> Self {
        Self { operator, lhs, rhs }
    }

    pub fn lhs(&self) -> &'a Expression<'a> {
        self.lhs
    }

    pub fn rhs(&self) -> Option<&'a Expression<'a>> {
        self.rhs
    }
}

#[derive(Debug)]
pub struct UnaryExpression<'a> {
    pub operator: UnaryOperator,
    pub operand: Option<&'a Expression<'a>>,
}

impl<'a> UnaryExpression<'a> {
    pub fn new(operator: UnaryOperator, operand: Option<&'a Expression<'a>>) -> Self {
        Self { operator, operand }
    }

    pub fn operand(&self) -> Option<&'a Expression<'a>> {
        self.operand
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
pub struct SubscriptExpression<'a> {
    pub callee: &'a Expression<'a>,
    pub arguments: Vec<&'a Expression<'a>>,
}

impl<'a> SubscriptExpression<'a> {
    pub fn new(callee: &'a Expression<'a>, arguments: Vec<&'a Expression<'a>>) -> Self {
        Self { callee, arguments }
    }

    pub fn callee(&self) -> &'a Expression<'a> {
        self.callee
    }

    pub fn arguments(&self) -> slice::Iter<'_, &Expression<'_>> {
        self.arguments.iter()
    }
}

#[derive(Debug)]
pub struct CallExpression<'a> {
    pub callee: &'a Expression<'a>,
    pub arguments: Vec<&'a Expression<'a>>,
}

impl<'a> CallExpression<'a> {
    pub fn new(callee: &'a Expression<'a>, arguments: Vec<&'a Expression<'a>>) -> Self {
        Self { callee, arguments }
    }

    pub fn callee(&self) -> &Expression<'a> {
        self.callee
    }

    pub fn arguments(&self) -> slice::Iter<'_, &Expression<'a>> {
        self.arguments.iter()
    }
}

#[derive(Debug)]
pub struct MemberExpression<'a> {
    pub object: &'a Expression<'a>,
    pub field: Option<&'a Identifier<'a>>,
}

impl<'a> MemberExpression<'a> {
    pub fn new(object: &'a Expression<'a>, field: Option<&'a Identifier<'a>>) -> Self {
        Self { object, field }
    }
}

#[derive(Debug)]
pub struct ArrayExpression<'a> {
    pub elements: Vec<&'a Expression<'a>>,
}

impl<'a> ArrayExpression<'a> {
    pub fn new(elements: Vec<&'a Expression<'a>>) -> Self {
        Self { elements }
    }

    pub fn elements(&self) -> slice::Iter<'_, &Expression<'a>> {
        self.elements.iter()
    }
}

#[derive(Debug)]
pub struct IfExpression<'a> {
    pub condition: Option<&'a Expression<'a>>,
    pub then_body: &'a Block<'a>,
    pub else_body: Option<&'a Block<'a>>,
}

impl<'a> IfExpression<'a> {
    pub fn new(
        condition: Option<&'a Expression<'a>>,
        then_body: &'a Block<'a>,
        else_body: Option<&'a Block<'a>>,
    ) -> Self {
        Self {
            condition,
            then_body,
            else_body,
        }
    }
}

#[derive(Debug)]
pub struct CaseExpression<'a> {
    pub head: Option<&'a Expression<'a>>,
    pub arms: Vec<&'a CaseArm<'a>>,
    pub else_body: Option<&'a Block<'a>>,
}

impl<'a> CaseExpression<'a> {
    pub fn new(
        head: Option<&'a Expression<'a>>,
        arms: Vec<&'a CaseArm<'a>>,
        else_body: Option<&'a Block<'a>>,
    ) -> Self {
        Self {
            head,
            arms,
            else_body,
        }
    }
}

#[derive(Debug)]
pub struct CaseArm<'a> {
    pub pattern: Option<&'a Pattern<'a>>,
    pub guard: Option<&'a Expression<'a>>,
    pub then_body: &'a Block<'a>,

    // `CaseArm` is the only syntactic element other than Program and Block that introduces
    // a new scope. This scope is necessary to use the variables introduced in each arm in
    // the guard clause.
    scope: Rc<RefCell<Scope>>,
    code: Code<'a>,
}

impl<'a> CaseArm<'a> {
    pub fn new(
        pattern: Option<&'a Pattern<'a>>,
        guard: Option<&'a Expression<'a>>,
        then_body: &'a Block<'a>,
        code: Code<'a>,
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

    pub fn pattern(&self) -> Option<&'a Pattern<'a>> {
        self.pattern.as_deref()
    }
}

impl<'a> Node<'a> for CaseArm<'a> {
    fn code(&self) -> slice::Iter<'_, CodeKind<'a>> {
        self.code.iter()
    }
}

impl fmt::Display for CaseArm<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CaseArm")
    }
}

#[derive(Debug)]
pub enum ExpressionKind<'a> {
    IntegerLiteral(i32),
    StringLiteral(Option<String>),
    StructLiteral(StructLiteral),
    VariableExpression(&'a Identifier<'a>),
    BinaryExpression(BinaryExpression),
    UnaryExpression(UnaryExpression),
    SubscriptExpression(SubscriptExpression),
    CallExpression(CallExpression),
    ArrayExpression(ArrayExpression),
    MemberExpression(MemberExpression),
    IfExpression(IfExpression),
    CaseExpression(CaseExpression),
    Expression(Option<&'a Expression<'a>>),
}

#[derive(Debug)]
pub struct Pattern<'a> {
    pub kind: PatternKind,
    pub code: Code<'a>,
}

impl<'a> Pattern<'a> {
    pub fn new(kind: PatternKind, code: Code<'a>) -> Self {
        Self { kind, code }
    }

    pub fn variable_pattern(identifier: &'a Identifier<'a>) -> Self {
        Self {
            kind: PatternKind::VariablePattern(Rc::clone(identifier)),
            code: Code::with_node(NodeKind::Identifier(Rc::clone(identifier))),
        }
    }
}

impl<'a> Node<'a> for Pattern<'a> {
    fn code(&self) -> slice::Iter<'_, CodeKind<'a>> {
        self.code.iter()
    }
}

impl fmt::Display for Pattern<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Pattern")
    }
}

#[derive(Debug)]
pub struct ArrayPattern<'a> {
    elements: Vec<&'a Pattern<'a>>,
}

impl<'a> ArrayPattern<'a> {
    pub fn new(elements: Vec<&'a Pattern<'a>>) -> Self {
        Self { elements }
    }

    pub fn elements(&self) -> slice::Iter<'_, &Pattern<'a>> {
        self.elements.iter()
    }
}

#[derive(Debug)]
pub struct RestPattern<'a> {
    pub id: Option<&'a Identifier<'a>>,
}

impl<'a> RestPattern<'a> {
    pub fn new(id: Option<&'a Identifier<'a>>) -> Self {
        Self { id }
    }
}

#[derive(Debug)]
pub struct StructPattern<'a> {
    pub name: &'a Identifier<'a>,
    fields: Vec<&'a ValueFieldPattern<'a>>,
}

impl<'a> StructPattern<'a> {
    pub fn new(name: &'a Identifier<'a>, fields: Vec<&'a ValueFieldPattern<'a>>) -> Self {
        Self { name, fields }
    }

    pub fn fields(&self) -> slice::Iter<'_, &ValueFieldPattern<'a>> {
        self.fields.iter()
    }
}

#[derive(Debug)]
pub struct ValueFieldPattern<'a> {
    pub name: &'a Identifier<'a>,
    pub value: Option<&'a Pattern<'a>>,
    pub code: Code<'a>,
}

impl<'a> ValueFieldPattern<'a> {
    pub fn new(name: &'a Identifier<'a>, value: Option<&'a Pattern<'a>>, code: Code<'a>) -> Self {
        Self { name, value, code }
    }
}

impl<'a> Node<'a> for ValueFieldPattern<'a> {
    fn code(&self) -> slice::Iter<'_, CodeKind<'a>> {
        self.code.iter()
    }
}

impl fmt::Display for ValueFieldPattern<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ValueFieldPattern({})", self.name)
    }
}

#[derive(Debug)]
pub enum PatternKind<'a> {
    IntegerPattern(i32),
    StringPattern(Option<String>),
    VariablePattern(&'a Identifier<'a>),
    ArrayPattern(ArrayPattern),
    RestPattern(RestPattern),
    StructPattern(StructPattern),
}

impl fmt::Display for NodeKind<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NodeKind::Program(program) => program.fmt(f),
            NodeKind::Block(block) => block.fmt(f),
            NodeKind::Identifier(id) => write!(f, "Identifier({})", id),
            NodeKind::StructDefinition(definition) => definition.fmt(f),
            NodeKind::FunctionDefinition(definition) => definition.fmt(f),
            NodeKind::TypeField(field) => field.fmt(f),
            NodeKind::TypeAnnotation(ty) => ty.fmt(f),
            NodeKind::ValueField(field) => field.fmt(f),
            NodeKind::ValueFieldPattern(pattern) => pattern.fmt(f),
            NodeKind::FunctionParameter(param) => param.fmt(f),
            NodeKind::Statement(stmt) => stmt.fmt(f),
            NodeKind::VariableDeclaration(declaration) => declaration.fmt(f),
            NodeKind::Pattern(pattern) => pattern.fmt(f),
            NodeKind::CaseArm(arm) => arm.fmt(f),
            NodeKind::Expression(expr) => expr.fmt(f),
        }
    }
}

impl fmt::Display for ExpressionKind<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExpressionKind::IntegerLiteral(i) => write!(f, "IntegerLiteral({})", i),
            ExpressionKind::StringLiteral(s) => {
                write!(
                    f,
                    "StringLiteral({})",
                    s.as_ref().unwrap_or(&"-".to_string())
                )
            }
            ExpressionKind::VariableExpression(expr) => write!(f, "VariableExpression({})", expr),
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
