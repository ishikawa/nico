//! Grammar
//! -------
//!
//! ```ignore
//! Program             := TopLevel*
//! TopLevel            := Statement | FunctionDeclaration | StructDeclaration
//! FunctionDeclaration := "export"? "fun" Id "(" (Parameter ",")* Parameter? ")" Block "end"
//! Parameter           := Id
//! StructDeclaration   := "export"? "struct" Id "{" (TypeField ",")* TypeField? "}"
//! TypeField           := Id ":" TypeAnnotation
//! Block               := Statement*
//! Statement           := VariableDeclaration | Expression
//! VariableDeclaration := "let" Pattern "=" Expression
//! Expression          := IntegerLiteral | StringLiteral | StructLiteral | VariableExpression
//!                      | BinaryExpression | UnaryExpression | SubscriptExpression | CallExpression
//!                      | ArrayExpression | MemberExpression | IfExpression | CaseExpression
//!                      | ExpressionGroup
//! ExpressionGroup.    := "(" Expression ")"
//! Id                  := <Identifier>
//! TypeAnnotation      := <Int32>
//! IntegerLiteral      := <Integer>
//! StringLiteral       := <String>
//! VariableExpression  := Id
//! StructLiteral       := Id "{" (ValueField ",")* ValueField? "}"
//! ValueField          := Id (":" Expression)?
//! BinaryExpression    := Expression ("+" | "-" | "*" | "/"| "%") Expression
//! UnaryExpression     := ("!" | "-") Expression
//! SubscriptExpression := Expression "[" Expression "]"
//! CallExpression      := Expression "(" (Expression ",")* Expression?* "]"
//! ArrayExpression     := "[" (Expression ",")* Expression? "]"
//! MemberExpression    := Expression "." Id
//! IfExpression        := "if" Expression Block ("else" Block)? "end"
//! CaseExpression      := "case" Expression CaseArm* ("else" Block)? "end"
//! CaseArm             := "when" Pattern ("if" Expression)? Block
//! Pattern             := IntegerPattern | StringPattern | VariablePattern | ArrayPattern | RestPattern
//!                      | StructPattern
//! IntegerPattern      := <Integer>
//! StringPattern       := <String>
//! VariablePattern     := Id
//! StructPattern       := Id "{" (ValueFieldPattern ",")* ValueFieldPattern? "}"
//! ValueFieldPattern   := Id (":" Pattern)?
//! ArrayPattern        := "[" (Pattern ",")* Pattern? "]"
//! RestPattern.        := "..." Id?
//! ```
use super::{EffectiveRange, MissingTokenKind, Scope, SyntaxToken, Token};
use crate::{sem, util::wrap};
use bumpalo::collections::String as BumpaloString;
use bumpalo::collections::Vec as BumpaloVec;
use bumpalo::Bump as BumpaloArena;
use std::rc::Rc;
use std::slice;
use std::{cell::RefCell, fmt};

#[derive(Debug, Default)]
pub struct Ast {
    arena: BumpaloArena,
}

impl Ast {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn arena(&self) -> &bumpalo::Bump {
        &self.arena
    }

    #[allow(clippy::mut_from_ref)]
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
    pub fn program(&self) -> Option<&'a Program<'a>> {
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
                return std::ptr::eq(*definition1, *definition2);
            }
        }

        if let DefinitionKind::FunctionDefinition(definition1) = self {
            if let DefinitionKind::FunctionDefinition(definition2) = other {
                return std::ptr::eq(*definition1, *definition2);
            }
        }

        if let DefinitionKind::FunctionParameter(definition1) = self {
            if let DefinitionKind::FunctionParameter(definition2) = other {
                return std::ptr::eq(*definition1, *definition2);
            }
        }

        if let DefinitionKind::Pattern(definition1) = self {
            if let DefinitionKind::Pattern(definition2) = other {
                return std::ptr::eq(*definition1, *definition2);
            }
        }

        false
    }
}

#[derive(Debug)]
pub struct Code<'a> {
    code: BumpaloVec<'a, CodeKind<'a>>,
}

impl<'a> Code<'a> {
    pub fn new(tree: &'a Ast) -> Self {
        Self {
            code: BumpaloVec::new_in(&tree.arena),
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
    body: BumpaloVec<'a, TopLevelKind<'a>>,
    declarations: Rc<RefCell<Scope<'a>>>,
    main_scope: Rc<RefCell<Scope<'a>>>,
    code: Code<'a>,
}

impl<'a> Program<'a> {
    pub fn new<I: IntoIterator<Item = TopLevelKind<'a>>>(
        tree: &'a Ast,
        body: I,
        code: Code<'a>,
    ) -> Program<'a> {
        let declarations = wrap(Scope::prelude());
        let main_scope = wrap(Scope::new());

        Program {
            body: BumpaloVec::from_iter_in(body, tree.arena()),
            declarations,
            main_scope,
            code,
        }
    }

    pub fn body(&self) -> impl ExactSizeIterator<Item = &TopLevelKind<'a>> + '_ {
        self.body.iter()
    }

    pub fn declarations_scope(&self) -> &Rc<RefCell<Scope<'a>>> {
        &self.declarations
    }

    pub fn main_scope(&self) -> &Rc<RefCell<Scope<'a>>> {
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
    id: BumpaloString<'a>,
    code: Code<'a>,
}

impl<'a> Identifier<'a> {
    pub fn new<S: AsRef<str>>(tree: &'a Ast, id: S, code: Code<'a>) -> Self {
        Self {
            id: BumpaloString::from_str_in(id.as_ref(), tree.arena()),
            code,
        }
    }

    pub fn as_str(&self) -> &str {
        self.id.as_str()
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
    name: Option<&'a Identifier<'a>>,
    fields: BumpaloVec<'a, &'a TypeField<'a>>,
    r#type: Rc<RefCell<sem::Type>>,
    code: Code<'a>,
}

impl<'a> StructDefinition<'a> {
    pub fn new<I: IntoIterator<Item = &'a TypeField<'a>>>(
        tree: &'a Ast,
        name: Option<&'a Identifier<'a>>,
        fields: I,
        code: Code<'a>,
    ) -> Self {
        Self {
            name,
            fields: BumpaloVec::from_iter_in(fields, tree.arena()),
            code,
            r#type: wrap(sem::Type::Unknown),
        }
    }

    pub fn name(&self) -> Option<&'a Identifier<'a>> {
        self.name
    }

    pub fn fields(&self) -> impl ExactSizeIterator<Item = &'a TypeField<'a>> + '_ {
        self.fields.iter().copied()
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
            .and_then(|f| f.type_annotation)
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
    name: Option<&'a Identifier<'a>>,
    type_annotation: Option<&'a TypeAnnotation<'a>>,
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

    pub fn type_annotation(&self) -> Option<&'a TypeAnnotation<'a>> {
        self.type_annotation
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
    r#type: Rc<RefCell<sem::Type>>,
    code: Code<'a>,
}

impl<'a> TypeAnnotation<'a> {
    pub fn new(r#type: Rc<RefCell<sem::Type>>, code: Code<'a>) -> Self {
        Self { r#type, code }
    }

    pub fn r#type(&self) -> &Rc<RefCell<sem::Type>> {
        &self.r#type
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
    name: Option<&'a Identifier<'a>>,
    parameters: BumpaloVec<'a, &'a FunctionParameter<'a>>,
    body: &'a Block<'a>,
    code: Code<'a>,
}

impl<'a> FunctionDefinition<'a> {
    pub fn new<I: IntoIterator<Item = &'a FunctionParameter<'a>>>(
        tree: &'a Ast,
        name: Option<&'a Identifier<'a>>,
        parameters: I,
        body: &'a Block<'a>,
        code: Code<'a>,
    ) -> Self {
        Self {
            name,
            parameters: BumpaloVec::from_iter_in(parameters, tree.arena()),
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

    pub fn parameters(&self) -> impl ExactSizeIterator<Item = &'a FunctionParameter<'a>> + '_ {
        self.parameters.iter().copied()
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
    name: &'a Identifier<'a>,
    code: Code<'a>,
}

impl<'a> FunctionParameter<'a> {
    pub fn new(name: &'a Identifier<'a>, code: Code<'a>) -> Self {
        Self { name, code }
    }

    pub fn name(&self) -> &'a Identifier<'a> {
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
    pattern: Option<&'a Pattern<'a>>,
    init: Option<&'a Expression<'a>>,
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

    pub fn pattern(&self) -> Option<&'a Pattern<'a>> {
        self.pattern
    }

    pub fn init(&self) -> Option<&'a Expression<'a>> {
        self.init
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
    kind: StatementKind<'a>,
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

    pub fn kind(&self) -> &StatementKind<'a> {
        &self.kind
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
    statements: BumpaloVec<'a, &'a Statement<'a>>,
    scope: Rc<RefCell<Scope<'a>>>,
    code: Code<'a>,
}

impl<'a> Block<'a> {
    pub fn new<I: IntoIterator<Item = &'a Statement<'a>>>(
        tree: &'a Ast,
        statements: I,
        code: Code<'a>,
    ) -> Self {
        Self {
            statements: BumpaloVec::from_iter_in(statements, tree.arena()),
            scope: wrap(Scope::new()),
            code,
        }
    }

    pub fn scope(&self) -> &Rc<RefCell<Scope<'a>>> {
        &self.scope
    }

    pub fn statements(&self) -> impl ExactSizeIterator<Item = &'a Statement<'a>> + '_ {
        self.statements.iter().copied()
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
    name: &'a Identifier<'a>,
    fields: BumpaloVec<'a, &'a ValueField<'a>>,
}

impl<'a> StructLiteral<'a> {
    pub fn new<I: IntoIterator<Item = &'a ValueField<'a>>>(
        tree: &'a Ast,
        name: &'a Identifier<'a>,
        fields: I,
    ) -> Self {
        Self {
            name,
            fields: BumpaloVec::from_iter_in(fields, tree.arena()),
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
    name: &'a Identifier<'a>,
    value: Option<&'a Expression<'a>>,
    code: Code<'a>,
}

impl<'a> ValueField<'a> {
    pub fn new(
        name: &'a Identifier<'a>,
        value: Option<&'a Expression<'a>>,
        code: Code<'a>,
    ) -> Self {
        Self { name, value, code }
    }

    pub fn name(&self) -> &'a Identifier<'a> {
        self.name
    }

    pub fn value(&self) -> Option<&'a Expression<'a>> {
        self.value
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
    operator: BinaryOperator,
    lhs: &'a Expression<'a>,
    rhs: Option<&'a Expression<'a>>,
}

impl<'a> BinaryExpression<'a> {
    pub fn new(
        operator: BinaryOperator,
        lhs: &'a Expression<'a>,
        rhs: Option<&'a Expression<'a>>,
    ) -> Self {
        Self { operator, lhs, rhs }
    }

    pub fn operator(&self) -> BinaryOperator {
        self.operator
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
    operator: UnaryOperator,
    operand: Option<&'a Expression<'a>>,
}

impl<'a> UnaryExpression<'a> {
    pub fn new(operator: UnaryOperator, operand: Option<&'a Expression<'a>>) -> Self {
        Self { operator, operand }
    }

    pub fn operator(&self) -> UnaryOperator {
        self.operator
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
    callee: &'a Expression<'a>,
    arguments: BumpaloVec<'a, &'a Expression<'a>>,
}

impl<'a> SubscriptExpression<'a> {
    pub fn new<I: IntoIterator<Item = &'a Expression<'a>>>(
        tree: &'a Ast,
        callee: &'a Expression<'a>,
        arguments: I,
    ) -> Self {
        Self {
            callee,
            arguments: BumpaloVec::from_iter_in(arguments, tree.arena()),
        }
    }

    pub fn callee(&self) -> &'a Expression<'a> {
        self.callee
    }

    pub fn arguments(&self) -> impl ExactSizeIterator<Item = &'a Expression<'a>> + '_ {
        self.arguments.iter().copied()
    }
}

#[derive(Debug)]
pub struct CallExpression<'a> {
    callee: &'a Expression<'a>,
    arguments: BumpaloVec<'a, &'a Expression<'a>>,
}

impl<'a> CallExpression<'a> {
    pub fn new<I: IntoIterator<Item = &'a Expression<'a>>>(
        tree: &'a Ast,
        callee: &'a Expression<'a>,
        arguments: I,
    ) -> Self {
        Self {
            callee,
            arguments: BumpaloVec::from_iter_in(arguments, tree.arena()),
        }
    }

    pub fn callee(&self) -> &'a Expression<'a> {
        self.callee
    }

    pub fn arguments(&self) -> impl ExactSizeIterator<Item = &'a Expression<'a>> + '_ {
        self.arguments.iter().copied()
    }
}

#[derive(Debug)]
pub struct MemberExpression<'a> {
    object: &'a Expression<'a>,
    field: Option<&'a Identifier<'a>>,
}

impl<'a> MemberExpression<'a> {
    pub fn new(object: &'a Expression<'a>, field: Option<&'a Identifier<'a>>) -> Self {
        Self { object, field }
    }

    pub fn object(&self) -> &'a Expression<'a> {
        self.object
    }

    pub fn field(&self) -> Option<&'a Identifier<'a>> {
        self.field
    }
}

#[derive(Debug)]
pub struct ArrayExpression<'a> {
    elements: BumpaloVec<'a, &'a Expression<'a>>,
}

impl<'a> ArrayExpression<'a> {
    pub fn new<I: IntoIterator<Item = &'a Expression<'a>>>(tree: &'a Ast, elements: I) -> Self {
        Self {
            elements: BumpaloVec::from_iter_in(elements, tree.arena()),
        }
    }

    pub fn elements(&self) -> impl ExactSizeIterator<Item = &'a Expression<'a>> + '_ {
        self.elements.iter().copied()
    }
}

#[derive(Debug)]
pub struct IfExpression<'a> {
    condition: Option<&'a Expression<'a>>,
    then_body: &'a Block<'a>,
    else_body: Option<&'a Block<'a>>,
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

    pub fn condition(&self) -> Option<&'a Expression<'a>> {
        self.condition
    }

    pub fn then_body(&self) -> &'a Block<'a> {
        self.then_body
    }

    pub fn else_body(&self) -> Option<&'a Block<'a>> {
        self.else_body
    }
}

#[derive(Debug)]
pub struct CaseExpression<'a> {
    head: Option<&'a Expression<'a>>,
    arms: BumpaloVec<'a, &'a CaseArm<'a>>,
    else_body: Option<&'a Block<'a>>,
}

impl<'a> CaseExpression<'a> {
    pub fn new<I: IntoIterator<Item = &'a CaseArm<'a>>>(
        tree: &'a Ast,
        head: Option<&'a Expression<'a>>,
        arms: I,
        else_body: Option<&'a Block<'a>>,
    ) -> Self {
        Self {
            head,
            arms: BumpaloVec::from_iter_in(arms, tree.arena()),
            else_body,
        }
    }

    pub fn head(&self) -> Option<&'a Expression<'a>> {
        self.head
    }

    pub fn arms(&self) -> impl ExactSizeIterator<Item = &'a CaseArm<'a>> + '_ {
        self.arms.iter().copied()
    }

    pub fn else_body(&self) -> Option<&'a Block<'a>> {
        self.else_body
    }
}

#[derive(Debug)]
pub struct CaseArm<'a> {
    pattern: Option<&'a Pattern<'a>>,
    guard: Option<&'a Expression<'a>>,
    then_body: &'a Block<'a>,

    // `CaseArm` is the only syntactic element other than Program and Block that introduces
    // a new scope. This scope is necessary to use the variables introduced in each arm in
    // the guard clause.
    scope: Rc<RefCell<Scope<'a>>>,
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

    pub fn scope(&self) -> &Rc<RefCell<Scope<'a>>> {
        &self.scope
    }

    pub fn pattern(&self) -> Option<&'a Pattern<'a>> {
        self.pattern
    }

    pub fn guard(&self) -> Option<&'a Expression<'a>> {
        self.guard
    }

    pub fn then_body(&self) -> &'a Block<'a> {
        self.then_body
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

#[derive(Debug, Clone, PartialEq, Hash)]
pub struct IntegerLiteral {
    value: i32,
}

impl IntegerLiteral {
    pub fn new(value: i32) -> Self {
        Self { value }
    }

    pub fn value(&self) -> i32 {
        self.value
    }
}

#[derive(Debug, Clone, PartialEq, Hash)]
pub struct StringLiteral<'a> {
    value: Option<BumpaloString<'a>>,
}

impl<'a> StringLiteral<'a> {
    pub fn new<S: AsRef<str>>(tree: &'a Ast, value: Option<S>) -> Self {
        Self {
            value: value.map(|x| BumpaloString::from_str_in(x.as_ref(), tree.arena())),
        }
    }

    pub fn value(&self) -> Option<&str> {
        self.value.as_deref()
    }
}

#[derive(Debug)]
pub enum ExpressionKind<'a> {
    IntegerLiteral(IntegerLiteral),
    StringLiteral(StringLiteral<'a>),
    StructLiteral(StructLiteral<'a>),
    VariableExpression(&'a Identifier<'a>),
    BinaryExpression(BinaryExpression<'a>),
    UnaryExpression(UnaryExpression<'a>),
    SubscriptExpression(SubscriptExpression<'a>),
    CallExpression(CallExpression<'a>),
    ArrayExpression(ArrayExpression<'a>),
    MemberExpression(MemberExpression<'a>),
    IfExpression(IfExpression<'a>),
    CaseExpression(CaseExpression<'a>),
    Expression(Option<&'a Expression<'a>>),
}

#[derive(Debug)]
pub struct Pattern<'a> {
    kind: PatternKind<'a>,
    code: Code<'a>,
}

impl<'a> Pattern<'a> {
    pub fn new(kind: PatternKind<'a>, code: Code<'a>) -> Self {
        Self { kind, code }
    }

    pub fn kind(&self) -> &PatternKind<'a> {
        &self.kind
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
    elements: BumpaloVec<'a, &'a Pattern<'a>>,
}

impl<'a> ArrayPattern<'a> {
    pub fn new<I: IntoIterator<Item = &'a Pattern<'a>>>(tree: &'a Ast, elements: I) -> Self {
        Self {
            elements: BumpaloVec::from_iter_in(elements, tree.arena()),
        }
    }

    pub fn elements(&self) -> impl ExactSizeIterator<Item = &'a Pattern<'a>> + '_ {
        self.elements.iter().copied()
    }
}

#[derive(Debug)]
pub struct RestPattern<'a> {
    id: Option<&'a Identifier<'a>>,
}

impl<'a> RestPattern<'a> {
    pub fn new(id: Option<&'a Identifier<'a>>) -> Self {
        Self { id }
    }

    pub fn id(&self) -> Option<&'a Identifier<'a>> {
        self.id
    }
}

#[derive(Debug)]
pub struct StructPattern<'a> {
    name: &'a Identifier<'a>,
    fields: BumpaloVec<'a, &'a ValueFieldPattern<'a>>,
}

impl<'a> StructPattern<'a> {
    pub fn new<I: IntoIterator<Item = &'a ValueFieldPattern<'a>>>(
        tree: &'a Ast,
        name: &'a Identifier<'a>,
        fields: I,
    ) -> Self {
        Self {
            name,
            fields: BumpaloVec::from_iter_in(fields, tree.arena()),
        }
    }

    pub fn name(&self) -> &'a Identifier<'a> {
        self.name
    }

    pub fn fields(&self) -> impl ExactSizeIterator<Item = &'a ValueFieldPattern<'a>> + '_ {
        self.fields.iter().copied()
    }
}

#[derive(Debug)]
pub struct ValueFieldPattern<'a> {
    name: &'a Identifier<'a>,
    value: Option<&'a Pattern<'a>>,
    omitted_value: Option<&'a Pattern<'a>>,
    code: Code<'a>,
}

impl<'a> ValueFieldPattern<'a> {
    pub fn new(
        tree: &'a Ast,
        name: &'a Identifier<'a>,
        value: Option<&'a Pattern<'a>>,
        code: Code<'a>,
    ) -> Self {
        if value.is_some() {
            Self {
                name,
                value,
                omitted_value: None,
                code,
            }
        } else {
            let kind = PatternKind::VariablePattern(name);
            let omitted_value = tree.alloc(Pattern::new(
                kind,
                Code::with_node(tree, NodeKind::Identifier(name)),
            ));

            Self {
                name,
                value,
                omitted_value: Some(omitted_value),
                code,
            }
        }
    }

    pub fn name(&self) -> &'a Identifier<'a> {
        self.name
    }

    pub fn value(&self) -> Option<&'a Pattern<'a>> {
        self.value
    }

    pub fn omitted_value(&self) -> Option<&'a Pattern<'a>> {
        self.omitted_value
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
    IntegerPattern(IntegerLiteral),
    StringPattern(StringLiteral<'a>),
    VariablePattern(&'a Identifier<'a>),
    ArrayPattern(ArrayPattern<'a>),
    RestPattern(RestPattern<'a>),
    StructPattern(StructPattern<'a>),
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
            ExpressionKind::IntegerLiteral(i) => write!(f, "IntegerLiteral({})", i.value()),
            ExpressionKind::StringLiteral(s) => {
                write!(
                    f,
                    "StringLiteral({})",
                    s.value().unwrap_or(&"-".to_string())
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
