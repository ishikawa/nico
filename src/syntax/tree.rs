//! Grammar
//! -------
//!
//! ```ignore
//! Program             := TopLevel*
//! TopLevel            := Statement | FunctionDeclaration | StructDeclaration
//! FunctionDeclaration := "export"? "fun" Id "(" FunctionParameter (, FunctionParameter)* ,? ")" Block "end"
//! FunctionParameter   := Id
//! StructDeclaration   := "export"? "struct" Id "{" TypeField (, TypeField)* ,? "}"
//! TypeField           := Id ":" TypeAnnotation
//! Block               := Statement*
//! Statement           := VariableDeclaration | Expression
//! VariableDeclaration := "let" Pattern "=" Expression
//! Expression          := IntegerLiteral | StringLiteral | StructLiteral | VariableExpression
//!                      | BinaryExpression | UnaryExpression | SubscriptExpression | CallExpression
//!                      | ArrayExpression | MemberExpression | IfExpression | CaseExpression
//!                      | GroupedExpression
//! GroupedExpression   := "(" Expression ")"
//! Id                  := <Identifier>
//! TypeAnnotation      := <Int32>
//! IntegerLiteral      := <Integer>
//! StringLiteral       := <String>
//! VariableExpression  := Id
//! StructLiteral       := Id "{" ValueField (, ValueField)* ,? "}"
//! ValueField          := Id (":" Expression)?
//! BinaryExpression    := Expression ("+" | "-" | "*" | "/"| "%") Expression
//! UnaryExpression     := ("!" | "-") Expression
//! SubscriptExpression := Expression "[" Expression "]"
//! CallExpression      := Expression "(" Expression (, Expression)* ,?* "]"
//! ArrayExpression     := "[" Expression (, Expression)* ,? "]"
//! MemberExpression    := Expression "." Id
//! IfExpression        := "if" Expression Block ("else" Block)? "end"
//! CaseExpression      := "case" Expression CaseArm* ("else" Block)? "end"
//! CaseArm             := "when" Pattern ("if" Expression)? Block
//! Pattern             := IntegerPattern | StringPattern | VariablePattern | ArrayPattern | RestPattern
//!                      | StructPattern
//! IntegerPattern      := <Integer>
//! StringPattern       := <String>
//! VariablePattern     := Id
//! StructPattern       := Id "{" ValueFieldPattern (, ValueFieldPattern)* ,? "}"
//! ValueFieldPattern   := Id (":" Pattern)?
//! ArrayPattern        := "[" Pattern (, Pattern)* ,? "]"
//! RestPattern         := "..." Id?
//! ```
use super::{Code, CodeKind, CodeKindIter, EffectiveRange, Scope, Token};
use crate::arena::{BumpaloArena, BumpaloString, BumpaloVec};
use crate::semantic::TypeKind;
use std::cell::Cell;
use std::fmt;

pub trait Node<'arena> {
    fn code(&self) -> CodeKindIter<'_, 'arena>;

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
    TopLevel(&'a TopLevel<'a>),
    Block(&'a Block<'a>),
    Identifier(&'a Identifier<'a>),
    StructDefinition(&'a StructDefinition<'a>),
    FunctionDefinition(&'a FunctionDefinition<'a>),
    FunctionParameter(&'a FunctionParameter<'a>),
    TypeField(&'a TypeField<'a>),
    TypeAnnotation(&'a TypeAnnotation<'a>),
    ValueField(&'a ValueField<'a>),
    Statement(&'a Statement<'a>),
    VariableDeclaration(&'a VariableDeclaration<'a>),
    Expression(&'a Expression<'a>),
    IntegerLiteral(&'a IntegerLiteral<'a>),
    StringLiteral(&'a StringLiteral<'a>),
    StructLiteral(&'a StructLiteral<'a>),
    VariableExpression(&'a VariableExpression<'a>),
    BinaryExpression(&'a BinaryExpression<'a>),
    UnaryExpression(&'a UnaryExpression<'a>),
    SubscriptExpression(&'a SubscriptExpression<'a>),
    CallExpression(&'a CallExpression<'a>),
    ArrayExpression(&'a ArrayExpression<'a>),
    MemberExpression(&'a MemberExpression<'a>),
    IfExpression(&'a IfExpression<'a>),
    CaseExpression(&'a CaseExpression<'a>),
    CaseArm(&'a CaseArm<'a>),
    Pattern(&'a Pattern<'a>),
    VariablePattern(&'a VariablePattern<'a>),
    ArrayPattern(&'a ArrayPattern<'a>),
    RestPattern(&'a RestPattern<'a>),
    StructPattern(&'a StructPattern<'a>),
    ValueFieldPattern(&'a ValueFieldPattern<'a>),
    GroupedExpression(&'a GroupedExpression<'a>),
}

impl<'a> From<&ExpressionKind<'a>> for NodeKind<'a> {
    fn from(expr: &ExpressionKind<'a>) -> Self {
        match expr {
            ExpressionKind::IntegerLiteral(kind) => NodeKind::IntegerLiteral(kind),
            ExpressionKind::StringLiteral(kind) => NodeKind::StringLiteral(kind),
            ExpressionKind::StructLiteral(kind) => NodeKind::StructLiteral(kind),
            ExpressionKind::VariableExpression(kind) => NodeKind::VariableExpression(kind),
            ExpressionKind::BinaryExpression(kind) => NodeKind::BinaryExpression(kind),
            ExpressionKind::UnaryExpression(kind) => NodeKind::UnaryExpression(kind),
            ExpressionKind::SubscriptExpression(kind) => NodeKind::SubscriptExpression(kind),
            ExpressionKind::CallExpression(kind) => NodeKind::CallExpression(kind),
            ExpressionKind::ArrayExpression(kind) => NodeKind::ArrayExpression(kind),
            ExpressionKind::MemberExpression(kind) => NodeKind::MemberExpression(kind),
            ExpressionKind::IfExpression(kind) => NodeKind::IfExpression(kind),
            ExpressionKind::CaseExpression(kind) => NodeKind::CaseExpression(kind),
            ExpressionKind::GroupedExpression(kind) => NodeKind::GroupedExpression(kind),
        }
    }
}

impl<'a> From<&StatementKind<'a>> for NodeKind<'a> {
    fn from(stmt: &StatementKind<'a>) -> Self {
        match stmt {
            StatementKind::Expression(node) => NodeKind::Expression(node),
            StatementKind::VariableDeclaration(node) => NodeKind::VariableDeclaration(node),
        }
    }
}

impl<'a> From<&PatternKind<'a>> for NodeKind<'a> {
    fn from(pat: &PatternKind<'a>) -> Self {
        match pat {
            PatternKind::IntegerPattern(kind) => NodeKind::IntegerLiteral(kind),
            PatternKind::StringPattern(kind) => NodeKind::StringLiteral(kind),
            PatternKind::VariablePattern(kind) => NodeKind::VariablePattern(kind),
            PatternKind::ArrayPattern(kind) => NodeKind::ArrayPattern(kind),
            PatternKind::RestPattern(kind) => NodeKind::RestPattern(kind),
            PatternKind::StructPattern(kind) => NodeKind::StructPattern(kind),
            PatternKind::ValueFieldPattern(kind) => NodeKind::ValueFieldPattern(kind),
        }
    }
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
        if let NodeKind::StructLiteral(node) = self {
            return Some(node);
        }

        None
    }

    pub fn variable_expression(&self) -> Option<&'a VariableExpression<'a>> {
        if let NodeKind::VariableExpression(node) = self {
            return Some(node);
        }
        None
    }

    pub fn variable_pattern(&self) -> Option<&'a VariablePattern<'a>> {
        if let NodeKind::VariablePattern(node) = self {
            return Some(node);
        }
        None
    }

    pub fn member_expression(&self) -> Option<&'a MemberExpression<'a>> {
        if let NodeKind::MemberExpression(node) = self {
            return Some(node);
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
    fn code(&self) -> CodeKindIter<'_, 'a> {
        match self {
            NodeKind::Program(kind) => kind.code(),
            NodeKind::TopLevel(kind) => kind.code(),
            NodeKind::Block(kind) => kind.code(),
            NodeKind::Identifier(kind) => kind.code(),
            NodeKind::StructDefinition(kind) => kind.code(),
            NodeKind::FunctionDefinition(kind) => kind.code(),
            NodeKind::TypeField(kind) => kind.code(),
            NodeKind::ValueField(kind) => kind.code(),
            NodeKind::TypeAnnotation(kind) => kind.code(),
            NodeKind::FunctionParameter(kind) => kind.code(),
            NodeKind::Statement(kind) => kind.code(),
            NodeKind::VariableDeclaration(kind) => kind.code(),
            NodeKind::Expression(kind) => kind.code(),
            NodeKind::IntegerLiteral(kind) => kind.code(),
            NodeKind::StructLiteral(kind) => kind.code(),
            NodeKind::StringLiteral(kind) => kind.code(),
            NodeKind::VariableExpression(kind) => kind.code(),
            NodeKind::BinaryExpression(kind) => kind.code(),
            NodeKind::UnaryExpression(kind) => kind.code(),
            NodeKind::SubscriptExpression(kind) => kind.code(),
            NodeKind::CallExpression(kind) => kind.code(),
            NodeKind::ArrayExpression(kind) => kind.code(),
            NodeKind::MemberExpression(kind) => kind.code(),
            NodeKind::IfExpression(kind) => kind.code(),
            NodeKind::CaseExpression(kind) => kind.code(),
            NodeKind::CaseArm(kind) => kind.code(),
            NodeKind::Pattern(kind) => kind.code(),
            NodeKind::VariablePattern(kind) => kind.code(),
            NodeKind::ArrayPattern(kind) => kind.code(),
            NodeKind::RestPattern(kind) => kind.code(),
            NodeKind::StructPattern(kind) => kind.code(),
            NodeKind::ValueFieldPattern(kind) => kind.code(),
            NodeKind::GroupedExpression(kind) => kind.code(),
        }
    }
}

#[derive(Debug)]
pub struct TopLevel<'a> {
    kind: TopLevelKind<'a>,
    code: Code<'a>,
}

impl<'a> TopLevel<'a> {
    pub fn new(kind: TopLevelKind<'a>, code: Code<'a>) -> Self {
        Self { kind, code }
    }

    pub fn kind(&self) -> &TopLevelKind<'a> {
        &self.kind
    }

    pub fn statement(&self) -> Option<&'a Statement<'a>> {
        self.kind().statement()
    }
}

impl<'a> Node<'a> for TopLevel<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
        self.code.iter()
    }
}

impl fmt::Display for TopLevel<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TopLevel ({})", self.kind())
    }
}

#[derive(Debug)]
pub enum TopLevelKind<'a> {
    StructDefinition(&'a StructDefinition<'a>),
    FunctionDefinition(&'a FunctionDefinition<'a>),
    Statement(&'a Statement<'a>),
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

impl fmt::Display for TopLevelKind<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TopLevelKind::StructDefinition(kind) => kind.fmt(f),
            TopLevelKind::FunctionDefinition(kind) => kind.fmt(f),
            TopLevelKind::Statement(kind) => kind.fmt(f),
        }
    }
}

#[derive(Debug)]
pub struct Program<'a> {
    body: BumpaloVec<'a, &'a TopLevel<'a>>,
    declarations: &'a Scope<'a>,
    main_scope: &'a Scope<'a>,
    code: Code<'a>,
}

impl<'a> Program<'a> {
    pub fn new<I: IntoIterator<Item = &'a TopLevel<'a>>>(
        arena: &'a BumpaloArena,
        body: I,
        code: Code<'a>,
    ) -> Program<'a> {
        let declarations = arena.alloc(Scope::prelude(arena));
        let main_scope = arena.alloc(Scope::new(arena));

        Program {
            body: BumpaloVec::from_iter_in(body, arena),
            declarations,
            main_scope,
            code,
        }
    }

    pub fn body(&self) -> impl ExactSizeIterator<Item = &'a TopLevel<'a>> + '_ {
        self.body.iter().copied()
    }

    pub fn declarations_scope(&self) -> &'a Scope<'a> {
        self.declarations
    }

    pub fn main_scope(&self) -> &'a Scope<'a> {
        self.main_scope
    }
}

impl<'a> Node<'a> for Program<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
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
    code: CodeKind<'a>,
}

impl<'a> Identifier<'a> {
    pub fn new<S: AsRef<str>>(arena: &'a BumpaloArena, id: S, token: Token) -> Self {
        Self {
            id: BumpaloString::from_str_in(id.as_ref(), arena),
            code: CodeKind::interpreted(token),
        }
    }

    pub fn as_str(&self) -> &str {
        self.id.as_str()
    }
}

impl<'a> AsRef<str> for Identifier<'a> {
    fn as_ref(&self) -> &str {
        self.id.as_ref()
    }
}

impl<'a> Node<'a> for Identifier<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
        CodeKindIter::from(&self.code)
    }
}

impl fmt::Display for Identifier<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.id.fmt(f)
    }
}

#[derive(Debug)]
pub struct StructDefinition<'a> {
    name: Option<&'a Identifier<'a>>,
    fields: BumpaloVec<'a, &'a TypeField<'a>>,
    code: Code<'a>,
    r#type: Cell<Option<TypeKind<'a>>>,
}

impl<'a> StructDefinition<'a> {
    pub fn new<I: IntoIterator<Item = &'a TypeField<'a>>>(
        arena: &'a BumpaloArena,
        name: Option<&'a Identifier<'a>>,
        fields: I,
        code: Code<'a>,
    ) -> Self {
        Self {
            name,
            fields: BumpaloVec::from_iter_in(fields, arena),
            code,
            r#type: Cell::default(),
        }
    }

    pub fn name(&self) -> Option<&'a Identifier<'a>> {
        self.name
    }

    pub fn fields(&self) -> impl ExactSizeIterator<Item = &'a TypeField<'a>> + '_ {
        self.fields.iter().copied()
    }

    pub fn get_field_type(&self, name: &str) -> Option<TypeKind<'a>> {
        self.fields
            .iter()
            .find(|f| {
                f.name()
                    .map_or(false, |field_name| field_name.as_str() == name)
            })
            .and_then(|f| f.type_annotation)
            .map(|annotation| annotation.r#type)
    }

    pub fn r#type(&self) -> Option<TypeKind<'a>> {
        self.r#type.get()
    }

    pub fn assign_type(&self, ty: TypeKind<'a>) {
        self.r#type.replace(Some(ty));
    }
}

impl<'a> Node<'a> for StructDefinition<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
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
    fn code(&self) -> CodeKindIter<'_, 'a> {
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
    r#type: TypeKind<'a>,
    code: Code<'a>,
}

impl<'a> TypeAnnotation<'a> {
    pub fn new(r#type: TypeKind<'a>, code: Code<'a>) -> Self {
        Self { r#type, code }
    }

    pub fn r#type(&self) -> TypeKind<'a> {
        self.r#type
    }
}

impl<'a> Node<'a> for TypeAnnotation<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
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
    r#type: Cell<Option<TypeKind<'a>>>,
}

impl<'a> FunctionDefinition<'a> {
    pub fn new<I: IntoIterator<Item = &'a FunctionParameter<'a>>>(
        arena: &'a BumpaloArena,
        name: Option<&'a Identifier<'a>>,
        parameters: I,
        body: &'a Block<'a>,
        code: Code<'a>,
    ) -> Self {
        Self {
            name,
            parameters: BumpaloVec::from_iter_in(parameters, arena),
            body,
            code,
            r#type: Cell::default(),
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

    pub fn r#type(&self) -> Option<TypeKind<'a>> {
        self.r#type.get()
    }

    pub fn assign_type(&self, ty: TypeKind<'a>) {
        self.r#type.replace(Some(ty));
    }
}

impl<'a> Node<'a> for FunctionDefinition<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
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
    r#type: Cell<Option<TypeKind<'a>>>,
}

impl<'a> FunctionParameter<'a> {
    pub fn new(name: &'a Identifier<'a>, code: Code<'a>) -> Self {
        Self {
            name,
            code,
            r#type: Cell::default(),
        }
    }

    pub fn name(&self) -> &'a Identifier<'a> {
        self.name
    }

    pub fn r#type(&self) -> Option<TypeKind<'a>> {
        self.r#type.get()
    }

    pub fn assign_type(&self, ty: TypeKind<'a>) {
        self.r#type.replace(Some(ty));
    }
}

impl<'a> Node<'a> for FunctionParameter<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
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
    fn code(&self) -> CodeKindIter<'_, 'a> {
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
    code: CodeKind<'a>,
}

#[derive(Debug)]
pub enum StatementKind<'a> {
    Expression(&'a Expression<'a>),
    VariableDeclaration(&'a VariableDeclaration<'a>),
}

impl<'a> Statement<'a> {
    pub fn new(kind: StatementKind<'a>) -> Self {
        let code = CodeKind::Node(NodeKind::from(&kind));
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
    fn code(&self) -> CodeKindIter<'_, 'a> {
        CodeKindIter::from(&self.code)
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
    scope: &'a Scope<'a>,
    code: Code<'a>,
}

impl<'a> Block<'a> {
    pub fn new<I: IntoIterator<Item = &'a Statement<'a>>>(
        arena: &'a BumpaloArena,
        statements: I,
        code: Code<'a>,
    ) -> Self {
        Self {
            statements: BumpaloVec::from_iter_in(statements, arena),
            scope: arena.alloc(Scope::new(arena)),
            code,
        }
    }

    pub fn scope(&self) -> &'a Scope<'a> {
        self.scope
    }

    pub fn statements(&self) -> impl ExactSizeIterator<Item = &'a Statement<'a>> + '_ {
        self.statements.iter().copied()
    }
}

impl<'a> Node<'a> for Block<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
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
    code: CodeKind<'a>,
}

impl<'a> Expression<'a> {
    pub fn new(kind: ExpressionKind<'a>) -> Self {
        let code = CodeKind::Node(NodeKind::from(&kind));
        Self { kind, code }
    }

    pub fn kind(&self) -> &ExpressionKind<'a> {
        &self.kind
    }

    pub fn variable_expression(&self) -> Option<&'a VariableExpression<'a>> {
        if let ExpressionKind::VariableExpression(expr) = self.kind {
            Some(expr)
        } else {
            None
        }
    }

    pub fn integer_literal(&self) -> Option<&IntegerLiteral<'a>> {
        if let ExpressionKind::IntegerLiteral(ref expr) = self.kind {
            Some(expr)
        } else {
            None
        }
    }

    pub fn string_literal(&self) -> Option<&StringLiteral<'a>> {
        if let ExpressionKind::StringLiteral(ref expr) = self.kind {
            Some(expr)
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

    pub fn r#type(&self) -> Option<TypeKind<'a>> {
        match self.kind() {
            ExpressionKind::IntegerLiteral(expr) => Some(expr.r#type()),
            ExpressionKind::StringLiteral(expr) => Some(expr.r#type()),
            ExpressionKind::VariableExpression(expr) => expr.r#type(),
            ExpressionKind::BinaryExpression(expr) => expr.r#type(),
            ExpressionKind::UnaryExpression(expr) => expr.r#type(),
            ExpressionKind::SubscriptExpression(expr) => expr.r#type(),
            ExpressionKind::CallExpression(expr) => expr.r#type(),
            ExpressionKind::ArrayExpression(expr) => expr.r#type(),
            ExpressionKind::IfExpression(expr) => expr.r#type(),
            ExpressionKind::CaseExpression(expr) => expr.r#type(),
            ExpressionKind::MemberExpression(expr) => expr.r#type(),
            ExpressionKind::StructLiteral(expr) => expr.r#type(),
            ExpressionKind::GroupedExpression(expr) => expr.r#type(),
        }
    }
}

impl<'a> Node<'a> for Expression<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
        CodeKindIter::from(&self.code)
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
    code: Code<'a>,
    r#type: Cell<Option<TypeKind<'a>>>,
}

impl<'a> StructLiteral<'a> {
    pub fn new<I: IntoIterator<Item = &'a ValueField<'a>>>(
        arena: &'a BumpaloArena,
        name: &'a Identifier<'a>,
        fields: I,
        code: Code<'a>,
    ) -> Self {
        Self {
            name,
            fields: BumpaloVec::from_iter_in(fields, arena),
            code,
            r#type: Cell::default(),
        }
    }

    pub fn name(&self) -> &'a Identifier<'a> {
        self.name
    }

    pub fn fields(&self) -> impl ExactSizeIterator<Item = &'a ValueField<'a>> + '_ {
        self.fields.iter().copied()
    }

    pub fn r#type(&self) -> Option<TypeKind<'a>> {
        self.r#type.get()
    }

    pub fn assign_type(&self, ty: TypeKind<'a>) {
        self.r#type.replace(Some(ty));
    }
}

impl<'a> Node<'a> for StructLiteral<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
        self.code.iter()
    }
}

impl fmt::Display for StructLiteral<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "StructLiteral({})", self.name())
    }
}

#[derive(Debug)]
pub struct ValueField<'a> {
    name: &'a Identifier<'a>,
    value: Option<&'a Expression<'a>>,
    code: Code<'a>,
    r#type: Cell<Option<TypeKind<'a>>>,
}

impl<'a> ValueField<'a> {
    pub fn new(
        name: &'a Identifier<'a>,
        value: Option<&'a Expression<'a>>,
        code: Code<'a>,
    ) -> Self {
        Self {
            name,
            value,
            code,
            r#type: Cell::default(),
        }
    }

    pub fn name(&self) -> &'a Identifier<'a> {
        self.name
    }

    pub fn value(&self) -> Option<&'a Expression<'a>> {
        self.value
    }

    pub fn r#type(&self) -> Option<TypeKind<'a>> {
        self.r#type.get()
    }

    pub fn assign_type(&self, ty: TypeKind<'a>) {
        self.r#type.replace(Some(ty));
    }
}

impl<'a> Node<'a> for ValueField<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
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
    code: Code<'a>,
    r#type: Cell<Option<TypeKind<'a>>>,
}

impl<'a> BinaryExpression<'a> {
    pub fn new(
        operator: BinaryOperator,
        lhs: &'a Expression<'a>,
        rhs: Option<&'a Expression<'a>>,
        code: Code<'a>,
    ) -> Self {
        Self {
            operator,
            lhs,
            rhs,
            code,
            r#type: Cell::default(),
        }
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

    pub fn r#type(&self) -> Option<TypeKind<'a>> {
        self.r#type.get()
    }

    pub fn assign_type(&self, ty: TypeKind<'a>) {
        self.r#type.replace(Some(ty));
    }
}

impl<'a> Node<'a> for BinaryExpression<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
        self.code.iter()
    }
}

impl fmt::Display for BinaryExpression<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "BinaryExpression({})", self.operator())
    }
}

#[derive(Debug)]
pub struct UnaryExpression<'a> {
    operator: UnaryOperator,
    operand: Option<&'a Expression<'a>>,
    code: Code<'a>,
    r#type: Cell<Option<TypeKind<'a>>>,
}

impl<'a> UnaryExpression<'a> {
    pub fn new(
        operator: UnaryOperator,
        operand: Option<&'a Expression<'a>>,
        code: Code<'a>,
    ) -> Self {
        Self {
            operator,
            operand,
            code,
            r#type: Cell::default(),
        }
    }

    pub fn operator(&self) -> UnaryOperator {
        self.operator
    }

    pub fn operand(&self) -> Option<&'a Expression<'a>> {
        self.operand
    }

    pub fn r#type(&self) -> Option<TypeKind<'a>> {
        self.r#type.get()
    }

    pub fn assign_type(&self, ty: TypeKind<'a>) {
        self.r#type.replace(Some(ty));
    }
}

impl<'a> Node<'a> for UnaryExpression<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
        self.code.iter()
    }
}

impl fmt::Display for UnaryExpression<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "UnaryExpression({})", self.operator())
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

impl fmt::Display for BinaryOperator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinaryOperator::Add => write!(f, "+"),
            BinaryOperator::Sub => write!(f, "-"),
            BinaryOperator::Mul => write!(f, "*"),
            BinaryOperator::Div => write!(f, "/"),
            BinaryOperator::Rem => write!(f, "%"),
            BinaryOperator::Lt => write!(f, "<"),
            BinaryOperator::Gt => write!(f, ">"),
            BinaryOperator::Le => write!(f, "<="),
            BinaryOperator::Ge => write!(f, ">="),
            BinaryOperator::Eq => write!(f, "=="),
            BinaryOperator::Ne => write!(f, "!="),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum UnaryOperator {
    Plus,
    Minus,
}

impl fmt::Display for UnaryOperator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnaryOperator::Plus => write!(f, "+"),
            UnaryOperator::Minus => write!(f, "-"),
        }
    }
}

#[derive(Debug)]
pub struct SubscriptExpression<'a> {
    callee: &'a Expression<'a>,
    arguments: BumpaloVec<'a, &'a Expression<'a>>,
    code: Code<'a>,
    r#type: Cell<Option<TypeKind<'a>>>,
}

impl<'a> SubscriptExpression<'a> {
    pub fn new<I: IntoIterator<Item = &'a Expression<'a>>>(
        arena: &'a BumpaloArena,
        callee: &'a Expression<'a>,
        arguments: I,
        code: Code<'a>,
    ) -> Self {
        Self {
            callee,
            arguments: BumpaloVec::from_iter_in(arguments, arena),
            code,
            r#type: Cell::default(),
        }
    }

    pub fn callee(&self) -> &'a Expression<'a> {
        self.callee
    }

    pub fn arguments(&self) -> impl ExactSizeIterator<Item = &'a Expression<'a>> + '_ {
        self.arguments.iter().copied()
    }

    pub fn r#type(&self) -> Option<TypeKind<'a>> {
        self.r#type.get()
    }

    pub fn assign_type(&self, ty: TypeKind<'a>) {
        self.r#type.replace(Some(ty));
    }
}

impl<'a> Node<'a> for SubscriptExpression<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
        self.code.iter()
    }
}

impl fmt::Display for SubscriptExpression<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SubscriptExpression({})", self.callee())
    }
}

#[derive(Debug)]
pub struct CallExpression<'a> {
    callee: &'a Expression<'a>,
    arguments: BumpaloVec<'a, &'a Expression<'a>>,
    code: Code<'a>,
    r#type: Cell<Option<TypeKind<'a>>>,
}

impl<'a> CallExpression<'a> {
    pub fn new<I: IntoIterator<Item = &'a Expression<'a>>>(
        arena: &'a BumpaloArena,
        callee: &'a Expression<'a>,
        arguments: I,
        code: Code<'a>,
    ) -> Self {
        Self {
            callee,
            arguments: BumpaloVec::from_iter_in(arguments, arena),
            code,
            r#type: Cell::default(),
        }
    }

    pub fn callee(&self) -> &'a Expression<'a> {
        self.callee
    }

    pub fn arguments(&self) -> impl ExactSizeIterator<Item = &'a Expression<'a>> + '_ {
        self.arguments.iter().copied()
    }

    pub fn r#type(&self) -> Option<TypeKind<'a>> {
        self.r#type.get()
    }

    pub fn assign_type(&self, ty: TypeKind<'a>) {
        self.r#type.replace(Some(ty));
    }
}

impl<'a> Node<'a> for CallExpression<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
        self.code.iter()
    }
}

impl fmt::Display for CallExpression<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CallExpression({})", self.callee())
    }
}

#[derive(Debug)]
pub struct MemberExpression<'a> {
    object: &'a Expression<'a>,
    field: Option<&'a Identifier<'a>>,
    code: Code<'a>,
    r#type: Cell<Option<TypeKind<'a>>>,
}

impl<'a> MemberExpression<'a> {
    pub fn new(
        object: &'a Expression<'a>,
        field: Option<&'a Identifier<'a>>,
        code: Code<'a>,
    ) -> Self {
        Self {
            object,
            field,
            code,
            r#type: Cell::default(),
        }
    }

    pub fn object(&self) -> &'a Expression<'a> {
        self.object
    }

    pub fn field(&self) -> Option<&'a Identifier<'a>> {
        self.field
    }

    pub fn r#type(&self) -> Option<TypeKind<'a>> {
        self.r#type.get()
    }

    pub fn assign_type(&self, ty: TypeKind<'a>) {
        self.r#type.replace(Some(ty));
    }
}

impl<'a> Node<'a> for MemberExpression<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
        self.code.iter()
    }
}

impl fmt::Display for MemberExpression<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "MemberExpression(.{})",
            self.field().map(&Identifier::as_str).unwrap_or("{unknown}")
        )
    }
}

#[derive(Debug)]
pub struct ArrayExpression<'a> {
    elements: BumpaloVec<'a, &'a Expression<'a>>,
    code: Code<'a>,
    r#type: Cell<Option<TypeKind<'a>>>,
}

impl<'a> ArrayExpression<'a> {
    pub fn new<I: IntoIterator<Item = &'a Expression<'a>>>(
        arena: &'a BumpaloArena,
        elements: I,
        code: Code<'a>,
    ) -> Self {
        Self {
            elements: BumpaloVec::from_iter_in(elements, arena),
            code,
            r#type: Cell::default(),
        }
    }

    pub fn elements(&self) -> impl ExactSizeIterator<Item = &'a Expression<'a>> + '_ {
        self.elements.iter().copied()
    }

    pub fn r#type(&self) -> Option<TypeKind<'a>> {
        self.r#type.get()
    }

    pub fn assign_type(&self, ty: TypeKind<'a>) {
        self.r#type.replace(Some(ty));
    }
}

impl<'a> Node<'a> for ArrayExpression<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
        self.code.iter()
    }
}

impl fmt::Display for ArrayExpression<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ArrayExpression({})", self.elements.len())
    }
}

#[derive(Debug)]
pub struct IfExpression<'a> {
    condition: Option<&'a Expression<'a>>,
    then_body: &'a Block<'a>,
    else_body: Option<&'a Block<'a>>,
    code: Code<'a>,
    r#type: Cell<Option<TypeKind<'a>>>,
}

impl<'a> IfExpression<'a> {
    pub fn new(
        condition: Option<&'a Expression<'a>>,
        then_body: &'a Block<'a>,
        else_body: Option<&'a Block<'a>>,
        code: Code<'a>,
    ) -> Self {
        Self {
            condition,
            then_body,
            else_body,
            code,
            r#type: Cell::default(),
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

    pub fn r#type(&self) -> Option<TypeKind<'a>> {
        self.r#type.get()
    }

    pub fn assign_type(&self, ty: TypeKind<'a>) {
        self.r#type.replace(Some(ty));
    }
}

impl<'a> Node<'a> for IfExpression<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
        self.code.iter()
    }
}

impl fmt::Display for IfExpression<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "IfExpression")
    }
}

#[derive(Debug)]
pub struct CaseExpression<'a> {
    head: Option<&'a Expression<'a>>,
    arms: BumpaloVec<'a, &'a CaseArm<'a>>,
    else_body: Option<&'a Block<'a>>,
    code: Code<'a>,
    r#type: Cell<Option<TypeKind<'a>>>,
}

impl<'a> CaseExpression<'a> {
    pub fn new<I: IntoIterator<Item = &'a CaseArm<'a>>>(
        arena: &'a BumpaloArena,
        head: Option<&'a Expression<'a>>,
        arms: I,
        else_body: Option<&'a Block<'a>>,
        code: Code<'a>,
    ) -> Self {
        Self {
            head,
            arms: BumpaloVec::from_iter_in(arms, arena),
            else_body,
            code,
            r#type: Cell::default(),
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

    pub fn r#type(&self) -> Option<TypeKind<'a>> {
        self.r#type.get()
    }

    pub fn assign_type(&self, ty: TypeKind<'a>) {
        self.r#type.replace(Some(ty));
    }
}

impl<'a> Node<'a> for CaseExpression<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
        self.code.iter()
    }
}

impl fmt::Display for CaseExpression<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CaseExpression")
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
    scope: &'a Scope<'a>,
    code: Code<'a>,
}

impl<'a> CaseArm<'a> {
    pub fn new(
        arena: &'a BumpaloArena,
        pattern: Option<&'a Pattern<'a>>,
        guard: Option<&'a Expression<'a>>,
        then_body: &'a Block<'a>,
        code: Code<'a>,
    ) -> Self {
        Self {
            pattern,
            guard,
            then_body,
            scope: arena.alloc(Scope::new(arena)),
            code,
        }
    }

    pub fn scope(&self) -> &'a Scope<'a> {
        self.scope
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
    fn code(&self) -> CodeKindIter<'_, 'a> {
        self.code.iter()
    }
}

impl fmt::Display for CaseArm<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CaseArm")
    }
}

#[derive(Debug)]
pub struct IntegerLiteral<'a> {
    value: i32,
    code: CodeKind<'a>,
}

impl<'a> IntegerLiteral<'a> {
    pub fn new(value: i32, token: Token) -> Self {
        let code = CodeKind::interpreted(token);
        Self { value, code }
    }

    pub fn value(&self) -> i32 {
        self.value
    }

    pub fn r#type(&self) -> TypeKind<'a> {
        TypeKind::Int32
    }
}

impl<'a> Node<'a> for IntegerLiteral<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
        CodeKindIter::from(&self.code)
    }
}

impl fmt::Display for IntegerLiteral<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "IntegerLiteral({})", self.value())
    }
}

#[derive(Debug)]
pub struct StringLiteral<'a> {
    value: Option<BumpaloString<'a>>,
    code: Code<'a>,
}

impl<'a> StringLiteral<'a> {
    pub fn new<S: AsRef<str>>(arena: &'a BumpaloArena, value: Option<S>, code: Code<'a>) -> Self {
        Self {
            value: value.map(|x| BumpaloString::from_str_in(x.as_ref(), arena)),
            code,
        }
    }

    pub fn value(&self) -> Option<&str> {
        self.value.as_deref()
    }

    pub fn r#type(&self) -> TypeKind<'a> {
        TypeKind::String
    }
}

impl<'a> Node<'a> for StringLiteral<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
        self.code.iter()
    }
}

impl fmt::Display for StringLiteral<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "StringLiteral({})",
            self.value().unwrap_or(&"-".to_string())
        )
    }
}

#[derive(Debug)]
pub struct VariableExpression<'a> {
    id: &'a Identifier<'a>,
    code: CodeKind<'a>,
    r#type: Cell<Option<TypeKind<'a>>>,
}

impl<'a> VariableExpression<'a> {
    pub fn new(id: &'a Identifier<'a>) -> Self {
        let code = CodeKind::Node(NodeKind::Identifier(id));
        Self {
            id,
            code,
            r#type: Cell::default(),
        }
    }

    pub fn id(&self) -> &'a Identifier<'a> {
        self.id
    }

    pub fn name(&self) -> &str {
        self.id.as_str()
    }

    pub fn r#type(&self) -> Option<TypeKind<'a>> {
        self.r#type.get()
    }

    pub fn assign_type(&self, ty: TypeKind<'a>) {
        self.r#type.replace(Some(ty));
    }
}

impl<'a> Node<'a> for VariableExpression<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
        CodeKindIter::from(&self.code)
    }
}

impl fmt::Display for VariableExpression<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "VariableExpression({})", self.id())
    }
}

#[derive(Debug)]
pub struct GroupedExpression<'a> {
    expression: Option<&'a Expression<'a>>,
    code: Code<'a>,
}

impl<'a> GroupedExpression<'a> {
    pub fn new(expression: Option<&'a Expression<'a>>, code: Code<'a>) -> Self {
        Self { expression, code }
    }

    pub fn expression(&self) -> Option<&'a Expression<'a>> {
        self.expression
    }

    pub fn r#type(&self) -> Option<TypeKind<'a>> {
        self.expression().and_then(|x| x.r#type())
    }
}

impl<'a> Node<'a> for GroupedExpression<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
        self.code.iter()
    }
}

impl fmt::Display for GroupedExpression<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(expression) = self.expression() {
            write!(f, "GroupedExpression({})", expression)
        } else {
            write!(f, "GroupedExpression")
        }
    }
}

#[derive(Debug)]
pub enum ExpressionKind<'a> {
    IntegerLiteral(&'a IntegerLiteral<'a>),
    StringLiteral(&'a StringLiteral<'a>),
    StructLiteral(&'a StructLiteral<'a>),
    VariableExpression(&'a VariableExpression<'a>),
    BinaryExpression(&'a BinaryExpression<'a>),
    UnaryExpression(&'a UnaryExpression<'a>),
    SubscriptExpression(&'a SubscriptExpression<'a>),
    CallExpression(&'a CallExpression<'a>),
    ArrayExpression(&'a ArrayExpression<'a>),
    MemberExpression(&'a MemberExpression<'a>),
    IfExpression(&'a IfExpression<'a>),
    CaseExpression(&'a CaseExpression<'a>),
    GroupedExpression(&'a GroupedExpression<'a>),
}

#[derive(Debug)]
pub struct Pattern<'a> {
    kind: PatternKind<'a>,
    code: CodeKind<'a>,
}

impl<'a> Pattern<'a> {
    pub fn new(kind: PatternKind<'a>) -> Self {
        let code = CodeKind::Node(NodeKind::from(&kind));
        Self { kind, code }
    }

    pub fn kind(&self) -> &PatternKind<'a> {
        &self.kind
    }
}

impl<'a> Node<'a> for Pattern<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
        CodeKindIter::from(&self.code)
    }
}

impl fmt::Display for Pattern<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Pattern")
    }
}

#[derive(Debug)]
pub struct VariablePattern<'a> {
    id: &'a Identifier<'a>,
    code: CodeKind<'a>,
    r#type: Cell<Option<TypeKind<'a>>>,
}

impl<'a> VariablePattern<'a> {
    pub fn new(id: &'a Identifier<'a>) -> Self {
        let code = CodeKind::Node(NodeKind::Identifier(id));
        Self {
            id,
            code,
            r#type: Cell::default(),
        }
    }

    pub fn id(&self) -> &'a Identifier<'a> {
        self.id
    }

    pub fn name(&self) -> &str {
        self.id.as_str()
    }

    pub fn r#type(&self) -> Option<TypeKind<'a>> {
        self.r#type.get()
    }

    pub fn assign_type(&self, ty: TypeKind<'a>) {
        self.r#type.replace(Some(ty));
    }
}

impl<'a> Node<'a> for VariablePattern<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
        CodeKindIter::from(&self.code)
    }
}

impl fmt::Display for VariablePattern<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "VariablePattern({})", self.id())
    }
}

#[derive(Debug)]
pub struct ArrayPattern<'a> {
    elements: BumpaloVec<'a, &'a Pattern<'a>>,
    code: Code<'a>,
    r#type: Cell<Option<TypeKind<'a>>>,
}

impl<'a> ArrayPattern<'a> {
    pub fn new<I: IntoIterator<Item = &'a Pattern<'a>>>(
        arena: &'a BumpaloArena,
        elements: I,
        code: Code<'a>,
    ) -> Self {
        Self {
            elements: BumpaloVec::from_iter_in(elements, arena),
            code,
            r#type: Cell::default(),
        }
    }

    pub fn elements(&self) -> impl ExactSizeIterator<Item = &'a Pattern<'a>> + '_ {
        self.elements.iter().copied()
    }

    pub fn r#type(&self) -> Option<TypeKind<'a>> {
        self.r#type.get()
    }

    pub fn assign_type(&self, ty: TypeKind<'a>) {
        self.r#type.replace(Some(ty));
    }
}

impl<'a> Node<'a> for ArrayPattern<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
        self.code.iter()
    }
}

impl fmt::Display for ArrayPattern<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ArrayPattern({})", self.elements.len())
    }
}

#[derive(Debug)]
pub struct RestPattern<'a> {
    variable_pattern: Option<&'a VariablePattern<'a>>,
    code: Code<'a>,
    r#type: Cell<Option<TypeKind<'a>>>,
}

impl<'a> RestPattern<'a> {
    pub fn new(variable_pattern: Option<&'a VariablePattern<'a>>, code: Code<'a>) -> Self {
        Self {
            variable_pattern,
            code,
            r#type: Cell::default(),
        }
    }

    pub fn variable_pattern(&self) -> Option<&'a VariablePattern<'a>> {
        self.variable_pattern
    }

    pub fn r#type(&self) -> Option<TypeKind<'a>> {
        self.r#type.get()
    }

    pub fn assign_type(&self, ty: TypeKind<'a>) {
        self.r#type.replace(Some(ty));
    }
}

impl<'a> Node<'a> for RestPattern<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
        self.code.iter()
    }
}

impl fmt::Display for RestPattern<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RestPattern")
    }
}

#[derive(Debug)]
pub struct StructPattern<'a> {
    name: &'a Identifier<'a>,
    fields: BumpaloVec<'a, &'a ValueFieldPattern<'a>>,
    code: Code<'a>,
    r#type: Cell<Option<TypeKind<'a>>>,
}

impl<'a> StructPattern<'a> {
    pub fn new<I: IntoIterator<Item = &'a ValueFieldPattern<'a>>>(
        arena: &'a BumpaloArena,
        name: &'a Identifier<'a>,
        fields: I,
        code: Code<'a>,
    ) -> Self {
        Self {
            name,
            fields: BumpaloVec::from_iter_in(fields, arena),
            code,
            r#type: Cell::default(),
        }
    }

    pub fn name(&self) -> &'a Identifier<'a> {
        self.name
    }

    pub fn fields(&self) -> impl ExactSizeIterator<Item = &'a ValueFieldPattern<'a>> + '_ {
        self.fields.iter().copied()
    }

    pub fn r#type(&self) -> Option<TypeKind<'a>> {
        self.r#type.get()
    }

    pub fn assign_type(&self, ty: TypeKind<'a>) {
        self.r#type.replace(Some(ty));
    }
}

impl<'a> Node<'a> for StructPattern<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
        self.code.iter()
    }
}

impl fmt::Display for StructPattern<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "StructPattern({})", self.name())
    }
}

#[derive(Debug)]
pub struct ValueFieldPattern<'a> {
    name: &'a Identifier<'a>,
    value: Option<&'a Pattern<'a>>,
    omitted_value: Option<&'a Pattern<'a>>,
    code: Code<'a>,
    r#type: Cell<Option<TypeKind<'a>>>,
}

impl<'a> ValueFieldPattern<'a> {
    pub fn new(
        arena: &'a BumpaloArena,
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
                r#type: Cell::default(),
            }
        } else {
            let expr = arena.alloc(VariablePattern::new(name));
            let kind = PatternKind::VariablePattern(expr);
            let omitted_value = arena.alloc(Pattern::new(kind));

            Self {
                name,
                value,
                omitted_value: Some(omitted_value),
                code,
                r#type: Cell::default(),
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

    pub fn r#type(&self) -> Option<TypeKind<'a>> {
        self.r#type.get()
    }

    pub fn assign_type(&self, ty: TypeKind<'a>) {
        self.r#type.replace(Some(ty));
    }
}

impl<'a> Node<'a> for ValueFieldPattern<'a> {
    fn code(&self) -> CodeKindIter<'_, 'a> {
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
    IntegerPattern(&'a IntegerLiteral<'a>),
    StringPattern(&'a StringLiteral<'a>),
    VariablePattern(&'a VariablePattern<'a>),
    ArrayPattern(&'a ArrayPattern<'a>),
    RestPattern(&'a RestPattern<'a>),
    StructPattern(&'a StructPattern<'a>),
    ValueFieldPattern(&'a ValueFieldPattern<'a>),
}

impl<'a> PatternKind<'a> {
    pub fn r#type(&self) -> Option<TypeKind<'a>> {
        match self {
            PatternKind::IntegerPattern(pat) => Some(pat.r#type()),
            PatternKind::StringPattern(pat) => Some(pat.r#type()),
            PatternKind::VariablePattern(pat) => pat.r#type(),
            PatternKind::ArrayPattern(pat) => pat.r#type(),
            PatternKind::RestPattern(pat) => pat.r#type(),
            PatternKind::StructPattern(pat) => pat.r#type(),
            PatternKind::ValueFieldPattern(pat) => pat.r#type(),
        }
    }
}

impl fmt::Display for NodeKind<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NodeKind::Program(program) => program.fmt(f),
            NodeKind::TopLevel(kind) => kind.fmt(f),
            NodeKind::Block(block) => block.fmt(f),
            NodeKind::Identifier(id) => id.fmt(f),
            NodeKind::StructDefinition(definition) => definition.fmt(f),
            NodeKind::FunctionDefinition(definition) => definition.fmt(f),
            NodeKind::TypeField(field) => field.fmt(f),
            NodeKind::TypeAnnotation(ty) => ty.fmt(f),
            NodeKind::ValueField(field) => field.fmt(f),
            NodeKind::FunctionParameter(param) => param.fmt(f),
            NodeKind::Statement(stmt) => stmt.fmt(f),
            NodeKind::VariableDeclaration(declaration) => declaration.fmt(f),
            NodeKind::Expression(expr) => expr.fmt(f),
            NodeKind::IntegerLiteral(expr) => expr.fmt(f),
            NodeKind::StringLiteral(expr) => expr.fmt(f),
            NodeKind::StructLiteral(expr) => expr.fmt(f),
            NodeKind::VariableExpression(expr) => expr.fmt(f),
            NodeKind::BinaryExpression(expr) => expr.fmt(f),
            NodeKind::UnaryExpression(expr) => expr.fmt(f),
            NodeKind::SubscriptExpression(expr) => expr.fmt(f),
            NodeKind::CallExpression(expr) => expr.fmt(f),
            NodeKind::ArrayExpression(expr) => expr.fmt(f),
            NodeKind::MemberExpression(expr) => expr.fmt(f),
            NodeKind::IfExpression(expr) => expr.fmt(f),
            NodeKind::CaseExpression(expr) => expr.fmt(f),
            NodeKind::CaseArm(arm) => arm.fmt(f),
            NodeKind::Pattern(pattern) => pattern.fmt(f),
            NodeKind::VariablePattern(pattern) => pattern.fmt(f),
            NodeKind::ArrayPattern(pattern) => pattern.fmt(f),
            NodeKind::RestPattern(pattern) => pattern.fmt(f),
            NodeKind::StructPattern(pattern) => pattern.fmt(f),
            NodeKind::ValueFieldPattern(pattern) => pattern.fmt(f),
            NodeKind::GroupedExpression(expr) => expr.fmt(f),
        }
    }
}

impl fmt::Display for ExpressionKind<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExpressionKind::IntegerLiteral(expr) => expr.fmt(f),
            ExpressionKind::StringLiteral(expr) => expr.fmt(f),
            ExpressionKind::VariableExpression(expr) => expr.fmt(f),
            ExpressionKind::BinaryExpression(expr) => expr.fmt(f),
            ExpressionKind::UnaryExpression(expr) => expr.fmt(f),
            ExpressionKind::SubscriptExpression(expr) => expr.fmt(f),
            ExpressionKind::CallExpression(expr) => expr.fmt(f),
            ExpressionKind::ArrayExpression(expr) => expr.fmt(f),
            ExpressionKind::IfExpression(expr) => expr.fmt(f),
            ExpressionKind::CaseExpression(expr) => expr.fmt(f),
            ExpressionKind::MemberExpression(expr) => expr.fmt(f),
            ExpressionKind::StructLiteral(expr) => expr.fmt(f),
            ExpressionKind::GroupedExpression(expr) => expr.fmt(f),
        }
    }
}
