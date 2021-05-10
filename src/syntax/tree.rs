use super::{EffectiveRange, MissingTokenKind, Scope, SyntaxToken, Token};
use crate::{sem, util::wrap};
use id_arena;
use std::rc::Rc;
use std::slice;
use std::{cell::RefCell, fmt};

pub type NodeArena = id_arena::Arena<NodeKind>;

pub type NodeId = id_arena::Id<NodeKind>;

pub struct AST {
    arena: NodeArena,
    root: NodeId,
}

impl AST {
    pub fn new(arena: NodeArena, root: NodeId) -> Self {
        Self { arena, root }
    }

    // get NodeKind
    pub fn get(&self, node: NodeId) -> Option<&NodeKind> {
        self.arena.get(node)
    }

    pub fn get_mut(&mut self, node: NodeId) -> Option<&mut NodeKind> {
        self.arena.get_mut(node)
    }

    // root
    pub fn root(&self) -> &Program {
        self.get(self.root)
            .unwrap_or_else(|| panic!("root node doesn't exist"))
            .program()
            .unwrap_or_else(|| panic!("root must be a program node."))
    }

    pub fn root_mut(&mut self) -> &mut Program {
        self.get(self.root)
            .unwrap_or_else(|| panic!("root node doesn't exist"))
            .program_mut()
            .unwrap_or_else(|| panic!("root must be a program node."))
    }
}

pub trait Node: fmt::Display {
    fn code(&self) -> slice::Iter<CodeKind>;

    /// Returns the effective range of this node.
    fn range(&self, tree: &AST) -> EffectiveRange {
        let mut it = self.code();

        // node must be at least one token.
        let init = it.next().unwrap();
        it.fold(init.range(tree), |acc, kind| kind.range(tree).union(&acc))
    }
}

#[derive(Debug)]
pub enum NodeKind {
    Program(Program),
    Block(Block),
    Identifier(Identifier),
    StructDefinition(StructDefinition),
    FunctionDefinition(FunctionDefinition),
    FunctionParameter(FunctionParameter),
    TypeField(TypeField),
    TypeAnnotation(TypeAnnotation),
    ValueField(ValueField),
    ValueFieldPattern(ValueFieldPattern),
    Statement(Statement),
    VariableDeclaration(VariableDeclaration),
    Expression(Expression),
    CaseArm(CaseArm),
    Pattern(Pattern),
}

impl NodeKind {
    pub fn program(&self) -> Option<&Program> {
        if let NodeKind::Program(program) = self {
            Some(program)
        } else {
            None
        }
    }

    pub fn program_mut(&mut self) -> Option<&mut Program> {
        if let NodeKind::Program(program) = self {
            Some(program)
        } else {
            None
        }
    }

    pub fn struct_definition(&self) -> Option<&StructDefinition> {
        if let NodeKind::StructDefinition(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn function_definition(&self) -> Option<&FunctionDefinition> {
        if let NodeKind::FunctionDefinition(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn function_parameter(&self) -> Option<&FunctionParameter> {
        if let NodeKind::FunctionParameter(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn variable_declaration(&self) -> Option<&VariableDeclaration> {
        if let NodeKind::VariableDeclaration(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn block(&self) -> Option<&Block> {
        if let NodeKind::Block(block) = self {
            Some(block)
        } else {
            None
        }
    }

    pub fn identifier(&self) -> Option<&Identifier> {
        if let NodeKind::Identifier(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn type_field(&self) -> Option<&TypeField> {
        if let NodeKind::TypeField(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn type_annotation(&self) -> Option<&TypeAnnotation> {
        if let NodeKind::TypeAnnotation(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn case_arm(&self) -> Option<&CaseArm> {
        if let NodeKind::CaseArm(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn pattern(&self) -> Option<&Pattern> {
        if let NodeKind::Pattern(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn value_field(&self) -> Option<&ValueField> {
        if let NodeKind::ValueField(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn value_field_pattern(&self) -> Option<&ValueFieldPattern> {
        if let NodeKind::ValueFieldPattern(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn statement(&self) -> Option<&Statement> {
        if let NodeKind::Statement(stmt) = self {
            Some(stmt)
        } else {
            None
        }
    }

    pub fn expression(&self) -> Option<&Expression> {
        if let NodeKind::Expression(node) = self {
            Some(node)
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

    pub fn variable_expression<'a>(&self, tree: &'a AST) -> Option<&'a Identifier> {
        if let NodeKind::Expression(node) = self {
            return node.variable_expression(tree);
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

    pub fn is_variable_expression<'a>(&self, tree: &'a AST) -> bool {
        self.variable_expression(tree).is_some()
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

/// `Builtin` is where a binding to "built-in" primitives/functions are defined.
/// It's not a part of an AST, so it doesn't have tokens.
#[derive(Debug, Clone)]
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
pub enum DefinitionKind {
    // Builtin functions, variables
    Builtin(Builtin),
    // Declaration node
    Node(NodeId),
}

impl DefinitionKind {
    pub fn builtin(&self) -> Option<&Builtin> {
        if let DefinitionKind::Builtin(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn struct_definition<'a>(&self, tree: &'a AST) -> Option<&'a StructDefinition> {
        if let DefinitionKind::Node(node) = self {
            if let Some(kind) = tree.get(*node) {
                if let NodeKind::StructDefinition(definition) = kind {
                    return Some(definition);
                }
            }
        }

        None
    }

    pub fn function_definition<'a>(&self, tree: &'a AST) -> Option<&'a FunctionDefinition> {
        if let DefinitionKind::Node(node_id) = self {
            if let Some(kind) = tree.get(*node_id) {
                if let NodeKind::FunctionDefinition(node) = kind {
                    return Some(node);
                }
            }
        }

        None
    }

    pub fn function_parameter<'a>(&self, tree: &'a AST) -> Option<&'a FunctionParameter> {
        if let DefinitionKind::Node(node_id) = self {
            if let Some(kind) = tree.get(*node_id) {
                if let NodeKind::FunctionParameter(node) = kind {
                    return Some(node);
                }
            }
        }

        None
    }

    pub fn pattern<'a>(&self, tree: &'a AST) -> Option<&'a Pattern> {
        if let DefinitionKind::Node(node_id) = self {
            if let Some(kind) = tree.get(*node_id) {
                if let NodeKind::Pattern(node) = kind {
                    return Some(node);
                }
            }
        }

        None
    }

    pub fn is_builtin(&self) -> bool {
        matches!(self, Self::Builtin(..))
    }

    pub fn is_struct_definition(&self, tree: &AST) -> bool {
        self.struct_definition(tree).is_some()
    }

    pub fn is_function_definition(&self, tree: &AST) -> bool {
        self.function_definition(tree).is_some()
    }

    pub fn is_function_parameter(&self, tree: &AST) -> bool {
        self.function_parameter(tree).is_some()
    }

    pub fn is_pattern(&self, tree: &AST) -> bool {
        self.pattern(tree).is_some()
    }

    pub fn ptr_eq(&self, other: &DefinitionKind) -> bool {
        if let DefinitionKind::Builtin(ref definition1) = self {
            if let DefinitionKind::Builtin(definition2) = other {
                return std::ptr::eq(definition1, definition2);
            }
        }

        if let DefinitionKind::Node(node_id1) = self {
            if let DefinitionKind::Node(node_id2) = other {
                return node_id1 == node_id2;
            }
        }

        false
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

    pub fn with_node(node: NodeId) -> Self {
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
    pub fn node(&mut self, node: NodeId) -> &mut Self {
        self.code.push(CodeKind::Node(node));
        self
    }
}

#[derive(Debug)]
pub enum CodeKind {
    Node(NodeId),
    SyntaxToken(SyntaxToken),
}

impl CodeKind {
    pub fn range(&self, tree: &AST) -> EffectiveRange {
        match self {
            CodeKind::Node(node_id) => tree.get(*node_id).unwrap().range(tree),
            CodeKind::SyntaxToken(token) => token.range(),
        }
    }
}

#[derive(Debug)]
pub struct Program {
    pub body: Vec<NodeId>,
    declarations: Rc<RefCell<Scope>>,
    main_scope: Rc<RefCell<Scope>>,
    code: Code,
}

impl Program {
    pub fn new(body: Vec<NodeId>, code: Code) -> Self {
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
    pub name: Option<NodeId>,
    pub fields: Vec<NodeId>,
    r#type: Rc<RefCell<sem::Type>>,
    code: Code,
}

impl StructDefinition {
    pub fn new(name: Option<NodeId>, fields: Vec<NodeId>, code: Code) -> Self {
        Self {
            name,
            fields,
            code,
            r#type: wrap(sem::Type::Unknown),
        }
    }

    pub fn name<'a>(&self, tree: &'a AST) -> Option<&'a Identifier> {
        if let Some(name) = self.name {
            return tree.get(name).unwrap().identifier();
        }

        None
    }

    pub fn fields<'a>(&'a self, tree: &'a AST) -> impl Iterator<Item = &'a TypeField> + 'a {
        self.fields
            .iter()
            .map(move |node_id| tree.get(*node_id).unwrap().type_field().unwrap())
    }

    pub fn r#type(&self) -> &Rc<RefCell<sem::Type>> {
        &self.r#type
    }

    pub fn get_field_type<'a>(&self, tree: &'a AST, name: &str) -> Option<Rc<RefCell<sem::Type>>> {
        self.fields(tree)
            .find(|f| {
                f.name(tree)
                    .map_or(false, |field_name| field_name.as_str() == name)
            })
            .and_then(|f| f.type_annotation(tree))
            .map(|annotation| Rc::clone(&annotation.r#type))
    }
}

impl Node for StructDefinition {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.iter()
    }
}

impl fmt::Display for StructDefinition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "StructDefinition")
    }
}

#[derive(Debug)]
pub struct TypeField {
    pub name: Option<NodeId>,
    pub type_annotation: Option<NodeId>,
    code: Code,
}

impl TypeField {
    pub fn new(name: Option<NodeId>, type_annotation: Option<NodeId>, code: Code) -> Self {
        Self {
            name,
            type_annotation,
            code,
        }
    }

    pub fn name<'a>(&self, tree: &'a AST) -> Option<&'a Identifier> {
        if let Some(name) = self.name {
            return tree.get(name).unwrap().identifier();
        }

        None
    }

    pub fn type_annotation<'a>(&self, tree: &'a AST) -> Option<&'a TypeAnnotation> {
        if let Some(node_id) = self.type_annotation {
            return tree.get(node_id).unwrap().type_annotation();
        }

        None
    }
}

impl Node for TypeField {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.iter()
    }
}

impl fmt::Display for TypeField {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TypeField")
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
    pub name: Option<NodeId>,
    pub parameters: Vec<NodeId>,
    pub body: NodeId,
    code: Code,
}

impl FunctionDefinition {
    pub fn new(name: Option<NodeId>, parameters: Vec<NodeId>, body: NodeId, code: Code) -> Self {
        Self {
            name,
            parameters,
            body,
            code,
        }
    }

    pub fn name<'a>(&self, tree: &'a AST) -> Option<&'a Identifier> {
        if let Some(node_id) = self.name {
            return tree.get(node_id).unwrap().identifier();
        }

        None
    }

    pub fn body<'a>(&self, tree: &'a AST) -> &'a Block {
        return tree.get(self.body).unwrap().block().unwrap();
    }

    pub fn parameters(&self) -> slice::Iter<NodeId> {
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
        write!(f, "FunctionDefinition")
    }
}

#[derive(Debug)]
pub struct FunctionParameter {
    pub name: NodeId,
    code: Code,
}

impl FunctionParameter {
    pub fn new(name: NodeId, code: Code) -> Self {
        Self { name, code }
    }

    pub fn name<'a>(&self, tree: &'a AST) -> &'a Identifier {
        return tree.get(self.name).unwrap().identifier().unwrap();
    }
}

impl Node for FunctionParameter {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.iter()
    }
}

impl fmt::Display for FunctionParameter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FunctionParameter")
    }
}

#[derive(Debug)]
pub struct VariableDeclaration {
    pub pattern: Option<NodeId>,
    pub init: Option<NodeId>,
    code: Code,
}

impl VariableDeclaration {
    pub fn new(pattern: Option<NodeId>, init: Option<NodeId>, code: Code) -> Self {
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
    Expression(NodeId),
    VariableDeclaration(NodeId),
}

impl Statement {
    pub fn new(kind: StatementKind, code: Code) -> Self {
        Self { kind, code }
    }

    pub fn expression<'a>(&self, tree: &'a AST) -> Option<&'a Expression> {
        if let StatementKind::Expression(node_id) = self.kind {
            return tree.get(node_id).unwrap().expression();
        } else {
            None
        }
    }

    pub fn variable_declaration<'a>(&self, tree: &'a AST) -> Option<&'a VariableDeclaration> {
        if let StatementKind::Expression(node_id) = self.kind {
            return tree.get(node_id).unwrap().variable_declaration();
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
    statements: Vec<NodeId>,
    scope: Rc<RefCell<Scope>>,
    code: Code,
}

impl Block {
    pub fn new(statements: Vec<NodeId>, code: Code) -> Self {
        Self {
            statements,
            scope: wrap(Scope::new()),
            code,
        }
    }

    pub fn scope(&self) -> &Rc<RefCell<Scope>> {
        &self.scope
    }

    pub fn statements<'a>(&'a self, tree: &'a AST) -> Statements {
        Statements::new(tree, self.statements.iter())
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
    pub fn new(kind: ExpressionKind, code: Code) -> Self {
        Self {
            kind,
            code,
            r#type: wrap(sem::Type::Unknown),
        }
    }

    pub fn kind(&self) -> &ExpressionKind {
        &self.kind
    }

    pub fn r#type(&self) -> &Rc<RefCell<sem::Type>> {
        &self.r#type
    }

    pub fn replace_type(&mut self, ty: &Rc<RefCell<sem::Type>>) {
        self.r#type = Rc::clone(ty);
    }

    pub fn struct_literal(&self) -> Option<&StructLiteral> {
        if let ExpressionKind::StructLiteral(ref expr) = self.kind {
            Some(expr)
        } else {
            None
        }
    }

    pub fn variable_expression<'a>(&self, tree: &'a AST) -> Option<&'a Identifier> {
        if let ExpressionKind::VariableExpression(node_id) = self.kind {
            tree.get(node_id).unwrap().identifier()
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
    pub name: NodeId,
    pub fields: Vec<NodeId>,
}

impl StructLiteral {
    pub fn new(name: NodeId, fields: Vec<NodeId>) -> Self {
        Self { name, fields }
    }

    pub fn name(&self) -> NodeId {
        self.name
    }
}

#[derive(Debug)]
pub struct ValueField {
    pub name: NodeId,
    pub value: Option<NodeId>,
    pub code: Code,
}

impl ValueField {
    pub fn new(name: NodeId, value: Option<NodeId>, code: Code) -> Self {
        Self { name, value, code }
    }

    pub fn name(&self) -> NodeId {
        self.name
    }
}

impl Node for ValueField {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.iter()
    }
}

impl fmt::Display for ValueField {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ValueField")
    }
}

#[derive(Debug)]
pub struct BinaryExpression {
    pub operator: BinaryOperator,
    pub lhs: NodeId,
    pub rhs: Option<NodeId>,
}

impl BinaryExpression {
    pub fn new(operator: BinaryOperator, lhs: NodeId, rhs: Option<NodeId>) -> Self {
        Self { operator, lhs, rhs }
    }

    pub fn lhs<'a>(&self, tree: &'a AST) -> &'a Expression {
        tree.get(self.lhs).unwrap().expression().unwrap()
    }

    pub fn rhs<'a>(&self, tree: &'a AST) -> Option<&'a Expression> {
        if let Some(node_id) = self.rhs {
            Some(tree.get(node_id).unwrap().expression().unwrap())
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub struct UnaryExpression {
    pub operator: UnaryOperator,
    pub operand: Option<NodeId>,
}

impl UnaryExpression {
    pub fn new(operator: UnaryOperator, operand: Option<NodeId>) -> Self {
        Self { operator, operand }
    }

    pub fn operand<'a>(&self, tree: &'a AST) -> Option<&'a Expression> {
        if let Some(node_id) = self.operand {
            Some(tree.get(node_id).unwrap().expression().unwrap())
        } else {
            None
        }
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
    pub callee: NodeId,
    pub arguments: Vec<NodeId>,
}

impl SubscriptExpression {
    pub fn new(callee: NodeId, arguments: Vec<NodeId>) -> Self {
        Self { callee, arguments }
    }

    pub fn callee<'a>(&self, tree: &'a AST) -> &'a Expression {
        tree.get(self.callee).unwrap().expression().unwrap()
    }

    pub fn arguments<'a>(&'a self, tree: &'a AST) -> Expressions<'a> {
        Expressions::new(tree, self.arguments.iter())
    }
}

#[derive(Debug)]
pub struct CallExpression {
    pub callee: NodeId,
    pub arguments: Vec<NodeId>,
}

impl CallExpression {
    pub fn new(callee: NodeId, arguments: Vec<NodeId>) -> Self {
        Self { callee, arguments }
    }

    pub fn callee(&self) -> NodeId {
        self.callee
    }

    pub fn arguments<'a>(&'a self, tree: &'a AST) -> Expressions<'a> {
        Expressions::new(tree, self.arguments.iter())
    }
}

#[derive(Debug)]
pub struct MemberExpression {
    pub object: NodeId,
    pub field: Option<NodeId>,
}

impl MemberExpression {
    pub fn new(object: NodeId, field: Option<NodeId>) -> Self {
        Self { object, field }
    }
}

#[derive(Debug)]
pub struct ArrayExpression {
    pub elements: Vec<NodeId>,
}

impl ArrayExpression {
    pub fn new(elements: Vec<NodeId>) -> Self {
        Self { elements }
    }

    pub fn elements<'a>(&'a self, tree: &'a AST) -> Expressions<'a> {
        Expressions::new(tree, self.elements.iter())
    }
}

#[derive(Debug)]
pub struct IfExpression {
    pub condition: Option<NodeId>, // Expression
    pub then_body: NodeId,         // Block
    pub else_body: Option<NodeId>, // Block
}

impl IfExpression {
    pub fn new(condition: Option<NodeId>, then_body: NodeId, else_body: Option<NodeId>) -> Self {
        Self {
            condition,
            then_body,
            else_body,
        }
    }

    pub fn condition<'a>(&self, tree: &'a AST) -> Option<&'a Expression> {
        if let Some(node_id) = self.condition {
            return tree.get(node_id).unwrap().expression();
        } else {
            None
        }
    }

    pub fn then_body<'a>(&self, tree: &'a AST) -> &'a Block {
        tree.get(self.then_body).unwrap().block().unwrap()
    }

    pub fn else_body<'a>(&self, tree: &'a AST) -> Option<&'a Block> {
        if let Some(node_id) = self.else_body {
            return tree.get(node_id).unwrap().block();
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub struct CaseExpression {
    pub head: Option<NodeId>,      // Expression
    pub arms: Vec<NodeId>,         // CaseArm
    pub else_body: Option<NodeId>, // Block
}

impl CaseExpression {
    pub fn new(head: Option<NodeId>, arms: Vec<NodeId>, else_body: Option<NodeId>) -> Self {
        Self {
            head,
            arms,
            else_body,
        }
    }

    pub fn head<'a>(&self, tree: &'a AST) -> Option<&'a Expression> {
        if let Some(node_id) = self.head {
            return tree.get(node_id).unwrap().expression();
        } else {
            None
        }
    }

    pub fn arms<'a>(&'a self, tree: &'a AST) -> CaseArms<'a> {
        CaseArms::new(tree, self.arms.iter())
    }

    pub fn else_body<'a>(&self, tree: &'a AST) -> Option<&'a Block> {
        if let Some(node_id) = self.else_body {
            return tree.get(node_id).unwrap().block();
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub struct CaseArm {
    pub pattern: Option<NodeId>, // Pattern
    pub guard: Option<NodeId>,   // Expression
    pub then_body: NodeId,       // Block

    // `CaseArm` is the only syntactic element other than Program and Block that introduces
    // a new scope. This scope is necessary to use the variables introduced in each arm in
    // the guard clause.
    scope: Rc<RefCell<Scope>>,
    code: Code,
}

impl CaseArm {
    pub fn new(
        pattern: Option<NodeId>,
        guard: Option<NodeId>,
        then_body: NodeId,
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

    pub fn pattern<'a>(&self, tree: &'a AST) -> Option<&'a Pattern> {
        if let Some(node_id) = self.pattern {
            return tree.get(node_id).unwrap().pattern();
        } else {
            None
        }
    }

    pub fn guard<'a>(&self, tree: &'a AST) -> Option<&'a Expression> {
        if let Some(node_id) = self.pattern {
            return tree.get(node_id).unwrap().expression();
        } else {
            None
        }
    }

    pub fn then_body<'a>(&self, tree: &'a AST) -> &'a Block {
        tree.get(self.then_body).unwrap().block().unwrap()
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
    VariableExpression(NodeId),
    BinaryExpression(BinaryExpression),
    UnaryExpression(UnaryExpression),
    SubscriptExpression(SubscriptExpression),
    CallExpression(CallExpression),
    ArrayExpression(ArrayExpression),
    MemberExpression(MemberExpression),
    IfExpression(IfExpression),
    CaseExpression(CaseExpression),
    Expression(Option<NodeId>),
}

#[derive(Debug)]
pub struct Pattern {
    kind: PatternKind,
    code: Code,
}

impl Pattern {
    pub fn new(kind: PatternKind, code: Code) -> Self {
        Self { kind, code }
    }

    pub fn kind(&self) -> &PatternKind {
        &self.kind
    }

    pub fn variable_pattern(identifier: NodeId) -> Self {
        Self {
            kind: PatternKind::VariablePattern(identifier),
            code: Code::with_node(identifier),
        }
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
    elements: Vec<NodeId>,
}

impl ArrayPattern {
    pub fn new(elements: Vec<NodeId>) -> Self {
        Self { elements }
    }

    pub fn elements(&self) -> slice::Iter<NodeId> {
        self.elements.iter()
    }
}

#[derive(Debug)]
pub struct RestPattern {
    pub id: Option<NodeId>,
}

impl RestPattern {
    pub fn new(id: Option<NodeId>) -> Self {
        Self { id }
    }
}

#[derive(Debug)]
pub struct StructPattern {
    pub name: NodeId,
    fields: Vec<NodeId>,
}

impl StructPattern {
    pub fn new(name: NodeId, fields: Vec<NodeId>) -> Self {
        Self { name, fields }
    }

    pub fn fields(&self) -> slice::Iter<NodeId> {
        self.fields.iter()
    }
}

#[derive(Debug)]
pub struct ValueFieldPattern {
    pub name: NodeId,
    pub value: Option<NodeId>,
    pub code: Code,
}

impl ValueFieldPattern {
    pub fn new(name: NodeId, value: Option<NodeId>, code: Code) -> Self {
        Self { name, value, code }
    }
}

impl Node for ValueFieldPattern {
    fn code(&self) -> slice::Iter<CodeKind> {
        self.code.iter()
    }
}

impl fmt::Display for ValueFieldPattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ValueFieldPattern")
    }
}

#[derive(Debug)]
pub enum PatternKind {
    IntegerPattern(i32),
    StringPattern(Option<String>),
    VariablePattern(NodeId),
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

impl fmt::Display for ExpressionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExpressionKind::IntegerLiteral(i) => write!(f, "IntegerLiteral({})", i),
            ExpressionKind::StringLiteral(s) => {
                write!(f, "StringLiteral({})", s.unwrap_or("-".to_string()))
            }
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
            ExpressionKind::Expression(Some(_)) => write!(f, "(Expression)"),
            ExpressionKind::Expression(None) => write!(f, "()"),
        }
    }
}
// Iterators
pub struct Expressions<'a> {
    tree: &'a AST,
    nodes: slice::Iter<'a, NodeId>,
}

impl<'a> Expressions<'a> {
    fn new(tree: &'a AST, nodes: slice::Iter<'a, NodeId>) -> Self {
        Self { tree, nodes }
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.len() == 0
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }
}

impl<'a> Iterator for Expressions<'a> {
    type Item = &'a Expression;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(node_id) = self.nodes.next() {
            let kind = self.tree.get(*node_id).unwrap();
            return Some(kind.expression().unwrap());
        }

        None
    }
}

pub struct Statements<'a> {
    tree: &'a AST,
    nodes: slice::Iter<'a, NodeId>,
}

impl<'a> Statements<'a> {
    fn new(tree: &'a AST, nodes: slice::Iter<'a, NodeId>) -> Self {
        Self { tree, nodes }
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.len() == 0
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }
}

impl<'a> Iterator for Statements<'a> {
    type Item = &'a Statement;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(node_id) = self.nodes.next() {
            let kind = self.tree.get(*node_id).unwrap();
            return Some(kind.statement().unwrap());
        }

        None
    }
}

pub struct CaseArms<'a> {
    tree: &'a AST,
    nodes: slice::Iter<'a, NodeId>,
}

impl<'a> CaseArms<'a> {
    fn new(tree: &'a AST, nodes: slice::Iter<'a, NodeId>) -> Self {
        Self { tree, nodes }
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.len() == 0
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }
}

impl<'a> Iterator for CaseArms<'a> {
    type Item = &'a CaseArm;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(node_id) = self.nodes.next() {
            let kind = self.tree.get(*node_id).unwrap();
            return Some(kind.case_arm().unwrap());
        }

        None
    }
}
