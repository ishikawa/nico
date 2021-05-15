use super::{EffectiveRange, MissingTokenKind, Scope, SyntaxToken, Trivia, TriviaKind};
use crate::syntax::Token;
use crate::{syntax::tree::*, util::wrap};
use std::{
    cell::RefCell,
    rc::{Rc, Weak},
};

#[derive(Debug, Clone)]
pub struct NodePath {
    skipped: bool,
    stopped: bool,
    node_id: NodeId,
    scope: Weak<RefCell<Scope>>,
    main_scope: Weak<RefCell<Scope>>,
    declarations: Weak<RefCell<Scope>>,
    parent: Option<Rc<RefCell<NodePath>>>,
}

impl<'a> NodePath {
    pub fn new(node_id: NodeId) -> Self {
        Self {
            skipped: false,
            stopped: false,
            node_id,
            parent: None,
            declarations: Weak::new(),
            scope: Weak::new(),
            main_scope: Weak::new(),
        }
    }

    pub fn child_path(node_id: NodeId, parent: &Rc<RefCell<NodePath>>) -> Self {
        let borrowed_parent = parent.borrow();

        Self {
            skipped: false,
            stopped: false,
            node_id,
            parent: Some(Rc::clone(parent)),
            scope: Weak::clone(&borrowed_parent.scope),
            main_scope: Weak::clone(&borrowed_parent.main_scope),
            declarations: Weak::clone(&borrowed_parent.declarations),
        }
    }

    pub fn node_id(&self) -> NodeId {
        self.node_id
    }

    pub fn node(&self, tree: &'a AST) -> &'a NodeKind {
        tree.get(self.node_id).unwrap()
    }

    /// Returns `true` if `skip()` or `stop()` invoked.
    fn skipped(&self) -> bool {
        self.skipped || self.stopped
    }

    /// skips traversing the children and `exit` of the current path.
    pub fn skip(&mut self) {
        self.skipped = true;
    }

    /// stops traversing entirely.
    pub fn stop(&mut self) {
        self.stopped = true;
    }

    pub fn parent(&self) -> Option<Rc<RefCell<NodePath>>> {
        self.parent.as_ref().map(Rc::clone)
    }

    pub fn expect_parent(&self) -> Rc<RefCell<NodePath>> {
        self.parent()
            .unwrap_or_else(|| panic!("parent must exist."))
    }

    pub fn scope(&self) -> Rc<RefCell<Scope>> {
        self.scope
            .upgrade()
            .unwrap_or_else(|| panic!("scope must live."))
    }

    fn on_enter(&mut self, tree: &'a AST) {
        match self.node(tree) {
            NodeKind::Program(ref program) => {
                self.main_scope = Rc::downgrade(program.main_scope());
                self.declarations = Rc::downgrade(program.declarations_scope());
                self.scope = Rc::downgrade(program.main_scope());
            }
            NodeKind::Block(ref block) => {
                self.scope = Rc::downgrade(block.scope());
            }
            NodeKind::CaseArm(ref arm) => {
                self.scope = Rc::downgrade(arm.scope());
            }
            NodeKind::Identifier(_) => {}
            NodeKind::StructDefinition(_) => {
                self.scope = Weak::clone(&self.declarations);
            }
            NodeKind::FunctionDefinition(_) => {
                self.scope = Weak::clone(&self.declarations);
            }
            _ => {}
        }
    }

    fn on_exit(&mut self, tree: &'a AST) {
        match self.node(tree) {
            NodeKind::Program(_) => {
                self.main_scope = Weak::new();
                self.scope = Weak::new();
            }
            NodeKind::Block(ref block) => {
                self.scope = Weak::clone(block.scope().borrow().parent());
            }
            NodeKind::CaseArm(ref arm) => {
                self.scope = Weak::clone(arm.scope().borrow().parent());
            }
            NodeKind::Identifier(_) => {}
            NodeKind::StructDefinition(_) => {
                self.scope = Weak::clone(&self.main_scope);
            }
            NodeKind::FunctionDefinition(_) => {
                self.scope = Weak::clone(&self.main_scope);
            }
            _ => {}
        }
    }
}

#[allow(unused_variables, unused_mut)]
pub trait Visitor<'a> {
    // Token
    fn enter_whitespace(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        token: &Token,
        trivia: &Trivia,
    ) {
    }
    fn exit_whitespace(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        token: &Token,
        trivia: &Trivia,
    ) {
    }

    fn enter_line_comment(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        token: &Token,
        trivia: &Trivia,
        comment: &str,
    ) {
    }
    fn exit_line_comment(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        token: &Token,
        trivia: &Trivia,
        comment: &str,
    ) {
    }

    fn enter_interpreted_token(&mut self, tree: &'a AST, path: &mut NodePath, token: &Token) {}
    fn exit_interpreted_token(&mut self, tree: &'a AST, path: &mut NodePath, token: &Token) {}

    fn enter_missing_token(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        range: EffectiveRange,
        item: MissingTokenKind,
    ) {
    }
    fn exit_missing_token(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        range: EffectiveRange,
        item: MissingTokenKind,
    ) {
    }

    fn enter_skipped_token(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        token: &Token,
        expected: MissingTokenKind,
    ) {
    }
    fn exit_skipped_token(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        token: &Token,
        expected: MissingTokenKind,
    ) {
    }

    // Node
    fn enter_program(&mut self, tree: &'a AST, path: &mut NodePath, program: &'a Program) {}
    fn exit_program(&mut self, tree: &'a AST, path: &mut NodePath, program: &'a Program) {}

    fn enter_block(&mut self, tree: &'a AST, path: &mut NodePath, block: &'a Block) {}
    fn exit_block(&mut self, tree: &'a AST, path: &mut NodePath, block: &'a Block) {}

    fn enter_identifier(&mut self, tree: &'a AST, path: &mut NodePath, id: &'a Identifier) {}
    fn exit_identifier(&mut self, tree: &'a AST, path: &mut NodePath, id: &'a Identifier) {}

    fn enter_struct_definition(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        definition: &'a StructDefinition,
    ) {
    }
    fn exit_struct_definition(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        definition: &'a StructDefinition,
    ) {
    }

    fn enter_function_definition(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        definition: &'a FunctionDefinition,
    ) {
    }
    fn exit_function_definition(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        definition: &'a FunctionDefinition,
    ) {
    }

    fn enter_function_parameter(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        param: &'a FunctionParameter,
    ) {
    }
    fn exit_function_parameter(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        param: &'a FunctionParameter,
    ) {
    }

    fn enter_type_field(&mut self, tree: &'a AST, path: &mut NodePath, field: &'a TypeField) {}
    fn exit_type_field(&mut self, tree: &'a AST, path: &mut NodePath, field: &'a TypeField) {}

    fn enter_type_annotation(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        annotation: &'a TypeAnnotation,
    ) {
    }
    fn exit_type_annotation(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        annotation: &'a TypeAnnotation,
    ) {
    }

    fn enter_statement(&mut self, tree: &'a AST, path: &mut NodePath, statement: &'a Statement) {}
    fn exit_statement(&mut self, tree: &'a AST, path: &mut NodePath, statement: &'a Statement) {}

    fn enter_variable_declaration(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        declaration: &'a VariableDeclaration,
    ) {
    }
    fn exit_variable_declaration(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        declaration: &'a VariableDeclaration,
    ) {
    }

    fn enter_case_arm(&mut self, tree: &'a AST, path: &mut NodePath, arm: &'a CaseArm) {}
    fn exit_case_arm(&mut self, tree: &'a AST, path: &mut NodePath, arm: &'a CaseArm) {}

    fn enter_pattern(&mut self, tree: &'a AST, path: &mut NodePath, pattern: &'a Pattern) {}
    fn exit_pattern(&mut self, tree: &'a AST, path: &mut NodePath, pattern: &'a Pattern) {}

    fn enter_value_field(&mut self, tree: &'a AST, path: &mut NodePath, field: &'a ValueField) {}
    fn exit_value_field(&mut self, tree: &'a AST, path: &mut NodePath, field: &'a ValueField) {}

    fn enter_value_field_pattern(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        pattern: &'a ValueFieldPattern,
    ) {
    }
    fn exit_value_field_pattern(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        pattern: &'a ValueFieldPattern,
    ) {
    }

    fn enter_expression(&mut self, tree: &'a AST, path: &mut NodePath, expression: &'a Expression) {
    }
    fn exit_expression(&mut self, tree: &'a AST, path: &mut NodePath, expression: &'a Expression) {}

    fn enter_integer_literal(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        expr: &'a Expression,
        literal: i32,
    ) {
    }
    fn exit_integer_literal(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        expr: &'a Expression,
        literal: i32,
    ) {
    }

    fn enter_string_literal(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        expr: &'a Expression,
        literal: Option<&str>,
    ) {
    }
    fn exit_string_literal(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        expr: &'a Expression,
        literal: Option<&str>,
    ) {
    }

    fn enter_struct_literal(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        expr: &'a Expression,
        literal: &'a StructLiteral,
    ) {
    }
    fn exit_struct_literal(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        expr: &'a Expression,
        literal: &'a StructLiteral,
    ) {
    }

    fn enter_variable(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        expr: &'a Expression,
        id: &'a Identifier,
    ) {
    }
    fn exit_variable(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        expr: &'a Expression,
        id: &'a Identifier,
    ) {
    }

    fn enter_binary_expression(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        expr: &'a Expression,
        bin_expr: &'a BinaryExpression,
    ) {
    }
    fn exit_binary_expression(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        expr: &'a Expression,
        bin_expr: &'a BinaryExpression,
    ) {
    }

    fn enter_unary_expression(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        expr: &'a Expression,
        unary_expr: &'a UnaryExpression,
    ) {
    }
    fn exit_unary_expression(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        expr: &'a Expression,
        unary_expr: &'a UnaryExpression,
    ) {
    }

    fn enter_subscript_expression(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        expr: &'a Expression,
        subscript_expr: &'a SubscriptExpression,
    ) {
    }
    fn exit_subscript_expression(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        expr: &'a Expression,
        subscript_expr: &'a SubscriptExpression,
    ) {
    }

    fn enter_call_expression(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        expr: &'a Expression,
        call_expr: &'a CallExpression,
    ) {
    }
    fn exit_call_expression(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        expr: &'a Expression,
        call_expr: &'a CallExpression,
    ) {
    }

    fn enter_access_expression(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        expr: &'a Expression,
        member_expr: &'a MemberExpression,
    ) {
    }
    fn exit_access_expression(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        expr: &'a Expression,
        member_expr: &'a MemberExpression,
    ) {
    }

    fn enter_array_expression(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        expr: &'a Expression,
        array_expr: &'a ArrayExpression,
    ) {
    }
    fn exit_array_expression(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        expr: &'a Expression,
        array_expr: &'a ArrayExpression,
    ) {
    }

    fn enter_if_expression(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        expr: &'a Expression,
        if_expr: &'a IfExpression,
    ) {
    }
    fn exit_if_expression(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        expr: &'a Expression,
        if_expr: &'a IfExpression,
    ) {
    }

    fn enter_case_expression(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        expr: &'a Expression,
        case_expr: &'a CaseExpression,
    ) {
    }
    fn exit_case_expression(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        expr: &'a Expression,
        case_expr: &'a CaseExpression,
    ) {
    }
}

pub fn traverse<'a>(visitor: &mut dyn Visitor<'a>, tree: &'a AST) {
    let path = wrap(NodePath::new(tree.root()));
    traverse_path(visitor, tree, &path);
}

fn traverse_path<'a>(visitor: &mut dyn Visitor<'a>, tree: &'a AST, path: &Rc<RefCell<NodePath>>) {
    path.borrow_mut().on_enter(tree);

    if !path.borrow().skipped() {
        dispatch_enter(visitor, tree, path);
    }
    if !path.borrow().skipped() {
        traverse_children(visitor, tree, path);
    }
    if !path.borrow().skipped() {
        dispatch_exit(visitor, tree, path);
    }

    path.borrow_mut().on_exit(tree);
}

fn dispatch_enter<'a>(visitor: &mut dyn Visitor<'a>, tree: &'a AST, path: &Rc<RefCell<NodePath>>) {
    let mut path = &mut path.borrow_mut();
    let node = path.node(tree);

    match node {
        NodeKind::Program(kind) => {
            visitor.enter_program(tree, &mut path, kind);
        }
        NodeKind::Block(kind) => {
            visitor.enter_block(tree, &mut path, kind);
        }
        NodeKind::Identifier(kind) => {
            visitor.enter_identifier(tree, &mut path, kind);
        }
        NodeKind::StructDefinition(kind) => {
            visitor.enter_struct_definition(tree, &mut path, kind);
        }
        NodeKind::FunctionDefinition(kind) => {
            visitor.enter_function_definition(tree, &mut path, kind);
        }
        NodeKind::TypeField(kind) => {
            visitor.enter_type_field(tree, &mut path, kind);
        }
        NodeKind::TypeAnnotation(kind) => {
            visitor.enter_type_annotation(tree, &mut path, kind);
        }
        NodeKind::FunctionParameter(kind) => {
            visitor.enter_function_parameter(tree, &mut path, kind);
        }
        NodeKind::Statement(kind) => {
            visitor.enter_statement(tree, &mut path, kind);
        }
        NodeKind::VariableDeclaration(kind) => {
            visitor.enter_variable_declaration(tree, &mut path, kind);
        }
        NodeKind::CaseArm(kind) => {
            visitor.enter_case_arm(tree, &mut path, kind);
        }
        NodeKind::Pattern(kind) => {
            visitor.enter_pattern(tree, &mut path, kind);
        }
        NodeKind::ValueField(kind) => {
            visitor.enter_value_field(tree, &mut path, kind);
        }
        NodeKind::ValueFieldPattern(kind) => {
            visitor.enter_value_field_pattern(tree, &mut path, kind);
        }
        NodeKind::Expression(expr) => {
            visitor.enter_expression(tree, &mut path, expr);

            if !path.skipped() {
                match expr.kind() {
                    ExpressionKind::IntegerLiteral(value) => {
                        visitor.enter_integer_literal(tree, &mut path, expr, *value);
                    }
                    ExpressionKind::StringLiteral(value) => {
                        visitor.enter_string_literal(tree, &mut path, expr, value.as_deref());
                    }
                    ExpressionKind::StructLiteral(kind) => {
                        visitor.enter_struct_literal(tree, &mut path, expr, kind);
                    }
                    ExpressionKind::VariableExpression(node_id) => {
                        let id = tree.get(*node_id).unwrap().identifier().unwrap();
                        visitor.enter_variable(tree, &mut path, expr, id);
                    }
                    ExpressionKind::BinaryExpression(kind) => {
                        visitor.enter_binary_expression(tree, &mut path, expr, kind);
                    }
                    ExpressionKind::UnaryExpression(kind) => {
                        visitor.enter_unary_expression(tree, &mut path, expr, kind);
                    }
                    ExpressionKind::SubscriptExpression(kind) => {
                        visitor.enter_subscript_expression(tree, &mut path, expr, kind);
                    }
                    ExpressionKind::CallExpression(kind) => {
                        visitor.enter_call_expression(tree, &mut path, expr, kind);
                    }
                    ExpressionKind::MemberExpression(kind) => {
                        visitor.enter_access_expression(tree, &mut path, expr, kind);
                    }
                    ExpressionKind::ArrayExpression(kind) => {
                        visitor.enter_array_expression(tree, &mut path, expr, kind);
                    }
                    ExpressionKind::IfExpression(kind) => {
                        visitor.enter_if_expression(tree, &mut path, expr, kind);
                    }
                    ExpressionKind::CaseExpression(kind) => {
                        visitor.enter_case_expression(tree, &mut path, expr, kind);
                    }
                    ExpressionKind::Expression(_) => {}
                }
            }
        }
    }
}

fn dispatch_exit<'a>(visitor: &mut dyn Visitor<'a>, tree: &'a AST, path: &Rc<RefCell<NodePath>>) {
    let mut path = &mut path.borrow_mut();
    let node = path.node(tree);

    match node {
        NodeKind::Program(kind) => {
            visitor.exit_program(tree, &mut path, kind);
        }
        NodeKind::Block(kind) => {
            visitor.exit_block(tree, &mut path, kind);
        }
        NodeKind::Identifier(kind) => {
            visitor.exit_identifier(tree, &mut path, kind);
        }
        NodeKind::StructDefinition(kind) => {
            visitor.exit_struct_definition(tree, &mut path, kind);
        }
        NodeKind::FunctionDefinition(kind) => {
            visitor.exit_function_definition(tree, &mut path, kind);
        }
        NodeKind::TypeField(kind) => {
            visitor.exit_type_field(tree, &mut path, kind);
        }
        NodeKind::TypeAnnotation(kind) => {
            visitor.exit_type_annotation(tree, &mut path, kind);
        }
        NodeKind::FunctionParameter(kind) => {
            visitor.exit_function_parameter(tree, &mut path, kind);
        }
        NodeKind::Statement(kind) => {
            visitor.exit_statement(tree, &mut path, kind);
        }
        NodeKind::VariableDeclaration(kind) => {
            visitor.exit_variable_declaration(tree, &mut path, kind);
        }
        NodeKind::Pattern(kind) => {
            visitor.exit_pattern(tree, &mut path, kind);
        }
        NodeKind::CaseArm(kind) => {
            visitor.exit_case_arm(tree, &mut path, kind);
        }
        NodeKind::ValueField(kind) => {
            visitor.exit_value_field(tree, &mut path, kind);
        }
        NodeKind::ValueFieldPattern(kind) => {
            visitor.exit_value_field_pattern(tree, &mut path, kind);
        }
        NodeKind::Expression(expr) => {
            visitor.exit_expression(tree, &mut path, expr);

            if !path.skipped() {
                match expr.kind() {
                    ExpressionKind::IntegerLiteral(value) => {
                        visitor.exit_integer_literal(tree, &mut path, expr, *value);
                    }
                    ExpressionKind::StringLiteral(value) => {
                        visitor.exit_string_literal(tree, &mut path, expr, value.as_deref());
                    }
                    ExpressionKind::VariableExpression(node_id) => {
                        let id = tree.get(*node_id).unwrap().identifier().unwrap();
                        visitor.exit_variable(tree, &mut path, expr, id);
                    }
                    ExpressionKind::StructLiteral(kind) => {
                        visitor.exit_struct_literal(tree, &mut path, expr, kind);
                    }
                    ExpressionKind::BinaryExpression(kind) => {
                        visitor.exit_binary_expression(tree, &mut path, expr, kind);
                    }
                    ExpressionKind::UnaryExpression(kind) => {
                        visitor.exit_unary_expression(tree, &mut path, expr, kind);
                    }
                    ExpressionKind::SubscriptExpression(kind) => {
                        visitor.exit_subscript_expression(tree, &mut path, expr, kind);
                    }
                    ExpressionKind::MemberExpression(kind) => {
                        visitor.exit_access_expression(tree, &mut path, expr, kind);
                    }
                    ExpressionKind::CallExpression(kind) => {
                        visitor.exit_call_expression(tree, &mut path, expr, kind);
                    }
                    ExpressionKind::ArrayExpression(kind) => {
                        visitor.exit_array_expression(tree, &mut path, expr, kind);
                    }
                    ExpressionKind::IfExpression(kind) => {
                        visitor.exit_if_expression(tree, &mut path, expr, kind);
                    }
                    ExpressionKind::CaseExpression(kind) => {
                        visitor.exit_case_expression(tree, &mut path, expr, kind);
                    }
                    ExpressionKind::Expression(_) => {}
                }
            }
        }
    }
}

fn traverse_children<'a>(
    visitor: &mut dyn Visitor<'a>,
    tree: &'a AST,
    path: &Rc<RefCell<NodePath>>,
) {
    let node = path.borrow().node(tree);

    for kind in node.code() {
        if path.borrow().skipped() {
            break;
        }

        match kind {
            CodeKind::Node(node) => {
                let child_path = wrap(NodePath::child_path(*node, path));
                traverse_path(visitor, tree, &child_path);

                // Propagates `stop`
                path.borrow_mut().stopped = child_path.borrow().stopped;
            }
            CodeKind::SyntaxToken(token) => {
                let mut mut_path = path.borrow_mut();

                match token {
                    SyntaxToken::Interpreted(token) => {
                        traverse_interpreted_token(visitor, tree, &mut mut_path, token)
                    }
                    SyntaxToken::Missing { range, item } => {
                        traverse_missing_token(visitor, tree, &mut mut_path, *range, *item)
                    }
                    SyntaxToken::Skipped { token, expected } => {
                        traverse_skipped_token(visitor, tree, &mut mut_path, token, *expected)
                    }
                }
            }
        }
    }
}

fn traverse_token_trivia<'a>(
    visitor: &mut dyn Visitor<'a>,
    tree: &'a AST,
    path: &mut NodePath,
    token: &Token,
) {
    for trivia in &token.leading_trivia {
        if path.skipped() {
            break;
        }

        match &trivia.kind {
            TriviaKind::LineComment(comment) => {
                if !path.skipped() {
                    visitor.enter_line_comment(tree, path, token, trivia, comment);
                }
                if !path.skipped() {
                    visitor.exit_line_comment(tree, path, token, trivia, comment);
                }
            }
            TriviaKind::Whitespace => {
                if !path.skipped() {
                    visitor.enter_whitespace(tree, path, token, trivia);
                }
                if !path.skipped() {
                    visitor.exit_whitespace(tree, path, token, trivia);
                }
            }
        }
    }
}

fn traverse_interpreted_token<'a>(
    visitor: &mut dyn Visitor<'a>,
    tree: &'a AST,
    path: &mut NodePath,
    token: &Token,
) {
    if !path.skipped() {
        traverse_token_trivia(visitor, tree, path, token);
    }
    if !path.skipped() {
        visitor.enter_interpreted_token(tree, path, token);
    }
    if !path.skipped() {
        visitor.exit_interpreted_token(tree, path, token);
    }
}

fn traverse_missing_token<'a>(
    visitor: &mut dyn Visitor<'a>,
    tree: &'a AST,
    path: &mut NodePath,
    range: EffectiveRange,
    item: MissingTokenKind,
) {
    if !path.skipped() {
        visitor.enter_missing_token(tree, path, range, item);
    }
    if !path.skipped() {
        visitor.exit_missing_token(tree, path, range, item);
    }
}

fn traverse_skipped_token<'a>(
    visitor: &mut dyn Visitor<'a>,
    tree: &'a AST,
    path: &mut NodePath,
    token: &Token,
    expected: MissingTokenKind,
) {
    if !path.skipped() {
        traverse_token_trivia(visitor, tree, path, token);
    }
    if !path.skipped() {
        visitor.enter_skipped_token(tree, path, token, expected);
    }
    if !path.skipped() {
        visitor.exit_skipped_token(tree, path, token, expected);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::Parser;

    #[derive(Debug, Default)]
    struct NodeCounter {
        number_of_expressions: i32,
    }

    impl<'a> Visitor<'a> for NodeCounter {
        fn enter_expression(&mut self, _tree: &'a AST, _path: &mut NodePath, _expr: &Expression) {
            self.number_of_expressions += 1;
        }
    }

    #[test]
    fn number_integer() {
        let mut visitor = NodeCounter::default();
        let mut tree = Parser::parse_string("42");

        traverse(&mut visitor, &mut tree);
        assert_eq!(visitor.number_of_expressions, 1);
    }
}
