use super::{EffectiveRange, MissingTokenKind, Scope, SyntaxToken, Trivia, TriviaKind};
use crate::syntax::Token;
use crate::{syntax::tree::*, util::wrap};
use std::{
    cell::RefCell,
    rc::{Rc, Weak},
};

pub struct NodePath<'a> {
    skipped: bool,
    stopped: bool,
    node_id: NodeId,
    tree: &'a mut AST,
    scope: Weak<RefCell<Scope>>,
    main_scope: Weak<RefCell<Scope>>,
    declarations: Weak<RefCell<Scope>>,
    parent: Option<Rc<RefCell<NodePath<'a>>>>,
}

impl<'a> NodePath<'a> {
    pub fn new(tree: &'a mut AST, node_id: NodeId) -> Self {
        Self {
            skipped: false,
            stopped: false,
            tree,
            node_id,
            parent: None,
            declarations: Weak::new(),
            scope: Weak::new(),
            main_scope: Weak::new(),
        }
    }

    pub fn child_path(node_id: NodeId, parent: &'a Rc<RefCell<NodePath<'a>>>) -> Self {
        let borrowed_parent = parent.borrow();

        Self {
            skipped: false,
            stopped: false,
            tree: borrowed_parent.tree_mut(),
            node_id,
            parent: Some(Rc::clone(parent)),
            scope: Weak::clone(&borrowed_parent.scope),
            main_scope: Weak::clone(&borrowed_parent.main_scope),
            declarations: Weak::clone(&borrowed_parent.declarations),
        }
    }

    pub fn tree(&self) -> &AST {
        self.tree
    }

    fn tree_mut(&self) -> &mut AST {
        self.tree
    }

    pub fn node_id(&self) -> NodeId {
        self.node_id
    }

    pub fn node(&self) -> &NodeKind {
        self.tree.get(self.node_id).unwrap()
    }

    pub fn node_mut(&mut self) -> &mut NodeKind {
        self.tree.get_mut(self.node_id).unwrap()
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

    pub fn parent(&self) -> Option<Rc<RefCell<NodePath<'a>>>> {
        self.parent.as_ref().map(Rc::clone)
    }

    pub fn expect_parent(&self) -> Rc<RefCell<NodePath<'a>>> {
        self.parent()
            .unwrap_or_else(|| panic!("parent must exist."))
    }

    pub fn scope(&self) -> Rc<RefCell<Scope>> {
        self.scope
            .upgrade()
            .unwrap_or_else(|| panic!("scope must live."))
    }

    fn on_enter(&mut self) {
        match self.node() {
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

    fn on_exit(&mut self) {
        match self.node() {
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
    fn enter_whitespace(&mut self, path: &mut NodePath<'_>, token: &Token, trivia: &Trivia) {}
    fn exit_whitespace(&mut self, path: &mut NodePath<'a>, token: &Token, trivia: &Trivia) {}

    fn enter_line_comment(
        &mut self,
        path: &mut NodePath<'a>,
        token: &Token,
        trivia: &Trivia,
        comment: &str,
    ) {
    }
    fn exit_line_comment(
        &mut self,
        path: &mut NodePath<'a>,
        token: &Token,
        trivia: &Trivia,
        comment: &str,
    ) {
    }

    fn enter_interpreted_token(&mut self, path: &mut NodePath<'a>, token: &Token) {}
    fn exit_interpreted_token(&mut self, path: &mut NodePath<'a>, token: &Token) {}

    fn enter_missing_token(
        &mut self,
        path: &mut NodePath<'a>,
        range: EffectiveRange,
        item: MissingTokenKind,
    ) {
    }
    fn exit_missing_token(
        &mut self,
        path: &mut NodePath<'a>,
        range: EffectiveRange,
        item: MissingTokenKind,
    ) {
    }

    fn enter_skipped_token(
        &mut self,
        path: &mut NodePath<'a>,
        token: &Token,
        expected: MissingTokenKind,
    ) {
    }
    fn exit_skipped_token(
        &mut self,
        path: &mut NodePath<'a>,
        token: &Token,
        expected: MissingTokenKind,
    ) {
    }

    // Node
    fn enter_program(&mut self, path: &mut NodePath<'a>, program: &mut Program) {}
    fn exit_program(&mut self, path: &mut NodePath<'a>, program: &mut Program) {}

    fn enter_block(&mut self, path: &mut NodePath<'a>, block: &mut Block) {}
    fn exit_block(&mut self, path: &mut NodePath<'a>, block: &mut Block) {}

    fn enter_identifier(&mut self, path: &mut NodePath<'a>, id: &mut Identifier) {}
    fn exit_identifier(&mut self, path: &mut NodePath<'a>, id: &mut Identifier) {}

    fn enter_struct_definition(
        &mut self,
        path: &mut NodePath<'a>,
        definition: &mut StructDefinition,
    ) {
    }
    fn exit_struct_definition(
        &mut self,
        path: &mut NodePath<'a>,
        definition: &mut StructDefinition,
    ) {
    }

    fn enter_function_definition(
        &mut self,
        path: &mut NodePath<'a>,
        definition: &mut FunctionDefinition,
    ) {
    }
    fn exit_function_definition(
        &mut self,
        path: &mut NodePath<'a>,
        definition: &mut FunctionDefinition,
    ) {
    }

    fn enter_function_parameter(&mut self, path: &mut NodePath<'a>, param: &mut FunctionParameter) {
    }
    fn exit_function_parameter(&mut self, path: &mut NodePath<'a>, param: &mut FunctionParameter) {}

    fn enter_type_field(&mut self, path: &mut NodePath<'a>, field: &mut TypeField) {}
    fn exit_type_field(&mut self, path: &mut NodePath<'a>, field: &mut TypeField) {}

    fn enter_type_annotation(&mut self, path: &mut NodePath<'a>, annotation: &mut TypeAnnotation) {}
    fn exit_type_annotation(&mut self, path: &mut NodePath<'a>, annotation: &mut TypeAnnotation) {}

    fn enter_statement(&mut self, path: &mut NodePath<'a>, statement: &mut Statement) {}
    fn exit_statement(&mut self, path: &mut NodePath<'a>, statement: &mut Statement) {}

    fn enter_variable_declaration(
        &mut self,
        path: &mut NodePath<'a>,
        declaration: &mut VariableDeclaration,
    ) {
    }
    fn exit_variable_declaration(
        &mut self,
        path: &mut NodePath<'a>,
        declaration: &mut VariableDeclaration,
    ) {
    }

    fn enter_case_arm(&mut self, path: &mut NodePath<'a>, arm: &mut CaseArm) {}
    fn exit_case_arm(&mut self, path: &mut NodePath<'a>, arm: &mut CaseArm) {}

    fn enter_pattern(&mut self, path: &mut NodePath<'a>, pattern: &mut Pattern) {}
    fn exit_pattern(&mut self, path: &mut NodePath<'a>, pattern: &mut Pattern) {}

    fn enter_value_field(&mut self, path: &mut NodePath<'a>, field: &mut ValueField) {}
    fn exit_value_field(&mut self, path: &mut NodePath<'a>, field: &mut ValueField) {}

    fn enter_value_field_pattern(
        &mut self,
        path: &mut NodePath<'a>,
        pattern: &mut ValueFieldPattern,
    ) {
    }
    fn exit_value_field_pattern(
        &mut self,
        path: &mut NodePath<'a>,
        pattern: &mut ValueFieldPattern,
    ) {
    }

    fn enter_expression(&mut self, path: &mut NodePath<'a>, expression: &mut Expression) {}
    fn exit_expression(&mut self, path: &mut NodePath<'a>, expression: &mut Expression) {}

    fn enter_integer_literal(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &mut Expression,
        literal: i32,
    ) {
    }
    fn exit_integer_literal(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &mut Expression,
        literal: i32,
    ) {
    }

    fn enter_string_literal(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &mut Expression,
        literal: Option<&str>,
    ) {
    }
    fn exit_string_literal(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &mut Expression,
        literal: Option<&str>,
    ) {
    }

    fn enter_struct_literal(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &mut Expression,
        value: &StructLiteral,
    ) {
    }
    fn exit_struct_literal(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &mut Expression,
        value: &StructLiteral,
    ) {
    }

    fn enter_variable(&mut self, path: &mut NodePath<'a>, expr: &mut Expression, id: &Identifier) {}
    fn exit_variable(&mut self, path: &mut NodePath<'a>, expr: &mut Expression, id: &Identifier) {}

    fn enter_binary_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &mut Expression,
        bin_expr: &BinaryExpression,
    ) {
    }
    fn exit_binary_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &mut Expression,
        bin_expr: &BinaryExpression,
    ) {
    }

    fn enter_unary_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &mut Expression,
        unary_expr: &UnaryExpression,
    ) {
    }
    fn exit_unary_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &mut Expression,
        unary_expr: &UnaryExpression,
    ) {
    }

    fn enter_subscript_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &mut Expression,
        subscript_expr: &SubscriptExpression,
    ) {
    }
    fn exit_subscript_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &mut Expression,
        subscript_expr: &SubscriptExpression,
    ) {
    }

    fn enter_call_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &mut Expression,
        call_expr: &CallExpression,
    ) {
    }
    fn exit_call_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &mut Expression,
        call_expr: &CallExpression,
    ) {
    }

    fn enter_access_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &mut Expression,
        member_expr: &MemberExpression,
    ) {
    }
    fn exit_access_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &mut Expression,
        member_expr: &MemberExpression,
    ) {
    }

    fn enter_array_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &mut Expression,
        array_expr: &ArrayExpression,
    ) {
    }
    fn exit_array_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &mut Expression,
        array_expr: &ArrayExpression,
    ) {
    }

    fn enter_if_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &mut Expression,
        if_expr: &IfExpression,
    ) {
    }
    fn exit_if_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &mut Expression,
        if_expr: &IfExpression,
    ) {
    }

    fn enter_case_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &mut Expression,
        case_expr: &CaseExpression,
    ) {
    }
    fn exit_case_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &mut Expression,
        case_expr: &CaseExpression,
    ) {
    }
}

pub fn traverse<'a>(visitor: &mut dyn Visitor<'a>, tree: &'a mut AST) {
    let path = wrap(NodePath::new(tree, tree.root()));
    traverse_path(visitor, &path);
}

fn traverse_path<'a>(visitor: &mut dyn Visitor<'a>, path: &'a Rc<RefCell<NodePath<'a>>>) {
    path.borrow_mut().on_enter();

    if !path.borrow().skipped() {
        dispatch_enter(visitor, path);
    }
    if !path.borrow().skipped() {
        traverse_children(visitor, path);
    }
    if !path.borrow().skipped() {
        dispatch_exit(visitor, path);
    }

    path.borrow_mut().on_exit();
}

fn dispatch_enter<'a>(visitor: &mut dyn Visitor<'a>, path: &'a Rc<RefCell<NodePath<'a>>>) {
    let mut path = &mut path.borrow_mut();
    let node = path.node_mut();

    match node {
        NodeKind::Program(kind) => {
            visitor.enter_program(&mut path, kind);
        }
        NodeKind::Block(kind) => {
            visitor.enter_block(&mut path, kind);
        }
        NodeKind::Identifier(kind) => {
            visitor.enter_identifier(&mut path, kind);
        }
        NodeKind::StructDefinition(kind) => {
            visitor.enter_struct_definition(&mut path, kind);
        }
        NodeKind::FunctionDefinition(kind) => {
            visitor.enter_function_definition(&mut path, kind);
        }
        NodeKind::TypeField(kind) => {
            visitor.enter_type_field(&mut path, kind);
        }
        NodeKind::TypeAnnotation(kind) => {
            visitor.enter_type_annotation(&mut path, kind);
        }
        NodeKind::FunctionParameter(kind) => {
            visitor.enter_function_parameter(&mut path, kind);
        }
        NodeKind::Statement(kind) => {
            visitor.enter_statement(&mut path, kind);
        }
        NodeKind::VariableDeclaration(kind) => {
            visitor.enter_variable_declaration(&mut path, kind);
        }
        NodeKind::CaseArm(kind) => {
            visitor.enter_case_arm(&mut path, kind);
        }
        NodeKind::Pattern(kind) => {
            visitor.enter_pattern(&mut path, kind);
        }
        NodeKind::ValueField(kind) => {
            visitor.enter_value_field(&mut path, kind);
        }
        NodeKind::ValueFieldPattern(kind) => {
            visitor.enter_value_field_pattern(&mut path, kind);
        }
        NodeKind::Expression(expr) => {
            visitor.enter_expression(&mut path, expr);

            if !path.skipped() {
                match expr.kind() {
                    ExpressionKind::IntegerLiteral(value) => {
                        visitor.enter_integer_literal(&mut path, expr, *value);
                    }
                    ExpressionKind::StringLiteral(value) => {
                        visitor.enter_string_literal(&mut path, expr, value.as_deref());
                    }
                    ExpressionKind::StructLiteral(kind) => {
                        visitor.enter_struct_literal(&mut path, expr, kind);
                    }
                    ExpressionKind::VariableExpression(node_id) => {
                        let id = path.tree().get_mut(*node_id).unwrap().identifier().unwrap();
                        visitor.enter_variable(&mut path, expr, id);
                    }
                    ExpressionKind::BinaryExpression(kind) => {
                        visitor.enter_binary_expression(&mut path, expr, kind);
                    }
                    ExpressionKind::UnaryExpression(kind) => {
                        visitor.enter_unary_expression(&mut path, expr, kind);
                    }
                    ExpressionKind::SubscriptExpression(kind) => {
                        visitor.enter_subscript_expression(&mut path, expr, kind);
                    }
                    ExpressionKind::CallExpression(kind) => {
                        visitor.enter_call_expression(&mut path, expr, kind);
                    }
                    ExpressionKind::MemberExpression(kind) => {
                        visitor.enter_access_expression(&mut path, expr, kind);
                    }
                    ExpressionKind::ArrayExpression(kind) => {
                        visitor.enter_array_expression(&mut path, expr, kind);
                    }
                    ExpressionKind::IfExpression(kind) => {
                        visitor.enter_if_expression(&mut path, expr, kind);
                    }
                    ExpressionKind::CaseExpression(kind) => {
                        visitor.enter_case_expression(&mut path, expr, kind);
                    }
                    ExpressionKind::Expression(_) => {}
                }
            }
        }
    }
}

fn dispatch_exit<'a>(visitor: &mut dyn Visitor<'a>, path: &Rc<RefCell<NodePath<'a>>>) {
    let mut path = &mut path.borrow_mut();
    let node = path.node_mut();

    match node {
        NodeKind::Program(kind) => {
            visitor.exit_program(&mut path, kind);
        }
        NodeKind::Block(kind) => {
            visitor.exit_block(&mut path, kind);
        }
        NodeKind::Identifier(kind) => {
            visitor.exit_identifier(&mut path, kind);
        }
        NodeKind::StructDefinition(kind) => {
            visitor.exit_struct_definition(&mut path, kind);
        }
        NodeKind::FunctionDefinition(kind) => {
            visitor.exit_function_definition(&mut path, kind);
        }
        NodeKind::TypeField(kind) => {
            visitor.exit_type_field(&mut path, kind);
        }
        NodeKind::TypeAnnotation(kind) => {
            visitor.exit_type_annotation(&mut path, kind);
        }
        NodeKind::FunctionParameter(kind) => {
            visitor.exit_function_parameter(&mut path, kind);
        }
        NodeKind::Statement(kind) => {
            visitor.exit_statement(&mut path, kind);
        }
        NodeKind::VariableDeclaration(kind) => {
            visitor.exit_variable_declaration(&mut path, kind);
        }
        NodeKind::Pattern(kind) => {
            visitor.exit_pattern(&mut path, kind);
        }
        NodeKind::CaseArm(kind) => {
            visitor.exit_case_arm(&mut path, kind);
        }
        NodeKind::ValueField(kind) => {
            visitor.exit_value_field(&mut path, kind);
        }
        NodeKind::ValueFieldPattern(kind) => {
            visitor.exit_value_field_pattern(&mut path, kind);
        }
        NodeKind::Expression(expr) => {
            visitor.exit_expression(&mut path, expr);

            if !path.skipped() {
                match expr.kind() {
                    ExpressionKind::IntegerLiteral(value) => {
                        visitor.exit_integer_literal(&mut path, expr, *value);
                    }
                    ExpressionKind::StringLiteral(value) => {
                        visitor.exit_string_literal(&mut path, expr, value.as_deref());
                    }
                    ExpressionKind::VariableExpression(node_id) => {
                        let id = path.tree().get_mut(*node_id).unwrap().identifier().unwrap();
                        visitor.exit_variable(&mut path, expr, id);
                    }
                    ExpressionKind::StructLiteral(kind) => {
                        visitor.exit_struct_literal(&mut path, expr, kind);
                    }
                    ExpressionKind::BinaryExpression(kind) => {
                        visitor.exit_binary_expression(&mut path, expr, kind);
                    }
                    ExpressionKind::UnaryExpression(kind) => {
                        visitor.exit_unary_expression(&mut path, expr, kind);
                    }
                    ExpressionKind::SubscriptExpression(kind) => {
                        visitor.exit_subscript_expression(&mut path, expr, kind);
                    }
                    ExpressionKind::MemberExpression(kind) => {
                        visitor.exit_access_expression(&mut path, expr, kind);
                    }
                    ExpressionKind::CallExpression(kind) => {
                        visitor.exit_call_expression(&mut path, expr, kind);
                    }
                    ExpressionKind::ArrayExpression(kind) => {
                        visitor.exit_array_expression(&mut path, expr, kind);
                    }
                    ExpressionKind::IfExpression(kind) => {
                        visitor.exit_if_expression(&mut path, expr, kind);
                    }
                    ExpressionKind::CaseExpression(kind) => {
                        visitor.exit_case_expression(&mut path, expr, kind);
                    }
                    ExpressionKind::Expression(_) => {}
                }
            }
        }
    }
}

fn traverse_children<'a>(visitor: &mut dyn Visitor<'a>, path: &'a Rc<RefCell<NodePath<'a>>>) {
    let node = path.borrow().node().clone();

    for kind in node.code() {
        if path.borrow().skipped() {
            break;
        }

        match kind {
            CodeKind::Node(node) => {
                let child_path = wrap(NodePath::child_path(*node, &path));
                traverse_path(visitor, &child_path);

                // Propagates `stop`
                path.borrow_mut().stopped = child_path.borrow().stopped;
            }
            CodeKind::SyntaxToken(token) => {
                let mut mut_path = path.borrow_mut();

                match token {
                    SyntaxToken::Interpreted(token) => {
                        traverse_interpreted_token(visitor, &mut mut_path, token)
                    }
                    SyntaxToken::Missing { range, item } => {
                        traverse_missing_token(visitor, &mut mut_path, *range, *item)
                    }
                    SyntaxToken::Skipped { token, expected } => {
                        traverse_skipped_token(visitor, &mut mut_path, token, *expected)
                    }
                }
            }
        }
    }
}

fn traverse_token_trivia<'a>(
    visitor: &mut dyn Visitor<'a>,
    path: &mut NodePath<'a>,
    token: &Token,
) {
    for trivia in &token.leading_trivia {
        if path.skipped() {
            break;
        }

        match &trivia.kind {
            TriviaKind::LineComment(comment) => {
                if !path.skipped() {
                    visitor.enter_line_comment(path, token, trivia, comment);
                }
                if !path.skipped() {
                    visitor.exit_line_comment(path, token, trivia, comment);
                }
            }
            TriviaKind::Whitespace => {
                if !path.skipped() {
                    visitor.enter_whitespace(path, token, trivia);
                }
                if !path.skipped() {
                    visitor.exit_whitespace(path, token, trivia);
                }
            }
        }
    }
}

fn traverse_interpreted_token<'a>(
    visitor: &mut dyn Visitor<'a>,
    path: &mut NodePath<'a>,
    token: &Token,
) {
    if !path.skipped() {
        traverse_token_trivia(visitor, path, token);
    }
    if !path.skipped() {
        visitor.enter_interpreted_token(path, token);
    }
    if !path.skipped() {
        visitor.exit_interpreted_token(path, token);
    }
}

fn traverse_missing_token<'a>(
    visitor: &mut dyn Visitor<'a>,
    path: &mut NodePath<'a>,
    range: EffectiveRange,
    item: MissingTokenKind,
) {
    if !path.skipped() {
        visitor.enter_missing_token(path, range, item);
    }
    if !path.skipped() {
        visitor.exit_missing_token(path, range, item);
    }
}

fn traverse_skipped_token<'a>(
    visitor: &mut dyn Visitor<'a>,
    path: &mut NodePath<'a>,
    token: &Token,
    expected: MissingTokenKind,
) {
    if !path.skipped() {
        traverse_token_trivia(visitor, path, token);
    }
    if !path.skipped() {
        visitor.enter_skipped_token(path, token, expected);
    }
    if !path.skipped() {
        visitor.exit_skipped_token(path, token, expected);
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
        fn enter_expression(&mut self, _path: &mut NodePath<'a>, _expr: &mut Expression) {
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
