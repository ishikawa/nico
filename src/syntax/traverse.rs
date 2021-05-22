use std::{
    cell::RefCell,
    rc::{Rc, Weak},
};

use crate::syntax::Token;
use crate::{syntax::tree::*, util::wrap};

use super::{EffectiveRange, MissingTokenKind, Scope, SyntaxToken, Trivia, TriviaKind};

pub struct NodePath<'a> {
    skipped: bool,
    stopped: bool,
    node: NodeKind<'a>,
    scope: Weak<RefCell<Scope>>,
    main_scope: Weak<RefCell<Scope>>,
    declarations: Weak<RefCell<Scope>>,
    parent: Option<Rc<RefCell<NodePath<'a>>>>,
}

impl<'a> NodePath<'a> {
    pub fn new(node: &NodeKind<'a>) -> Self {
        Self {
            skipped: false,
            stopped: false,
            node: node.clone(),
            parent: None,
            declarations: Weak::new(),
            scope: Weak::new(),
            main_scope: Weak::new(),
        }
    }

    pub fn child_path(node: &NodeKind<'a>, parent: &Rc<RefCell<NodePath<'a>>>) -> Self {
        let borrowed_parent = parent.borrow();

        Self {
            skipped: false,
            stopped: false,
            node: node.clone(),
            parent: Some(Rc::clone(parent)),
            scope: Weak::clone(&borrowed_parent.scope),
            main_scope: Weak::clone(&borrowed_parent.main_scope),
            declarations: Weak::clone(&borrowed_parent.declarations),
        }
    }

    pub fn node(&self) -> &NodeKind<'a> {
        &self.node
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
        match self.node {
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
        match self.node {
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
    fn enter_whitespace(&mut self, path: &mut NodePath<'a>, token: &'a Token, trivia: &Trivia) {}
    fn exit_whitespace(&mut self, path: &mut NodePath<'a>, token: &'a Token, trivia: &Trivia) {}

    fn enter_line_comment(
        &mut self,
        path: &mut NodePath<'a>,
        token: &'a Token,
        trivia: &'a Trivia,
        comment: &'a str,
    ) {
    }
    fn exit_line_comment(
        &mut self,
        path: &mut NodePath<'a>,
        token: &'a Token,
        trivia: &'a Trivia,
        comment: &'a str,
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
        token: &'a Token,
        expected: MissingTokenKind,
    ) {
    }
    fn exit_skipped_token(
        &mut self,
        path: &mut NodePath<'a>,
        token: &'a Token,
        expected: MissingTokenKind,
    ) {
    }

    // Node
    fn enter_program(&mut self, path: &mut NodePath<'a>, program: &'a Program<'a>) {}
    fn exit_program(&mut self, path: &mut NodePath<'a>, program: &'a Program<'a>) {}

    fn enter_block(&mut self, path: &mut NodePath<'a>, block: &'a Block<'a>) {}
    fn exit_block(&mut self, path: &mut NodePath<'a>, block: &'a Block<'a>) {}

    fn enter_identifier(&mut self, path: &mut NodePath<'a>, id: &'a Identifier<'a>) {}
    fn exit_identifier(&mut self, path: &mut NodePath<'a>, id: &'a Identifier<'a>) {}

    fn enter_struct_definition(
        &mut self,
        path: &mut NodePath<'a>,
        definition: &'a StructDefinition<'a>,
    ) {
    }
    fn exit_struct_definition(
        &mut self,
        path: &mut NodePath<'a>,
        definition: &'a StructDefinition<'a>,
    ) {
    }

    fn enter_function_definition(
        &mut self,
        path: &mut NodePath<'a>,
        definition: &'a FunctionDefinition<'a>,
    ) {
    }
    fn exit_function_definition(
        &mut self,
        path: &mut NodePath<'a>,
        definition: &'a FunctionDefinition<'a>,
    ) {
    }

    fn enter_function_parameter(
        &mut self,
        path: &mut NodePath<'a>,
        param: &'a FunctionParameter<'a>,
    ) {
    }
    fn exit_function_parameter(
        &mut self,
        path: &mut NodePath<'a>,
        param: &'a FunctionParameter<'a>,
    ) {
    }

    fn enter_type_field(&mut self, path: &mut NodePath<'a>, field: &'a TypeField<'a>) {}
    fn exit_type_field(&mut self, path: &mut NodePath<'a>, field: &'a TypeField<'a>) {}

    fn enter_type_annotation(
        &mut self,
        path: &mut NodePath<'a>,
        annotation: &'a TypeAnnotation<'a>,
    ) {
    }
    fn exit_type_annotation(
        &mut self,
        path: &mut NodePath<'a>,
        annotation: &'a TypeAnnotation<'a>,
    ) {
    }

    fn enter_statement(&mut self, path: &mut NodePath<'a>, statement: &'a Statement<'a>) {}
    fn exit_statement(&mut self, path: &mut NodePath<'a>, statement: &'a Statement<'a>) {}

    fn enter_variable_declaration(
        &mut self,
        path: &mut NodePath<'a>,
        declaration: &'a VariableDeclaration<'a>,
    ) {
    }
    fn exit_variable_declaration(
        &mut self,
        path: &mut NodePath<'a>,
        declaration: &'a VariableDeclaration<'a>,
    ) {
    }

    fn enter_case_arm(&mut self, path: &mut NodePath<'a>, arm: &'a CaseArm<'a>) {}
    fn exit_case_arm(&mut self, path: &mut NodePath<'a>, arm: &'a CaseArm<'a>) {}

    fn enter_pattern(&mut self, path: &mut NodePath<'a>, pattern: &'a Pattern<'a>) {}
    fn exit_pattern(&mut self, path: &mut NodePath<'a>, pattern: &'a Pattern<'a>) {}

    fn enter_value_field(&mut self, path: &mut NodePath<'a>, field: &'a ValueField<'a>) {}
    fn exit_value_field(&mut self, path: &mut NodePath<'a>, field: &'a ValueField<'a>) {}

    fn enter_value_field_pattern(
        &mut self,
        path: &mut NodePath<'a>,
        pattern: &'a ValueFieldPattern<'a>,
    ) {
    }
    fn exit_value_field_pattern(
        &mut self,
        path: &mut NodePath<'a>,
        pattern: &'a ValueFieldPattern<'a>,
    ) {
    }

    fn enter_expression(&mut self, path: &mut NodePath<'a>, expression: &'a Expression<'a>) {}
    fn exit_expression(&mut self, path: &mut NodePath<'a>, expression: &'a Expression<'a>) {}

    fn enter_integer_literal(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        literal: &'a IntegerLiteral,
    ) {
    }
    fn exit_integer_literal(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        literal: &'a IntegerLiteral,
    ) {
    }

    fn enter_string_literal(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        literal: &'a StringLiteral<'a>,
    ) {
    }
    fn exit_string_literal(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        literal: &'a StringLiteral<'a>,
    ) {
    }

    fn enter_struct_literal(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        value: &'a StructLiteral<'a>,
    ) {
    }
    fn exit_struct_literal(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        value: &'a StructLiteral<'a>,
    ) {
    }

    fn enter_variable(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        id: &'a Identifier<'a>,
    ) {
    }
    fn exit_variable(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        id: &'a Identifier<'a>,
    ) {
    }

    fn enter_binary_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        bin_expr: &'a BinaryExpression<'a>,
    ) {
    }
    fn exit_binary_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        bin_expr: &'a BinaryExpression<'a>,
    ) {
    }

    fn enter_unary_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        unary_expr: &'a UnaryExpression<'a>,
    ) {
    }
    fn exit_unary_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        unary_expr: &'a UnaryExpression<'a>,
    ) {
    }

    fn enter_subscript_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        subscript_expr: &'a SubscriptExpression<'a>,
    ) {
    }
    fn exit_subscript_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        subscript_expr: &'a SubscriptExpression<'a>,
    ) {
    }

    fn enter_call_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        call_expr: &'a CallExpression<'a>,
    ) {
    }
    fn exit_call_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        call_expr: &'a CallExpression<'a>,
    ) {
    }

    fn enter_access_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        member_expr: &'a MemberExpression<'a>,
    ) {
    }
    fn exit_access_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        member_expr: &'a MemberExpression<'a>,
    ) {
    }

    fn enter_array_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        array_expr: &'a ArrayExpression<'a>,
    ) {
    }
    fn exit_array_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        array_expr: &'a ArrayExpression<'a>,
    ) {
    }

    fn enter_if_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        if_expr: &'a IfExpression<'a>,
    ) {
    }
    fn exit_if_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        if_expr: &'a IfExpression<'a>,
    ) {
    }

    fn enter_case_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        case_expr: &'a CaseExpression<'a>,
    ) {
    }
    fn exit_case_expression(
        &mut self,
        path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        case_expr: &'a CaseExpression<'a>,
    ) {
    }
}

pub fn traverse<'a>(visitor: &mut dyn Visitor<'a>, program: &'a Program<'a>) {
    let path = wrap(NodePath::new(&NodeKind::Program(program)));
    traverse_path(visitor, &path);
}

fn traverse_path<'a>(visitor: &mut dyn Visitor<'a>, path: &Rc<RefCell<NodePath<'a>>>) {
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

fn dispatch_enter<'a>(visitor: &mut dyn Visitor<'a>, path: &Rc<RefCell<NodePath<'a>>>) {
    let mut path = &mut path.borrow_mut();
    let node = path.node().clone();

    match node {
        NodeKind::Program(_) => {
            visitor.enter_program(&mut path, &node.program().unwrap());
        }
        NodeKind::Block(_) => {
            visitor.enter_block(&mut path, &node.block().unwrap());
        }
        NodeKind::Identifier(_) => {
            visitor.enter_identifier(&mut path, &node.identifier().unwrap());
        }
        NodeKind::StructDefinition(_) => {
            visitor.enter_struct_definition(&mut path, &node.struct_definition().unwrap());
        }
        NodeKind::FunctionDefinition(_) => {
            visitor.enter_function_definition(&mut path, &node.function_definition().unwrap());
        }
        NodeKind::TypeField(_) => {
            visitor.enter_type_field(&mut path, &node.type_field().unwrap());
        }
        NodeKind::TypeAnnotation(_) => {
            visitor.enter_type_annotation(&mut path, &node.type_annotation().unwrap());
        }
        NodeKind::FunctionParameter(_) => {
            visitor.enter_function_parameter(&mut path, &node.function_parameter().unwrap());
        }
        NodeKind::Statement(_) => {
            visitor.enter_statement(&mut path, &node.statement().unwrap());
        }
        NodeKind::VariableDeclaration(_) => {
            visitor.enter_variable_declaration(&mut path, &node.variable_declaration().unwrap());
        }
        NodeKind::CaseArm(_) => {
            visitor.enter_case_arm(&mut path, &node.case_arm().unwrap());
        }
        NodeKind::Pattern(_) => {
            visitor.enter_pattern(&mut path, &node.pattern().unwrap());
        }
        NodeKind::ValueField(_) => {
            visitor.enter_value_field(&mut path, &node.struct_field().unwrap());
        }
        NodeKind::ValueFieldPattern(_) => {
            visitor.enter_value_field_pattern(&mut path, &node.struct_field_pattern().unwrap());
        }
        NodeKind::Expression(_) => {
            let expr = node.expression().unwrap();
            visitor.enter_expression(&mut path, &expr);

            if !path.skipped() {
                match expr.kind() {
                    ExpressionKind::IntegerLiteral(value) => {
                        visitor.enter_integer_literal(&mut path, expr, value);
                    }
                    ExpressionKind::StringLiteral(value) => {
                        visitor.enter_string_literal(&mut path, expr, value);
                    }
                    ExpressionKind::StructLiteral(kind) => {
                        visitor.enter_struct_literal(&mut path, expr, kind);
                    }
                    ExpressionKind::VariableExpression(id) => {
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
    let node = path.node().clone();

    match node {
        NodeKind::Program(_) => {
            visitor.exit_program(&mut path, &node.program().unwrap());
        }
        NodeKind::Block(_) => {
            visitor.exit_block(&mut path, &node.block().unwrap());
        }
        NodeKind::Identifier(_) => {
            visitor.exit_identifier(&mut path, &node.identifier().unwrap());
        }
        NodeKind::StructDefinition(_) => {
            visitor.exit_struct_definition(&mut path, &node.struct_definition().unwrap());
        }
        NodeKind::FunctionDefinition(_) => {
            visitor.exit_function_definition(&mut path, &node.function_definition().unwrap());
        }
        NodeKind::TypeField(_) => {
            visitor.exit_type_field(&mut path, &node.type_field().unwrap());
        }
        NodeKind::TypeAnnotation(_) => {
            visitor.exit_type_annotation(&mut path, &node.type_annotation().unwrap());
        }
        NodeKind::FunctionParameter(_) => {
            visitor.exit_function_parameter(&mut path, &node.function_parameter().unwrap());
        }
        NodeKind::Statement(_) => {
            visitor.exit_statement(&mut path, &node.statement().unwrap());
        }
        NodeKind::VariableDeclaration(_) => {
            visitor.exit_variable_declaration(&mut path, &node.variable_declaration().unwrap());
        }
        NodeKind::Pattern(_) => {
            visitor.exit_pattern(&mut path, &node.pattern().unwrap());
        }
        NodeKind::CaseArm(_) => {
            visitor.exit_case_arm(&mut path, &node.case_arm().unwrap());
        }
        NodeKind::ValueField(_) => {
            visitor.exit_value_field(&mut path, &node.struct_field().unwrap());
        }
        NodeKind::ValueFieldPattern(_) => {
            visitor.exit_value_field_pattern(&mut path, &node.struct_field_pattern().unwrap());
        }
        NodeKind::Expression(_) => {
            let expr = node.expression().unwrap();
            visitor.exit_expression(&mut path, &expr);

            if !path.skipped() {
                match expr.kind() {
                    ExpressionKind::IntegerLiteral(value) => {
                        visitor.exit_integer_literal(&mut path, expr, value);
                    }
                    ExpressionKind::StringLiteral(value) => {
                        visitor.exit_string_literal(&mut path, expr, value);
                    }
                    ExpressionKind::VariableExpression(id) => {
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

fn traverse_children<'a>(visitor: &mut dyn Visitor<'a>, path: &Rc<RefCell<NodePath<'a>>>) {
    let node = path.borrow().node().clone();

    for kind in node.code() {
        if path.borrow().skipped() {
            break;
        }

        match kind {
            CodeKind::Node(node) => {
                let child_path = wrap(NodePath::child_path(node, &path));
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
    token: &'a Token,
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
    token: &'a Token,
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
    token: &'a Token,
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
        fn enter_expression(&mut self, _path: &mut NodePath<'a>, _expr: &'a Expression<'a>) {
            self.number_of_expressions += 1;
        }
    }

    #[test]
    fn number_integer() {
        let mut visitor = NodeCounter::default();
        let tree = Ast::new();
        let program = Parser::parse_string(&tree, "42");

        traverse(&mut visitor, &program);
        assert_eq!(visitor.number_of_expressions, 1);
    }
}
