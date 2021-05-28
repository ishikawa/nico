use super::{CodeKind, EffectiveRange, MissingTokenKind, Scope, SyntaxToken, Trivia, TriviaKind};
use crate::arena::{BumpaloArena, BumpaloBox};
use crate::syntax::tree::*;
use crate::syntax::Token;
use std::cell::Cell;

pub struct NodePath<'a> {
    node: NodeKind<'a>,
    parent: BumpaloBox<'a, Cell<Option<&'a NodePath<'a>>>>,
    // Scopes. If the node is the root, these scopes point it even if exited.
    scope: BumpaloBox<'a, Cell<&'a Scope<'a>>>,
    main_scope: BumpaloBox<'a, Cell<&'a Scope<'a>>>,
    declarations: BumpaloBox<'a, Cell<&'a Scope<'a>>>,
    skipped: BumpaloBox<'a, Cell<bool>>,
    stopped: BumpaloBox<'a, Cell<bool>>,
}

impl<'a> NodePath<'a> {
    pub fn new(
        arena: &'a BumpaloArena,
        node: NodeKind<'a>,
        parent: Option<&'a NodePath<'a>>,
        scope: &'a Scope<'a>,
        main_scope: &'a Scope<'a>,
        declarations: &'a Scope<'a>,
    ) -> Self {
        Self {
            node,
            parent: BumpaloBox::new_in(Cell::new(parent), arena),
            scope: BumpaloBox::new_in(Cell::new(scope), arena),
            main_scope: BumpaloBox::new_in(Cell::new(main_scope), arena),
            declarations: BumpaloBox::new_in(Cell::new(declarations), arena),
            skipped: BumpaloBox::new_in(Cell::new(false), arena),
            stopped: BumpaloBox::new_in(Cell::new(false), arena),
        }
    }

    pub fn root_path(arena: &'a BumpaloArena, node: &'a Program<'a>) -> Self {
        Self::new(
            arena,
            NodeKind::Program(node),
            None,
            node.main_scope(),
            node.main_scope(),
            node.declarations_scope(),
        )
    }

    pub fn child_path(
        arena: &'a BumpaloArena,
        node: NodeKind<'a>,
        parent: &'a NodePath<'a>,
    ) -> Self {
        Self::new(
            arena,
            node,
            Some(parent),
            parent.scope.get(),
            parent.main_scope.get(),
            parent.declarations.get(),
        )
    }

    pub fn node(&self) -> &NodeKind<'a> {
        &self.node
    }

    /// Returns `true` if `skip()` or `stop()` invoked.
    fn skipped(&self) -> bool {
        self.skipped.get() || self.stopped.get()
    }

    /// skips traversing the children and `exit` of the current path.
    pub fn skip(&self) {
        self.skipped.replace(true);
    }

    /// stops traversing entirely.
    pub fn stop(&self) {
        self.stopped.replace(true);
    }

    pub fn parent(&self) -> Option<&'a NodePath<'a>> {
        self.parent.get()
    }

    pub fn expect_parent(&self) -> &'a NodePath<'a> {
        self.parent()
            .unwrap_or_else(|| panic!("parent must exist."))
    }

    pub fn scope(&self) -> &'a Scope<'a> {
        self.scope.get()
    }

    fn on_enter(&self) {
        match self.node {
            NodeKind::Block(block) => {
                self.scope.replace(block.scope());
            }
            NodeKind::CaseArm(arm) => {
                self.scope.replace(arm.scope());
            }
            NodeKind::StructDefinition(_) => {
                self.scope.replace(self.declarations.get());
            }
            NodeKind::FunctionDefinition(_) => {
                self.scope.replace(self.declarations.get());
            }
            _ => {}
        }
    }

    fn on_exit(&self) {
        match self.node {
            // Before binding completed, parent scope is `None`.
            NodeKind::Block(block) => {
                if let Some(scope) = block.scope().parent() {
                    self.scope.replace(scope);
                }
            }
            NodeKind::CaseArm(arm) => {
                if let Some(scope) = arm.scope().parent() {
                    self.scope.replace(scope);
                }
            }
            NodeKind::StructDefinition(_) => {
                self.scope.replace(self.main_scope.get());
            }
            NodeKind::FunctionDefinition(_) => {
                self.scope.replace(self.main_scope.get());
            }
            _ => {}
        }
    }
}

#[allow(unused_variables, unused_mut)]
pub trait Visitor<'a> {
    // Token
    fn enter_whitespace(&mut self, path: &'a NodePath<'a>, token: &Token, trivia: &Trivia) {}
    fn exit_whitespace(&mut self, path: &'a NodePath<'a>, token: &Token, trivia: &Trivia) {}

    fn enter_line_comment(
        &mut self,
        path: &'a NodePath<'a>,
        token: &Token,
        trivia: &Trivia,
        comment: &str,
    ) {
    }
    fn exit_line_comment(
        &mut self,
        path: &'a NodePath<'a>,
        token: &Token,
        trivia: &Trivia,
        comment: &str,
    ) {
    }

    fn enter_interpreted_token(&mut self, path: &'a NodePath<'a>, token: &Token) {}
    fn exit_interpreted_token(&mut self, path: &'a NodePath<'a>, token: &Token) {}

    fn enter_missing_token(
        &mut self,
        path: &'a NodePath<'a>,
        range: EffectiveRange,
        item: MissingTokenKind,
    ) {
    }
    fn exit_missing_token(
        &mut self,
        path: &'a NodePath<'a>,
        range: EffectiveRange,
        item: MissingTokenKind,
    ) {
    }

    fn enter_skipped_token(
        &mut self,
        path: &'a NodePath<'a>,
        token: &Token,
        expected: MissingTokenKind,
    ) {
    }
    fn exit_skipped_token(
        &mut self,
        path: &'a NodePath<'a>,
        token: &Token,
        expected: MissingTokenKind,
    ) {
    }

    // Node
    fn enter_program(&mut self, path: &'a NodePath<'a>, program: &'a Program<'a>) {}
    fn exit_program(&mut self, path: &'a NodePath<'a>, program: &'a Program<'a>) {}

    fn enter_top_level(&mut self, path: &'a NodePath<'a>, program: &'a TopLevel<'a>) {}
    fn exit_top_level(&mut self, path: &'a NodePath<'a>, program: &'a TopLevel<'a>) {}

    fn enter_block(&mut self, path: &'a NodePath<'a>, block: &'a Block<'a>) {}
    fn exit_block(&mut self, path: &'a NodePath<'a>, block: &'a Block<'a>) {}

    fn enter_identifier(&mut self, path: &'a NodePath<'a>, id: &'a Identifier<'a>) {}
    fn exit_identifier(&mut self, path: &'a NodePath<'a>, id: &'a Identifier<'a>) {}

    fn enter_struct_definition(
        &mut self,
        path: &'a NodePath<'a>,
        definition: &'a StructDefinition<'a>,
    ) {
    }
    fn exit_struct_definition(
        &mut self,
        path: &'a NodePath<'a>,
        definition: &'a StructDefinition<'a>,
    ) {
    }

    fn enter_function_definition(
        &mut self,
        path: &'a NodePath<'a>,
        definition: &'a FunctionDefinition<'a>,
    ) {
    }
    fn exit_function_definition(
        &mut self,
        path: &'a NodePath<'a>,
        definition: &'a FunctionDefinition<'a>,
    ) {
    }

    fn enter_function_parameter(
        &mut self,
        path: &'a NodePath<'a>,
        param: &'a FunctionParameter<'a>,
    ) {
    }
    fn exit_function_parameter(
        &mut self,
        path: &'a NodePath<'a>,
        param: &'a FunctionParameter<'a>,
    ) {
    }

    fn enter_type_field(&mut self, path: &'a NodePath<'a>, field: &'a TypeField<'a>) {}
    fn exit_type_field(&mut self, path: &'a NodePath<'a>, field: &'a TypeField<'a>) {}

    fn enter_type_annotation(
        &mut self,
        path: &'a NodePath<'a>,
        annotation: &'a TypeAnnotation<'a>,
    ) {
    }
    fn exit_type_annotation(&mut self, path: &'a NodePath<'a>, annotation: &'a TypeAnnotation<'a>) {
    }

    fn enter_statement(&mut self, path: &'a NodePath<'a>, statement: &'a Statement<'a>) {}
    fn exit_statement(&mut self, path: &'a NodePath<'a>, statement: &'a Statement<'a>) {}

    fn enter_variable_declaration(
        &mut self,
        path: &'a NodePath<'a>,
        declaration: &'a VariableDeclaration<'a>,
    ) {
    }
    fn exit_variable_declaration(
        &mut self,
        path: &'a NodePath<'a>,
        declaration: &'a VariableDeclaration<'a>,
    ) {
    }

    fn enter_case_arm(&mut self, path: &'a NodePath<'a>, arm: &'a CaseArm<'a>) {}
    fn exit_case_arm(&mut self, path: &'a NodePath<'a>, arm: &'a CaseArm<'a>) {}

    fn enter_value_field(&mut self, path: &'a NodePath<'a>, field: &'a ValueField<'a>) {}
    fn exit_value_field(&mut self, path: &'a NodePath<'a>, field: &'a ValueField<'a>) {}

    fn enter_grouped_expression(
        &mut self,
        path: &'a NodePath<'a>,
        expression: &'a GroupedExpression<'a>,
    ) {
    }
    fn exit_grouped_expression(
        &mut self,
        path: &'a NodePath<'a>,
        expression: &'a GroupedExpression<'a>,
    ) {
    }

    fn enter_expression(&mut self, path: &'a NodePath<'a>, expression: &'a Expression<'a>) {}
    fn exit_expression(&mut self, path: &'a NodePath<'a>, expression: &'a Expression<'a>) {}

    fn enter_integer_literal(&mut self, path: &'a NodePath<'a>, literal: &'a IntegerLiteral<'a>) {}
    fn exit_integer_literal(&mut self, path: &'a NodePath<'a>, literal: &'a IntegerLiteral<'a>) {}

    fn enter_string_literal(&mut self, path: &'a NodePath<'a>, literal: &'a StringLiteral<'a>) {}
    fn exit_string_literal(&mut self, path: &'a NodePath<'a>, literal: &'a StringLiteral<'a>) {}

    fn enter_struct_literal(&mut self, path: &'a NodePath<'a>, expr: &'a StructLiteral<'a>) {}
    fn exit_struct_literal(&mut self, path: &'a NodePath<'a>, expr: &'a StructLiteral<'a>) {}

    fn enter_variable_expression(
        &mut self,
        path: &'a NodePath<'a>,
        expr: &'a VariableExpression<'a>,
    ) {
    }
    fn exit_variable_expression(
        &mut self,
        path: &'a NodePath<'a>,
        expr: &'a VariableExpression<'a>,
    ) {
    }

    fn enter_binary_expression(&mut self, path: &'a NodePath<'a>, expr: &'a BinaryExpression<'a>) {}
    fn exit_binary_expression(&mut self, path: &'a NodePath<'a>, expr: &'a BinaryExpression<'a>) {}

    fn enter_unary_expression(
        &mut self,
        path: &'a NodePath<'a>,
        unary_expr: &'a UnaryExpression<'a>,
    ) {
    }
    fn exit_unary_expression(
        &mut self,
        path: &'a NodePath<'a>,
        unary_expr: &'a UnaryExpression<'a>,
    ) {
    }

    fn enter_subscript_expression(
        &mut self,
        path: &'a NodePath<'a>,
        subscript_expr: &'a SubscriptExpression<'a>,
    ) {
    }
    fn exit_subscript_expression(
        &mut self,
        path: &'a NodePath<'a>,
        subscript_expr: &'a SubscriptExpression<'a>,
    ) {
    }

    fn enter_call_expression(&mut self, path: &'a NodePath<'a>, call_expr: &'a CallExpression<'a>) {
    }
    fn exit_call_expression(&mut self, path: &'a NodePath<'a>, call_expr: &'a CallExpression<'a>) {}

    fn enter_member_expression(
        &mut self,
        path: &'a NodePath<'a>,
        member_expr: &'a MemberExpression<'a>,
    ) {
    }
    fn exit_member_expression(
        &mut self,
        path: &'a NodePath<'a>,
        member_expr: &'a MemberExpression<'a>,
    ) {
    }

    fn enter_array_expression(
        &mut self,
        path: &'a NodePath<'a>,
        array_expr: &'a ArrayExpression<'a>,
    ) {
    }
    fn exit_array_expression(
        &mut self,
        path: &'a NodePath<'a>,
        array_expr: &'a ArrayExpression<'a>,
    ) {
    }

    fn enter_if_expression(&mut self, path: &'a NodePath<'a>, if_expr: &'a IfExpression<'a>) {}
    fn exit_if_expression(&mut self, path: &'a NodePath<'a>, if_expr: &'a IfExpression<'a>) {}

    fn enter_case_expression(&mut self, path: &'a NodePath<'a>, case_expr: &'a CaseExpression<'a>) {
    }
    fn exit_case_expression(&mut self, path: &'a NodePath<'a>, case_expr: &'a CaseExpression<'a>) {}

    fn enter_pattern(&mut self, path: &'a NodePath<'a>, pattern: &'a Pattern<'a>) {}
    fn exit_pattern(&mut self, path: &'a NodePath<'a>, pattern: &'a Pattern<'a>) {}

    fn enter_variable_pattern(&mut self, path: &'a NodePath<'a>, pattern: &'a VariablePattern<'a>) {
    }
    fn exit_variable_pattern(&mut self, path: &'a NodePath<'a>, pattern: &'a VariablePattern<'a>) {}

    fn enter_value_field_pattern(
        &mut self,
        path: &'a NodePath<'a>,
        pattern: &'a ValueFieldPattern<'a>,
    ) {
    }
    fn exit_value_field_pattern(
        &mut self,
        path: &'a NodePath<'a>,
        pattern: &'a ValueFieldPattern<'a>,
    ) {
    }
}

pub fn traverse<'a>(
    arena: &'a BumpaloArena,
    visitor: &mut dyn Visitor<'a>,
    program: &'a Program<'a>,
) {
    let path = arena.alloc(NodePath::root_path(arena, program));
    traverse_path(arena, visitor, path);
}

fn traverse_path<'a>(
    arena: &'a BumpaloArena,
    visitor: &mut dyn Visitor<'a>,
    path: &'a NodePath<'a>,
) {
    path.on_enter();

    if !path.skipped() {
        dispatch_enter(visitor, path);
    }
    if !path.skipped() {
        traverse_children(arena, visitor, path);
    }
    if !path.skipped() {
        dispatch_exit(visitor, path);
    }

    path.on_exit();
}

fn dispatch_enter<'a>(visitor: &mut dyn Visitor<'a>, path: &'a NodePath<'a>) {
    let node = path.node().clone();

    match node {
        NodeKind::Program(kind) => {
            visitor.enter_program(path, kind);
        }
        NodeKind::TopLevel(kind) => {
            visitor.enter_top_level(path, kind);
        }
        NodeKind::Block(kind) => {
            visitor.enter_block(path, kind);
        }
        NodeKind::Identifier(kind) => {
            visitor.enter_identifier(path, kind);
        }
        NodeKind::StructDefinition(kind) => {
            visitor.enter_struct_definition(path, kind);
        }
        NodeKind::FunctionDefinition(kind) => {
            visitor.enter_function_definition(path, kind);
        }
        NodeKind::TypeField(kind) => {
            visitor.enter_type_field(path, kind);
        }
        NodeKind::TypeAnnotation(kind) => {
            visitor.enter_type_annotation(path, kind);
        }
        NodeKind::FunctionParameter(kind) => {
            visitor.enter_function_parameter(path, kind);
        }
        NodeKind::Statement(kind) => {
            visitor.enter_statement(path, kind);
        }
        NodeKind::VariableDeclaration(kind) => {
            visitor.enter_variable_declaration(path, kind);
        }
        NodeKind::ValueField(kind) => {
            visitor.enter_value_field(path, kind);
        }
        // Expression
        NodeKind::IntegerLiteral(value) => {
            visitor.enter_integer_literal(path, value);
        }
        NodeKind::StringLiteral(value) => {
            visitor.enter_string_literal(path, value);
        }
        NodeKind::VariableExpression(kind) => {
            visitor.enter_variable_expression(path, kind);
        }
        NodeKind::BinaryExpression(kind) => {
            visitor.enter_binary_expression(path, kind);
        }
        NodeKind::UnaryExpression(kind) => {
            visitor.enter_unary_expression(path, kind);
        }
        NodeKind::SubscriptExpression(kind) => {
            visitor.enter_subscript_expression(path, kind);
        }
        NodeKind::CallExpression(kind) => {
            visitor.enter_call_expression(path, kind);
        }
        NodeKind::MemberExpression(kind) => {
            visitor.enter_member_expression(path, kind);
        }
        NodeKind::ArrayExpression(kind) => {
            visitor.enter_array_expression(path, kind);
        }
        NodeKind::StructLiteral(kind) => {
            visitor.enter_struct_literal(path, kind);
        }
        NodeKind::IfExpression(kind) => {
            visitor.enter_if_expression(path, kind);
        }
        NodeKind::CaseExpression(kind) => {
            visitor.enter_case_expression(path, kind);
        }
        NodeKind::CaseArm(kind) => {
            visitor.enter_case_arm(path, kind);
        }
        NodeKind::GroupedExpression(kind) => {
            visitor.enter_grouped_expression(path, kind);
        }
        NodeKind::Expression(expr) => {
            visitor.enter_expression(path, expr);
        }
        // Pattern
        NodeKind::Pattern(kind) => {
            visitor.enter_pattern(path, kind);
        }
        NodeKind::VariablePattern(kind) => {
            visitor.enter_variable_pattern(path, kind);
        }
        NodeKind::ArrayPattern(_) => { /* todo */ }
        NodeKind::RestPattern(_) => { /* todo */ }
        NodeKind::StructPattern(_) => { /* todo */ }
        NodeKind::ValueFieldPattern(kind) => {
            visitor.enter_value_field_pattern(path, kind);
        }
    }
}

fn dispatch_exit<'a>(visitor: &mut dyn Visitor<'a>, path: &'a NodePath<'a>) {
    let node = path.node().clone();

    match node {
        NodeKind::Program(kind) => {
            visitor.exit_program(path, kind);
        }
        NodeKind::TopLevel(kind) => {
            visitor.exit_top_level(path, kind);
        }
        NodeKind::Block(kind) => {
            visitor.exit_block(path, kind);
        }
        NodeKind::Identifier(kind) => {
            visitor.exit_identifier(path, kind);
        }
        NodeKind::StructDefinition(kind) => {
            visitor.exit_struct_definition(path, kind);
        }
        NodeKind::FunctionDefinition(kind) => {
            visitor.exit_function_definition(path, kind);
        }
        NodeKind::TypeField(kind) => {
            visitor.exit_type_field(path, kind);
        }
        NodeKind::TypeAnnotation(kind) => {
            visitor.exit_type_annotation(path, kind);
        }
        NodeKind::FunctionParameter(kind) => {
            visitor.exit_function_parameter(path, kind);
        }
        NodeKind::Statement(kind) => {
            visitor.exit_statement(path, kind);
        }
        NodeKind::VariableDeclaration(kind) => {
            visitor.exit_variable_declaration(path, kind);
        }
        NodeKind::ValueField(kind) => {
            visitor.exit_value_field(path, kind);
        }
        // Expression
        NodeKind::IntegerLiteral(value) => {
            visitor.exit_integer_literal(path, value);
        }
        NodeKind::StringLiteral(value) => {
            visitor.exit_string_literal(path, value);
        }
        NodeKind::VariableExpression(kind) => {
            visitor.exit_variable_expression(path, kind);
        }
        NodeKind::BinaryExpression(kind) => {
            visitor.exit_binary_expression(path, kind);
        }
        NodeKind::UnaryExpression(kind) => {
            visitor.exit_unary_expression(path, kind);
        }
        NodeKind::SubscriptExpression(kind) => {
            visitor.exit_subscript_expression(path, kind);
        }
        NodeKind::MemberExpression(kind) => {
            visitor.exit_member_expression(path, kind);
        }
        NodeKind::CallExpression(kind) => {
            visitor.exit_call_expression(path, kind);
        }
        NodeKind::ArrayExpression(kind) => {
            visitor.exit_array_expression(path, kind);
        }
        NodeKind::StructLiteral(kind) => {
            visitor.exit_struct_literal(path, kind);
        }
        NodeKind::IfExpression(kind) => {
            visitor.exit_if_expression(path, kind);
        }
        NodeKind::CaseExpression(kind) => {
            visitor.exit_case_expression(path, kind);
        }
        NodeKind::CaseArm(kind) => {
            visitor.exit_case_arm(path, kind);
        }
        NodeKind::GroupedExpression(kind) => {
            visitor.exit_grouped_expression(path, kind);
        }
        NodeKind::Expression(expr) => {
            visitor.exit_expression(path, expr);
        }
        // Pattern
        NodeKind::Pattern(kind) => {
            visitor.exit_pattern(path, kind);
        }
        NodeKind::VariablePattern(kind) => {
            visitor.exit_variable_pattern(path, kind);
        }
        NodeKind::ArrayPattern(_) => { /* todo */ }
        NodeKind::RestPattern(_) => { /* todo */ }
        NodeKind::StructPattern(_) => { /* todo */ }
        NodeKind::ValueFieldPattern(kind) => {
            visitor.exit_value_field_pattern(path, kind);
        }
    }
}

fn traverse_children<'a>(
    arena: &'a BumpaloArena,
    visitor: &mut dyn Visitor<'a>,
    path: &'a NodePath<'a>,
) {
    let node = path.node().clone();

    for kind in node.code() {
        if path.skipped() {
            break;
        }

        match kind {
            CodeKind::Node(node) => {
                let child_path = arena.alloc(NodePath::child_path(arena, node.clone(), path));
                traverse_path(arena, visitor, child_path);

                // Propagates `stop`
                path.stopped.replace(child_path.stopped.get());
            }
            CodeKind::SyntaxToken(token) => match token {
                SyntaxToken::Interpreted(token) => traverse_interpreted_token(visitor, path, token),
                SyntaxToken::Missing { range, item } => {
                    traverse_missing_token(visitor, path, *range, *item)
                }
                SyntaxToken::Skipped { token, expected } => {
                    traverse_skipped_token(visitor, path, token, *expected)
                }
            },
        }
    }
}

fn traverse_token_trivia<'a>(visitor: &mut dyn Visitor<'a>, path: &'a NodePath<'a>, token: &Token) {
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
    path: &'a NodePath<'a>,
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
    path: &'a NodePath<'a>,
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
    path: &'a NodePath<'a>,
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
    use crate::arena::BumpaloArena;
    use crate::syntax::Parser;

    // count expressions
    #[derive(Debug, Default)]
    struct ExpressionCounter {
        number_of_expressions: i32,
    }

    impl<'a> Visitor<'a> for ExpressionCounter {
        fn enter_expression(&mut self, _path: &'a NodePath<'a>, _expr: &'a Expression<'a>) {
            self.number_of_expressions += 1;
        }
    }

    #[test]
    fn number_integer() {
        let mut visitor = ExpressionCounter::default();
        let arena = BumpaloArena::new();
        let program = Parser::parse_string(&arena, "42 + 55");

        traverse(&arena, &mut visitor, &program);
        assert_eq!(visitor.number_of_expressions, 3);
    }

    // stop()
    #[derive(Debug, Default)]
    struct StopInExpression {
        stop_at: i32,
        enter_program: i32,
        exit_program: i32,
        enter_statement: i32,
        exit_statement: i32,
        enter_expression: i32,
        exit_expression: i32,
    }

    impl<'a> Visitor<'a> for StopInExpression {
        fn enter_program(&mut self, _path: &'a NodePath<'a>, _program: &'a Program<'a>) {
            self.enter_program += 1;
        }

        fn exit_program(&mut self, _path: &'a NodePath<'a>, _program: &'a Program<'a>) {
            self.exit_program += 1;
        }

        fn enter_statement(&mut self, _path: &'a NodePath<'a>, _statement: &'a Statement<'a>) {
            self.enter_statement += 1;
        }

        fn exit_statement(&mut self, _path: &'a NodePath<'a>, _statement: &'a Statement<'a>) {
            self.exit_statement += 1;
        }

        fn enter_expression(&mut self, path: &'a NodePath<'a>, _expression: &'a Expression<'a>) {
            if self.enter_expression == self.stop_at {
                path.stop();
            }
            self.enter_expression += 1;
        }

        fn exit_expression(&mut self, _path: &'a NodePath<'a>, _expression: &'a Expression<'a>) {
            self.exit_expression += 1;
        }
    }

    #[test]
    fn never_stop_traversal() {
        let mut visitor = StopInExpression::default();
        visitor.stop_at = -1; // never stop

        let arena = BumpaloArena::new();
        let program = Parser::parse_string(&arena, "42 + 55");

        traverse(&arena, &mut visitor, &program);
        assert_eq!(visitor.enter_program, 1);
        assert_eq!(visitor.enter_statement, 1);
        assert_eq!(visitor.enter_expression, 3);

        assert_eq!(visitor.exit_program, 1);
        assert_eq!(visitor.exit_statement, 1);
        assert_eq!(visitor.exit_expression, 3);
    }

    #[test]
    fn stop_at_2nd_expression() {
        let mut visitor = StopInExpression::default();
        visitor.stop_at = 1; // Stop at 2nd expression

        let arena = BumpaloArena::new();
        let program = Parser::parse_string(&arena, "42 + 55");

        traverse(&arena, &mut visitor, &program);
        assert_eq!(visitor.enter_program, 1);
        assert_eq!(visitor.enter_statement, 1);
        assert_eq!(visitor.enter_expression, 2);

        assert_eq!(visitor.exit_program, 0);
        assert_eq!(visitor.exit_statement, 0);
        assert_eq!(visitor.exit_expression, 0);
    }

    #[test]
    fn stop_at_last_expression() {
        let mut visitor = StopInExpression::default();
        visitor.stop_at = 2; // Stop at 2nd expression

        let arena = BumpaloArena::new();
        let program = Parser::parse_string(&arena, "42 + 55");

        traverse(&arena, &mut visitor, &program);
        assert_eq!(visitor.enter_program, 1);
        assert_eq!(visitor.enter_statement, 1);
        assert_eq!(visitor.enter_expression, 3);

        assert_eq!(visitor.exit_program, 0);
        assert_eq!(visitor.exit_statement, 0);
        assert_eq!(visitor.exit_expression, 1);
    }
}
