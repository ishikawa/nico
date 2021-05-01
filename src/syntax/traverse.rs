use std::{
    cell::RefCell,
    rc::{Rc, Weak},
};

use crate::syntax::Token;
use crate::{syntax::tree::*, util::wrap};

use super::{EffectiveRange, MissingTokenKind, Scope, SyntaxToken, Trivia, TriviaKind};

pub struct NodePath {
    skipped: bool,
    node: NodeKind,
    scope: Weak<RefCell<Scope>>,
    main_scope: Weak<RefCell<Scope>>,
    declarations: Weak<RefCell<Scope>>,
    parent: Option<Rc<RefCell<NodePath>>>,
}

impl NodePath {
    pub fn child(node: &NodeKind, parent: Option<Rc<RefCell<NodePath>>>) -> Self {
        if let Some(ref parent) = parent {
            let borrowed_parent = parent.borrow();
            Self {
                skipped: false,
                node: node.clone(),
                parent: Some(Rc::clone(parent)),
                scope: Weak::clone(&borrowed_parent.scope),
                main_scope: Weak::clone(&borrowed_parent.main_scope),
                declarations: Weak::clone(&borrowed_parent.declarations),
            }
        } else {
            Self {
                skipped: false,
                node: node.clone(),
                parent: None,
                declarations: Weak::new(),
                scope: Weak::new(),
                main_scope: Weak::new(),
            }
        }
    }

    pub fn node(&self) -> &NodeKind {
        &self.node
    }

    /// skips traversing the children and `exit` of the current path.
    pub fn skip(&mut self) {
        self.skipped = true;
    }

    pub fn parent(&self) -> Option<Rc<RefCell<NodePath>>> {
        self.parent.as_ref().map(Rc::clone)
    }

    pub fn scope(&self) -> Option<Rc<RefCell<Scope>>> {
        self.scope.upgrade()
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
pub trait Visitor {
    // Token
    fn enter_whitespace(&mut self, path: &mut NodePath, token: &Token, trivia: &Trivia) {}
    fn exit_whitespace(&mut self, path: &mut NodePath, token: &Token, trivia: &Trivia) {}

    fn enter_line_comment(
        &mut self,
        path: &mut NodePath,
        token: &Token,
        trivia: &Trivia,
        comment: &str,
    ) {
    }
    fn exit_line_comment(
        &mut self,
        path: &mut NodePath,
        token: &Token,
        trivia: &Trivia,
        comment: &str,
    ) {
    }

    fn enter_interpreted_token(&mut self, path: &mut NodePath, token: &Token) {}
    fn exit_interpreted_token(&mut self, path: &mut NodePath, token: &Token) {}

    fn enter_missing_token(
        &mut self,
        path: &mut NodePath,
        range: EffectiveRange,
        item: MissingTokenKind,
    ) {
    }
    fn exit_missing_token(
        &mut self,
        path: &mut NodePath,
        range: EffectiveRange,
        item: MissingTokenKind,
    ) {
    }

    fn enter_skipped_token(
        &mut self,
        path: &mut NodePath,
        token: &Token,
        expected: MissingTokenKind,
    ) {
    }
    fn exit_skipped_token(
        &mut self,
        path: &mut NodePath,
        token: &Token,
        expected: MissingTokenKind,
    ) {
    }

    // Node
    fn enter_program(&mut self, path: &mut NodePath, program: &Program) {}
    fn exit_program(&mut self, path: &mut NodePath, program: &Program) {}

    fn enter_block(&mut self, path: &mut NodePath, block: &Block) {}
    fn exit_block(&mut self, path: &mut NodePath, block: &Block) {}

    fn enter_identifier(&mut self, path: &mut NodePath, id: &Identifier) {}
    fn exit_identifier(&mut self, path: &mut NodePath, id: &Identifier) {}

    fn enter_struct_definition(&mut self, path: &mut NodePath, definition: &StructDefinition) {}
    fn exit_struct_definition(&mut self, path: &mut NodePath, definition: &StructDefinition) {}

    fn enter_function_definition(&mut self, path: &mut NodePath, definition: &FunctionDefinition) {}
    fn exit_function_definition(&mut self, path: &mut NodePath, definition: &FunctionDefinition) {}

    fn enter_function_parameter(&mut self, path: &mut NodePath, param: &FunctionParameter) {}
    fn exit_function_parameter(&mut self, path: &mut NodePath, param: &FunctionParameter) {}

    fn enter_type_field(&mut self, path: &mut NodePath, field: &TypeField) {}
    fn exit_type_field(&mut self, path: &mut NodePath, field: &TypeField) {}

    fn enter_type_annotation(&mut self, path: &mut NodePath, annotation: &TypeAnnotation) {}
    fn exit_type_annotation(&mut self, path: &mut NodePath, annotation: &TypeAnnotation) {}

    fn enter_statement(&mut self, path: &mut NodePath, statement: &Statement) {}
    fn exit_statement(&mut self, path: &mut NodePath, statement: &Statement) {}

    fn enter_variable_declaration(
        &mut self,
        path: &mut NodePath,
        declaration: &VariableDeclaration,
    ) {
    }
    fn exit_variable_declaration(
        &mut self,
        path: &mut NodePath,
        declaration: &VariableDeclaration,
    ) {
    }

    fn enter_case_arm(&mut self, path: &mut NodePath, arm: &CaseArm) {}
    fn exit_case_arm(&mut self, path: &mut NodePath, arm: &CaseArm) {}

    fn enter_pattern(&mut self, path: &mut NodePath, pattern: &Pattern) {}
    fn exit_pattern(&mut self, path: &mut NodePath, pattern: &Pattern) {}

    fn enter_struct_field(&mut self, path: &mut NodePath, pattern: &StructField) {}
    fn exit_struct_field(&mut self, path: &mut NodePath, pattern: &StructField) {}

    fn enter_struct_field_pattern(&mut self, path: &mut NodePath, pattern: &StructFieldPattern) {}
    fn exit_struct_field_pattern(&mut self, path: &mut NodePath, pattern: &StructFieldPattern) {}

    fn enter_expression(&mut self, path: &mut NodePath, expression: &Expression) {}
    fn exit_expression(&mut self, path: &mut NodePath, expression: &Expression) {}

    fn enter_integer_literal(&mut self, path: &mut NodePath, literal: i32) {}
    fn exit_integer_literal(&mut self, path: &mut NodePath, literal: i32) {}

    fn enter_string_literal(&mut self, path: &mut NodePath, literal: Option<&str>) {}
    fn exit_string_literal(&mut self, path: &mut NodePath, literal: Option<&str>) {}

    fn enter_struct_literal(&mut self, path: &mut NodePath, value: &StructLiteral) {}
    fn exit_struct_literal(&mut self, path: &mut NodePath, value: &StructLiteral) {}

    fn enter_variable(&mut self, path: &mut NodePath, id: &Identifier) {}
    fn exit_variable(&mut self, path: &mut NodePath, id: &Identifier) {}

    fn enter_binary_expression(&mut self, path: &mut NodePath, expr: &BinaryExpression) {}
    fn exit_binary_expression(&mut self, path: &mut NodePath, expr: &BinaryExpression) {}

    fn enter_unary_expression(&mut self, path: &mut NodePath, expr: &UnaryExpression) {}
    fn exit_unary_expression(&mut self, path: &mut NodePath, expr: &UnaryExpression) {}

    fn enter_subscript_expression(&mut self, path: &mut NodePath, expr: &SubscriptExpression) {}
    fn exit_subscript_expression(&mut self, path: &mut NodePath, expr: &SubscriptExpression) {}

    fn enter_call_expression(&mut self, path: &mut NodePath, expr: &CallExpression) {}
    fn exit_call_expression(&mut self, path: &mut NodePath, expr: &CallExpression) {}

    fn enter_access_expression(&mut self, path: &mut NodePath, expr: &MemberExpression) {}
    fn exit_access_expression(&mut self, path: &mut NodePath, expr: &MemberExpression) {}

    fn enter_array_expression(&mut self, path: &mut NodePath, expr: &ArrayExpression) {}
    fn exit_array_expression(&mut self, path: &mut NodePath, expr: &ArrayExpression) {}

    fn enter_if_expression(&mut self, path: &mut NodePath, expr: &IfExpression) {}
    fn exit_if_expression(&mut self, path: &mut NodePath, expr: &IfExpression) {}

    fn enter_case_expression(&mut self, path: &mut NodePath, expr: &CaseExpression) {}
    fn exit_case_expression(&mut self, path: &mut NodePath, expr: &CaseExpression) {}
}

pub fn traverse(visitor: &mut dyn Visitor, node: &NodeKind, parent: Option<Rc<RefCell<NodePath>>>) {
    let path = wrap(NodePath::child(node, parent));
    traverse_path(visitor, &path);
}

fn traverse_path(visitor: &mut dyn Visitor, path: &Rc<RefCell<NodePath>>) {
    path.borrow_mut().on_enter();

    if !path.borrow().skipped {
        dispatch_enter(visitor, path);
    }
    if !path.borrow().skipped {
        traverse_children(visitor, path);
    }
    if !path.borrow().skipped {
        dispatch_exit(visitor, path);
    }

    path.borrow_mut().on_exit();
}

fn dispatch_enter(visitor: &mut dyn Visitor, path: &Rc<RefCell<NodePath>>) {
    let mut path = &mut path.borrow_mut();
    let node = path.node().clone();

    match node {
        NodeKind::Program(_) => {
            visitor.enter_program(&mut path, node.program().unwrap().as_ref());
        }
        NodeKind::Block(_) => {
            visitor.enter_block(&mut path, node.block().unwrap().as_ref());
        }
        NodeKind::Identifier(_) => {
            visitor.enter_identifier(&mut path, node.identifier().unwrap().as_ref());
        }
        NodeKind::StructDefinition(_) => {
            visitor.enter_struct_definition(&mut path, node.struct_definition().unwrap().as_ref());
        }
        NodeKind::FunctionDefinition(_) => {
            visitor
                .enter_function_definition(&mut path, node.function_definition().unwrap().as_ref());
        }
        NodeKind::TypeField(_) => {
            visitor.enter_type_field(&mut path, node.type_field().unwrap().as_ref());
        }
        NodeKind::TypeAnnotation(_) => {
            visitor.enter_type_annotation(&mut path, node.type_annotation().unwrap().as_ref());
        }
        NodeKind::FunctionParameter(_) => {
            visitor
                .enter_function_parameter(&mut path, node.function_parameter().unwrap().as_ref());
        }
        NodeKind::Statement(_) => {
            visitor.enter_statement(&mut path, node.statement().unwrap().as_ref());
        }
        NodeKind::VariableDeclaration(_) => {
            visitor.enter_variable_declaration(
                &mut path,
                node.variable_declaration().unwrap().as_ref(),
            );
        }
        NodeKind::CaseArm(_) => {
            visitor.enter_case_arm(&mut path, node.case_arm().unwrap().as_ref());
        }
        NodeKind::Pattern(_) => {
            visitor.enter_pattern(&mut path, node.pattern().unwrap().as_ref());
        }
        NodeKind::StructField(_) => {
            visitor.enter_struct_field(&mut path, node.struct_field().unwrap().as_ref());
        }
        NodeKind::StructFieldPattern(_) => {
            visitor.enter_struct_field_pattern(
                &mut path,
                node.struct_field_pattern().unwrap().as_ref(),
            );
        }
        NodeKind::Expression(_) => {
            let expr = node.expression().unwrap();
            visitor.enter_expression(&mut path, &expr);

            if !path.skipped {
                match expr.kind() {
                    ExpressionKind::IntegerLiteral(value) => {
                        visitor.enter_integer_literal(&mut path, *value);
                    }
                    ExpressionKind::StringLiteral(value) => {
                        visitor.enter_string_literal(&mut path, value.as_deref());
                    }
                    ExpressionKind::StructLiteral(kind) => {
                        visitor.enter_struct_literal(&mut path, kind);
                    }
                    ExpressionKind::VariableExpression(id) => {
                        visitor.enter_variable(&mut path, id);
                    }
                    ExpressionKind::BinaryExpression(kind) => {
                        visitor.enter_binary_expression(&mut path, kind);
                    }
                    ExpressionKind::UnaryExpression(kind) => {
                        visitor.enter_unary_expression(&mut path, kind);
                    }
                    ExpressionKind::SubscriptExpression(kind) => {
                        visitor.enter_subscript_expression(&mut path, kind);
                    }
                    ExpressionKind::CallExpression(kind) => {
                        visitor.enter_call_expression(&mut path, kind);
                    }
                    ExpressionKind::MemberExpression(kind) => {
                        visitor.enter_access_expression(&mut path, kind);
                    }
                    ExpressionKind::ArrayExpression(kind) => {
                        visitor.enter_array_expression(&mut path, kind);
                    }
                    ExpressionKind::IfExpression(kind) => {
                        visitor.enter_if_expression(&mut path, kind);
                    }
                    ExpressionKind::CaseExpression(kind) => {
                        visitor.enter_case_expression(&mut path, kind);
                    }
                    ExpressionKind::Expression(_) => {}
                }
            }
        }
    }
}

fn dispatch_exit(visitor: &mut dyn Visitor, path: &Rc<RefCell<NodePath>>) {
    let mut path = &mut path.borrow_mut();
    let node = path.node().clone();

    match node {
        NodeKind::Program(_) => {
            visitor.exit_program(&mut path, node.program().unwrap().as_ref());
        }
        NodeKind::Block(_) => {
            visitor.exit_block(&mut path, node.block().unwrap().as_ref());
        }
        NodeKind::Identifier(_) => {
            visitor.exit_identifier(&mut path, node.identifier().unwrap().as_ref());
        }
        NodeKind::StructDefinition(_) => {
            visitor.exit_struct_definition(&mut path, node.struct_definition().unwrap().as_ref());
        }
        NodeKind::FunctionDefinition(_) => {
            visitor
                .exit_function_definition(&mut path, node.function_definition().unwrap().as_ref());
        }
        NodeKind::TypeField(_) => {
            visitor.exit_type_field(&mut path, node.type_field().unwrap().as_ref());
        }
        NodeKind::TypeAnnotation(_) => {
            visitor.exit_type_annotation(&mut path, node.type_annotation().unwrap().as_ref());
        }
        NodeKind::FunctionParameter(_) => {
            visitor.exit_function_parameter(&mut path, node.function_parameter().unwrap().as_ref());
        }
        NodeKind::Statement(_) => {
            visitor.exit_statement(&mut path, node.statement().unwrap().as_ref());
        }
        NodeKind::VariableDeclaration(_) => {
            visitor.exit_variable_declaration(
                &mut path,
                node.variable_declaration().unwrap().as_ref(),
            );
        }
        NodeKind::Pattern(_) => {
            visitor.exit_pattern(&mut path, node.pattern().unwrap().as_ref());
        }
        NodeKind::CaseArm(_) => {
            visitor.exit_case_arm(&mut path, node.case_arm().unwrap().as_ref());
        }
        NodeKind::StructField(_) => {
            visitor.exit_struct_field(&mut path, node.struct_field().unwrap().as_ref());
        }
        NodeKind::StructFieldPattern(_) => {
            visitor.exit_struct_field_pattern(
                &mut path,
                node.struct_field_pattern().unwrap().as_ref(),
            );
        }
        NodeKind::Expression(_) => {
            let expr = node.expression().unwrap();
            visitor.exit_expression(&mut path, &expr);

            if !path.skipped {
                match expr.kind() {
                    ExpressionKind::IntegerLiteral(value) => {
                        visitor.exit_integer_literal(&mut path, *value);
                    }
                    ExpressionKind::StringLiteral(value) => {
                        visitor.exit_string_literal(&mut path, value.as_deref());
                    }
                    ExpressionKind::VariableExpression(id) => {
                        visitor.exit_variable(&mut path, id);
                    }
                    ExpressionKind::StructLiteral(kind) => {
                        visitor.exit_struct_literal(&mut path, kind);
                    }
                    ExpressionKind::BinaryExpression(kind) => {
                        visitor.exit_binary_expression(&mut path, kind);
                    }
                    ExpressionKind::UnaryExpression(kind) => {
                        visitor.exit_unary_expression(&mut path, kind);
                    }
                    ExpressionKind::SubscriptExpression(kind) => {
                        visitor.exit_subscript_expression(&mut path, kind);
                    }
                    ExpressionKind::MemberExpression(kind) => {
                        visitor.exit_access_expression(&mut path, kind);
                    }
                    ExpressionKind::CallExpression(kind) => {
                        visitor.exit_call_expression(&mut path, kind);
                    }
                    ExpressionKind::ArrayExpression(kind) => {
                        visitor.exit_array_expression(&mut path, kind);
                    }
                    ExpressionKind::IfExpression(kind) => {
                        visitor.exit_if_expression(&mut path, kind);
                    }
                    ExpressionKind::CaseExpression(kind) => {
                        visitor.exit_case_expression(&mut path, kind);
                    }
                    ExpressionKind::Expression(_) => {}
                }
            }
        }
    }
}

fn traverse_children(visitor: &mut dyn Visitor, path: &Rc<RefCell<NodePath>>) {
    let node = path.borrow().node().clone();

    for kind in node.code() {
        match kind {
            CodeKind::Node(node) => traverse(visitor, node, Some(Rc::clone(path))),
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

fn traverse_token_trivia(visitor: &mut dyn Visitor, path: &mut NodePath, token: &Token) {
    for trivia in &token.leading_trivia {
        match &trivia.kind {
            TriviaKind::LineComment(comment) => {
                if !path.skipped {
                    visitor.enter_line_comment(path, token, trivia, comment);
                }
                if !path.skipped {
                    visitor.exit_line_comment(path, token, trivia, comment);
                }
            }
            TriviaKind::Whitespace => {
                if !path.skipped {
                    visitor.enter_whitespace(path, token, trivia);
                }
                if !path.skipped {
                    visitor.exit_whitespace(path, token, trivia);
                }
            }
        }
    }
}

fn traverse_interpreted_token(visitor: &mut dyn Visitor, path: &mut NodePath, token: &Token) {
    if !path.skipped {
        traverse_token_trivia(visitor, path, token);
    }
    if !path.skipped {
        visitor.enter_interpreted_token(path, token);
    }
    if !path.skipped {
        visitor.exit_interpreted_token(path, token);
    }
}

fn traverse_missing_token(
    visitor: &mut dyn Visitor,
    path: &mut NodePath,
    range: EffectiveRange,
    item: MissingTokenKind,
) {
    if !path.skipped {
        visitor.enter_missing_token(path, range, item);
    }
    if !path.skipped {
        visitor.exit_missing_token(path, range, item);
    }
}

fn traverse_skipped_token(
    visitor: &mut dyn Visitor,
    path: &mut NodePath,
    token: &Token,
    expected: MissingTokenKind,
) {
    if !path.skipped {
        traverse_token_trivia(visitor, path, token);
    }
    if !path.skipped {
        visitor.enter_skipped_token(path, token, expected);
    }
    if !path.skipped {
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

    impl Visitor for NodeCounter {
        fn enter_expression(&mut self, _path: &mut NodePath, _expr: &Expression) {
            self.number_of_expressions += 1;
        }
    }

    #[test]
    fn number_integer() {
        let mut visitor = NodeCounter::default();
        let program = Parser::parse_string("42");

        traverse(&mut visitor, &NodeKind::Program(Rc::clone(&program)), None);
        assert_eq!(visitor.number_of_expressions, 1);
    }
}
