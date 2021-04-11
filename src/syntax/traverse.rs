use std::{
    cell::RefCell,
    rc::{Rc, Weak},
};

use crate::syntax::Token;
use crate::{syntax::tree::*, util::wrap};

use super::{MissingTokenKind, Position, Scope, SyntaxToken, Trivia, TriviaKind};

pub struct NodePath {
    skipped: bool,
    node: Rc<Node>,
    scope: Weak<RefCell<Scope>>,
    main_scope: Weak<RefCell<Scope>>,
    declarations: Weak<RefCell<Scope>>,
    parent: Option<Rc<RefCell<NodePath>>>,
}

impl NodePath {
    pub fn child(node: &Rc<Node>, parent: Option<Rc<RefCell<NodePath>>>) -> Self {
        if let Some(ref parent) = parent {
            let borrowed_parent = parent.borrow();
            Self {
                skipped: false,
                node: Rc::clone(node),
                parent: Some(Rc::clone(parent)),
                scope: Weak::clone(&borrowed_parent.scope),
                main_scope: Weak::clone(&borrowed_parent.main_scope),
                declarations: Weak::clone(&borrowed_parent.declarations),
            }
        } else {
            Self {
                skipped: false,
                node: Rc::clone(node),
                parent: None,
                declarations: Weak::new(),
                scope: Weak::new(),
                main_scope: Weak::new(),
            }
        }
    }

    pub fn node(&self) -> &Rc<Node> {
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
        match self.node.kind() {
            NodeKind::Program(Program {
                main_scope,
                declarations,
                ..
            }) => {
                self.main_scope = Rc::downgrade(main_scope);
                self.scope = Rc::downgrade(declarations);
            }
            NodeKind::Block(Block { scope, .. }) => {
                self.scope = Rc::downgrade(scope);
            }
            NodeKind::Identifier(_) => {}
            NodeKind::StructDefinition(_) => {
                self.scope = Weak::clone(&self.declarations);
            }
            NodeKind::FunctionDefinition(_) => {
                self.scope = Weak::clone(&self.declarations);
            }
            NodeKind::TypeField(_) => {}
            NodeKind::TypeAnnotation(_) => {}
            NodeKind::FunctionParameter(_) => {}
            NodeKind::Statement(_) => {}
            NodeKind::Expression(_) => {}
        }
    }

    fn on_exit(&mut self) {
        match self.node.kind() {
            NodeKind::Program(_) => {
                self.main_scope = Weak::new();
                self.scope = Weak::new();
            }
            NodeKind::Block(Block { scope, .. }) => {
                self.scope = Weak::clone(&scope.borrow().parent);
            }
            NodeKind::Identifier(_) => {}
            NodeKind::StructDefinition(_) => {
                self.scope = Weak::clone(&self.main_scope);
            }
            NodeKind::FunctionDefinition(_) => {
                self.scope = Weak::clone(&self.main_scope);
            }
            NodeKind::TypeField(_) => {}
            NodeKind::TypeAnnotation(_) => {}
            NodeKind::FunctionParameter(_) => {}
            NodeKind::Statement(_) => {}
            NodeKind::Expression(_) => {}
        }
    }
}

#[allow(unused_variables, unused_mut)]
pub trait Visitor {
    // Token
    fn enter_whitespace(&mut self, path: &Rc<RefCell<NodePath>>, token: &Token, trivia: &Trivia) {}
    fn exit_whitespace(&mut self, path: &Rc<RefCell<NodePath>>, token: &Token, trivia: &Trivia) {}

    fn enter_line_comment(
        &mut self,
        path: &Rc<RefCell<NodePath>>,
        token: &Token,
        trivia: &Trivia,
        comment: &str,
    ) {
    }
    fn exit_line_comment(
        &mut self,
        path: &Rc<RefCell<NodePath>>,
        token: &Token,
        trivia: &Trivia,
        comment: &str,
    ) {
    }

    fn enter_interpreted_token(&mut self, path: &Rc<RefCell<NodePath>>, token: &Token) {}
    fn exit_interpreted_token(&mut self, path: &Rc<RefCell<NodePath>>, token: &Token) {}

    fn enter_missing_token(
        &mut self,
        path: &Rc<RefCell<NodePath>>,
        position: Position,
        item: MissingTokenKind,
    ) {
    }
    fn exit_missing_token(
        &mut self,
        path: &Rc<RefCell<NodePath>>,
        position: Position,
        item: MissingTokenKind,
    ) {
    }

    fn enter_skipped_token(
        &mut self,
        path: &Rc<RefCell<NodePath>>,
        token: &Token,
        expected: MissingTokenKind,
    ) {
    }
    fn exit_skipped_token(
        &mut self,
        path: &Rc<RefCell<NodePath>>,
        token: &Token,
        expected: MissingTokenKind,
    ) {
    }

    // Node
    fn enter_program(&mut self, path: &Rc<RefCell<NodePath>>) {}
    fn exit_program(&mut self, path: &Rc<RefCell<NodePath>>) {}

    fn enter_block(&mut self, path: &Rc<RefCell<NodePath>>) {}
    fn exit_block(&mut self, path: &Rc<RefCell<NodePath>>) {}

    fn enter_identifier(&mut self, path: &Rc<RefCell<NodePath>>) {}
    fn exit_identifier(&mut self, path: &Rc<RefCell<NodePath>>) {}

    fn enter_struct_definition(&mut self, path: &Rc<RefCell<NodePath>>) {}
    fn exit_struct_definition(&mut self, path: &Rc<RefCell<NodePath>>) {}

    fn enter_function_definition(&mut self, path: &Rc<RefCell<NodePath>>) {}
    fn exit_function_definition(&mut self, path: &Rc<RefCell<NodePath>>) {}

    fn enter_function_parameter(&mut self, path: &Rc<RefCell<NodePath>>) {}
    fn exit_function_parameter(&mut self, path: &Rc<RefCell<NodePath>>) {}

    fn enter_type_field(&mut self, path: &Rc<RefCell<NodePath>>) {}
    fn exit_type_field(&mut self, path: &Rc<RefCell<NodePath>>) {}

    fn enter_type_annotation(&mut self, path: &Rc<RefCell<NodePath>>) {}
    fn exit_type_annotation(&mut self, path: &Rc<RefCell<NodePath>>) {}

    fn enter_unknown_token(&mut self, path: &Rc<RefCell<NodePath>>) {}
    fn exit_unknown_token(&mut self, path: &Rc<RefCell<NodePath>>) {}

    fn enter_statement(&mut self, path: &Rc<RefCell<NodePath>>) {}
    fn exit_statement(&mut self, path: &Rc<RefCell<NodePath>>) {}

    fn enter_expression(&mut self, path: &Rc<RefCell<NodePath>>) {}
    fn exit_expression(&mut self, path: &Rc<RefCell<NodePath>>) {}

    fn enter_integer_literal(&mut self, path: &Rc<RefCell<NodePath>>, literal: &IntegerLiteral) {}
    fn exit_integer_literal(&mut self, path: &Rc<RefCell<NodePath>>, literal: &IntegerLiteral) {}

    fn enter_string_literal(&mut self, path: &Rc<RefCell<NodePath>>, literal: &StringLiteral) {}
    fn exit_string_literal(&mut self, path: &Rc<RefCell<NodePath>>, literal: &StringLiteral) {}

    fn enter_variable(&mut self, path: &Rc<RefCell<NodePath>>, expr: &Identifier) {}
    fn exit_variable(&mut self, path: &Rc<RefCell<NodePath>>, expr: &Identifier) {}

    fn enter_call_expression(&mut self, path: &Rc<RefCell<NodePath>>, expr: &CallExpression) {}
    fn exit_call_expression(&mut self, path: &Rc<RefCell<NodePath>>, expr: &CallExpression) {}

    fn enter_binary_expression(&mut self, path: &Rc<RefCell<NodePath>>, expr: &BinaryExpression) {}
    fn exit_binary_expression(&mut self, path: &Rc<RefCell<NodePath>>, expr: &BinaryExpression) {}

    fn enter_unary_expression(&mut self, path: &Rc<RefCell<NodePath>>, expr: &UnaryExpression) {}
    fn exit_unary_expression(&mut self, path: &Rc<RefCell<NodePath>>, expr: &UnaryExpression) {}

    fn enter_subscript_expression(
        &mut self,
        path: &Rc<RefCell<NodePath>>,
        expr: &SubscriptExpression,
    ) {
    }

    fn exit_subscript_expression(
        &mut self,
        path: &Rc<RefCell<NodePath>>,
        expr: &SubscriptExpression,
    ) {
    }
}

pub fn traverse(visitor: &mut dyn Visitor, node: &Rc<Node>, parent: Option<Rc<RefCell<NodePath>>>) {
    let path = NodePath::child(node, parent);
    let path = wrap(path);

    path.borrow_mut().on_enter();

    if !path.borrow().skipped {
        dispatch_enter(visitor, &path);
    }
    if !path.borrow().skipped {
        traverse_children(visitor, &path);
    }
    if !path.borrow().skipped {
        dispatch_exit(visitor, &path);
    }

    path.borrow_mut().on_exit();
}

fn dispatch_enter(visitor: &mut dyn Visitor, path: &Rc<RefCell<NodePath>>) {
    let node = Rc::clone(path.borrow().node());

    match node.kind() {
        NodeKind::Program(_) => {
            visitor.enter_program(path);
        }
        NodeKind::Block(_) => {
            visitor.enter_block(path);
        }
        NodeKind::Identifier(_) => {
            visitor.enter_identifier(path);
        }
        NodeKind::StructDefinition(_) => {
            visitor.enter_struct_definition(path);
        }
        NodeKind::FunctionDefinition(_) => {
            visitor.enter_function_definition(path);
        }
        NodeKind::TypeField(_) => {
            visitor.enter_type_field(path);
        }
        NodeKind::TypeAnnotation(_) => {
            visitor.enter_type_annotation(path);
        }
        NodeKind::FunctionParameter(_) => {
            visitor.enter_function_parameter(path);
        }
        NodeKind::Statement(_) => {
            visitor.enter_statement(path);
        }
        NodeKind::Expression(Expression { kind, .. }) => {
            visitor.enter_expression(path);

            if !path.borrow().skipped {
                match kind {
                    ExpressionKind::IntegerLiteral(expr) => {
                        visitor.enter_integer_literal(path, expr);
                    }
                    ExpressionKind::StringLiteral(expr) => {
                        visitor.enter_string_literal(path, expr);
                    }
                    ExpressionKind::VariableExpression(expr) => {
                        visitor.enter_variable(path, expr);
                    }
                    ExpressionKind::CallExpression(expr) => {
                        visitor.enter_call_expression(path, expr);
                    }
                    ExpressionKind::BinaryExpression(expr) => {
                        visitor.enter_binary_expression(path, expr);
                    }
                    ExpressionKind::UnaryExpression(expr) => {
                        visitor.enter_unary_expression(path, expr);
                    }
                    ExpressionKind::SubscriptExpression(expr) => {
                        visitor.enter_subscript_expression(path, expr);
                    }
                }
            }
        }
    }
}

fn dispatch_exit(visitor: &mut dyn Visitor, path: &Rc<RefCell<NodePath>>) {
    let node = Rc::clone(path.borrow().node());

    match node.kind() {
        NodeKind::Program(_) => {
            visitor.exit_program(path);
        }
        NodeKind::Block(_) => {
            visitor.exit_block(path);
        }
        NodeKind::Identifier(_) => {
            visitor.exit_identifier(path);
        }
        NodeKind::StructDefinition(_) => {
            visitor.exit_struct_definition(path);
        }
        NodeKind::FunctionDefinition(_) => {
            visitor.exit_function_definition(path);
        }
        NodeKind::TypeField(_) => {
            visitor.exit_type_field(path);
        }
        NodeKind::TypeAnnotation(_) => {
            visitor.exit_type_annotation(path);
        }
        NodeKind::FunctionParameter(_) => {
            visitor.exit_function_parameter(path);
        }
        NodeKind::Statement(_) => {
            visitor.exit_statement(path);
        }
        NodeKind::Expression(Expression { kind, .. }) => {
            visitor.exit_expression(path);

            if !path.borrow().skipped {
                match kind {
                    ExpressionKind::IntegerLiteral(expr) => {
                        visitor.exit_integer_literal(path, expr);
                    }
                    ExpressionKind::StringLiteral(expr) => {
                        visitor.exit_string_literal(path, expr);
                    }
                    ExpressionKind::VariableExpression(expr) => {
                        visitor.exit_variable(path, expr);
                    }
                    ExpressionKind::CallExpression(expr) => {
                        visitor.exit_call_expression(path, expr);
                    }
                    ExpressionKind::BinaryExpression(expr) => {
                        visitor.exit_binary_expression(path, expr);
                    }
                    ExpressionKind::UnaryExpression(expr) => {
                        visitor.exit_unary_expression(path, expr);
                    }
                    ExpressionKind::SubscriptExpression(expr) => {
                        visitor.exit_subscript_expression(path, expr);
                    }
                }
            }
        }
    }
}

fn traverse_children(visitor: &mut dyn Visitor, path: &Rc<RefCell<NodePath>>) {
    let node = Rc::clone(path.borrow().node());

    for kind in node.code() {
        match kind {
            CodeKind::Node(node) => traverse(visitor, node, Some(Rc::clone(path))),
            CodeKind::SyntaxToken(token) => match token {
                SyntaxToken::Interpreted(token) => traverse_interpreted_token(visitor, path, token),
                SyntaxToken::Missing { position, item } => {
                    traverse_missing_token(visitor, path, *position, *item)
                }
                SyntaxToken::Skipped { token, expected } => {
                    traverse_skipped_token(visitor, path, token, *expected)
                }
            },
        }
    }
}

fn traverse_token_trivia(visitor: &mut dyn Visitor, path: &Rc<RefCell<NodePath>>, token: &Token) {
    for trivia in &token.leading_trivia {
        match &trivia.kind {
            TriviaKind::LineComment(comment) => {
                if !path.borrow().skipped {
                    visitor.enter_line_comment(path, token, trivia, comment);
                }
                if !path.borrow().skipped {
                    visitor.exit_line_comment(path, token, trivia, comment);
                }
            }
            TriviaKind::Whitespace => {
                if !path.borrow().skipped {
                    visitor.enter_whitespace(path, token, trivia);
                }
                if !path.borrow().skipped {
                    visitor.exit_whitespace(path, token, trivia);
                }
            }
        }
    }
}

fn traverse_interpreted_token(
    visitor: &mut dyn Visitor,
    path: &Rc<RefCell<NodePath>>,
    token: &Token,
) {
    if !path.borrow().skipped {
        traverse_token_trivia(visitor, path, token);
    }
    if !path.borrow().skipped {
        visitor.enter_interpreted_token(path, token);
    }
    if !path.borrow().skipped {
        visitor.exit_interpreted_token(path, token);
    }
}

fn traverse_missing_token(
    visitor: &mut dyn Visitor,
    path: &Rc<RefCell<NodePath>>,
    position: Position,
    item: MissingTokenKind,
) {
    if !path.borrow().skipped {
        visitor.enter_missing_token(path, position, item);
    }
    if !path.borrow().skipped {
        visitor.exit_missing_token(path, position, item);
    }
}

fn traverse_skipped_token(
    visitor: &mut dyn Visitor,
    path: &Rc<RefCell<NodePath>>,
    token: &Token,
    expected: MissingTokenKind,
) {
    if !path.borrow().skipped {
        traverse_token_trivia(visitor, path, token);
    }
    if !path.borrow().skipped {
        visitor.enter_skipped_token(path, token, expected);
    }
    if !path.borrow().skipped {
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
        fn enter_expression(&mut self, _path: &Rc<RefCell<NodePath>>) {
            self.number_of_expressions += 1;
        }
    }

    #[test]
    fn number_integer() {
        let mut visitor = NodeCounter::default();
        let program = Rc::new(Parser::parse_string("42"));

        traverse(&mut visitor, &program, None);
        assert_eq!(visitor.number_of_expressions, 1);
    }
}
