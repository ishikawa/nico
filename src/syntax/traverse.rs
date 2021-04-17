use std::{
    cell::RefCell,
    rc::{Rc, Weak},
};

use crate::syntax::Token;
use crate::{syntax::tree::*, util::wrap};

use super::{EffectiveRange, MissingTokenKind, Scope, SyntaxToken, Trivia, TriviaKind};

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
            _ => {}
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
    fn enter_program(&mut self, path: &mut NodePath) {}
    fn exit_program(&mut self, path: &mut NodePath) {}

    fn enter_block(&mut self, path: &mut NodePath) {}
    fn exit_block(&mut self, path: &mut NodePath) {}

    fn enter_identifier(&mut self, path: &mut NodePath) {}
    fn exit_identifier(&mut self, path: &mut NodePath) {}

    fn enter_struct_definition(&mut self, path: &mut NodePath) {}
    fn exit_struct_definition(&mut self, path: &mut NodePath) {}

    fn enter_function_definition(&mut self, path: &mut NodePath) {}
    fn exit_function_definition(&mut self, path: &mut NodePath) {}

    fn enter_function_parameter(&mut self, path: &mut NodePath) {}
    fn exit_function_parameter(&mut self, path: &mut NodePath) {}

    fn enter_type_field(&mut self, path: &mut NodePath) {}
    fn exit_type_field(&mut self, path: &mut NodePath) {}

    fn enter_type_annotation(&mut self, path: &mut NodePath) {}
    fn exit_type_annotation(&mut self, path: &mut NodePath) {}

    fn enter_unknown_token(&mut self, path: &mut NodePath) {}
    fn exit_unknown_token(&mut self, path: &mut NodePath) {}

    fn enter_statement(&mut self, path: &mut NodePath) {}
    fn exit_statement(&mut self, path: &mut NodePath) {}

    fn enter_unit(&mut self, path: &mut NodePath) {}
    fn exit_unit(&mut self, path: &mut NodePath) {}

    fn enter_expression(&mut self, path: &mut NodePath) {}
    fn exit_expression(&mut self, path: &mut NodePath) {}

    fn enter_integer_literal(&mut self, path: &mut NodePath, literal: &IntegerLiteral) {}
    fn exit_integer_literal(&mut self, path: &mut NodePath, literal: &IntegerLiteral) {}

    fn enter_string_literal(&mut self, path: &mut NodePath, literal: &StringLiteral) {}
    fn exit_string_literal(&mut self, path: &mut NodePath, literal: &StringLiteral) {}

    fn enter_variable(&mut self, path: &mut NodePath, expr: &Identifier) {}
    fn exit_variable(&mut self, path: &mut NodePath, expr: &Identifier) {}

    fn enter_binary_expression(&mut self, path: &mut NodePath, expr: &BinaryExpression) {}
    fn exit_binary_expression(&mut self, path: &mut NodePath, expr: &BinaryExpression) {}

    fn enter_unary_expression(&mut self, path: &mut NodePath, expr: &UnaryExpression) {}
    fn exit_unary_expression(&mut self, path: &mut NodePath, expr: &UnaryExpression) {}

    fn enter_subscript_expression(&mut self, path: &mut NodePath, expr: &SubscriptExpression) {}
    fn exit_subscript_expression(&mut self, path: &mut NodePath, expr: &SubscriptExpression) {}

    fn enter_call_expression(&mut self, path: &mut NodePath, expr: &CallExpression) {}
    fn exit_call_expression(&mut self, path: &mut NodePath, expr: &CallExpression) {}

    fn enter_array_expression(&mut self, path: &mut NodePath, expr: &ArrayExpression) {}
    fn exit_array_expression(&mut self, path: &mut NodePath, expr: &ArrayExpression) {}

    fn enter_if_expression(&mut self, path: &mut NodePath, expr: &IfExpression) {}
    fn exit_if_expression(&mut self, path: &mut NodePath, expr: &IfExpression) {}
}

pub fn traverse(visitor: &mut dyn Visitor, node: &Rc<Node>, parent: Option<Rc<RefCell<NodePath>>>) {
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
    let node = Rc::clone(path.borrow().node());
    let mut path = &mut path.borrow_mut();

    match node.kind() {
        NodeKind::Program(_) => {
            visitor.enter_program(&mut path);
        }
        NodeKind::Block(_) => {
            visitor.enter_block(&mut path);
        }
        NodeKind::Identifier(_) => {
            visitor.enter_identifier(&mut path);
        }
        NodeKind::StructDefinition(_) => {
            visitor.enter_struct_definition(&mut path);
        }
        NodeKind::FunctionDefinition(_) => {
            visitor.enter_function_definition(&mut path);
        }
        NodeKind::TypeField(_) => {
            visitor.enter_type_field(&mut path);
        }
        NodeKind::TypeAnnotation(_) => {
            visitor.enter_type_annotation(&mut path);
        }
        NodeKind::FunctionParameter(_) => {
            visitor.enter_function_parameter(&mut path);
        }
        NodeKind::Statement(_) => {
            visitor.enter_statement(&mut path);
        }
        NodeKind::Unit => {
            visitor.enter_unit(&mut path);
        }
        NodeKind::Expression(Expression { kind, .. }) => {
            visitor.enter_expression(&mut path);

            if !path.skipped {
                match kind {
                    ExpressionKind::IntegerLiteral(expr) => {
                        visitor.enter_integer_literal(&mut path, expr);
                    }
                    ExpressionKind::StringLiteral(expr) => {
                        visitor.enter_string_literal(&mut path, expr);
                    }
                    ExpressionKind::VariableExpression(expr) => {
                        visitor.enter_variable(&mut path, expr);
                    }
                    ExpressionKind::BinaryExpression(expr) => {
                        visitor.enter_binary_expression(&mut path, expr);
                    }
                    ExpressionKind::UnaryExpression(expr) => {
                        visitor.enter_unary_expression(&mut path, expr);
                    }
                    ExpressionKind::SubscriptExpression(expr) => {
                        visitor.enter_subscript_expression(&mut path, expr);
                    }
                    ExpressionKind::CallExpression(expr) => {
                        visitor.enter_call_expression(&mut path, expr);
                    }
                    ExpressionKind::ArrayExpression(expr) => {
                        visitor.enter_array_expression(&mut path, expr);
                    }
                    ExpressionKind::IfExpression(expr) => {
                        visitor.enter_if_expression(&mut path, expr);
                    }
                    ExpressionKind::Expression(_) => {}
                }
            }
        }
    }
}

fn dispatch_exit(visitor: &mut dyn Visitor, path: &Rc<RefCell<NodePath>>) {
    let node = Rc::clone(path.borrow().node());
    let mut path = &mut path.borrow_mut();

    match node.kind() {
        NodeKind::Program(_) => {
            visitor.exit_program(&mut path);
        }
        NodeKind::Block(_) => {
            visitor.exit_block(&mut path);
        }
        NodeKind::Identifier(_) => {
            visitor.exit_identifier(&mut path);
        }
        NodeKind::StructDefinition(_) => {
            visitor.exit_struct_definition(&mut path);
        }
        NodeKind::FunctionDefinition(_) => {
            visitor.exit_function_definition(&mut path);
        }
        NodeKind::TypeField(_) => {
            visitor.exit_type_field(&mut path);
        }
        NodeKind::TypeAnnotation(_) => {
            visitor.exit_type_annotation(&mut path);
        }
        NodeKind::FunctionParameter(_) => {
            visitor.exit_function_parameter(&mut path);
        }
        NodeKind::Statement(_) => {
            visitor.exit_statement(&mut path);
        }
        NodeKind::Unit => {
            visitor.exit_unit(&mut path);
        }
        NodeKind::Expression(Expression { kind, .. }) => {
            visitor.exit_expression(&mut path);

            if !path.skipped {
                match kind {
                    ExpressionKind::IntegerLiteral(expr) => {
                        visitor.exit_integer_literal(&mut path, expr);
                    }
                    ExpressionKind::StringLiteral(expr) => {
                        visitor.exit_string_literal(&mut path, expr);
                    }
                    ExpressionKind::VariableExpression(expr) => {
                        visitor.exit_variable(&mut path, expr);
                    }
                    ExpressionKind::BinaryExpression(expr) => {
                        visitor.exit_binary_expression(&mut path, expr);
                    }
                    ExpressionKind::UnaryExpression(expr) => {
                        visitor.exit_unary_expression(&mut path, expr);
                    }
                    ExpressionKind::SubscriptExpression(expr) => {
                        visitor.exit_subscript_expression(&mut path, expr);
                    }
                    ExpressionKind::CallExpression(expr) => {
                        visitor.exit_call_expression(&mut path, expr);
                    }
                    ExpressionKind::ArrayExpression(expr) => {
                        visitor.exit_array_expression(&mut path, expr);
                    }
                    ExpressionKind::IfExpression(expr) => {
                        visitor.exit_if_expression(&mut path, expr);
                    }
                    ExpressionKind::Expression(_) => {}
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
            CodeKind::SyntaxToken(token) => {
                let mut path = path.borrow_mut();

                match token {
                    SyntaxToken::Interpreted(token) => {
                        traverse_interpreted_token(visitor, &mut path, token)
                    }
                    SyntaxToken::Missing { range, item } => {
                        traverse_missing_token(visitor, &mut path, *range, *item)
                    }
                    SyntaxToken::Skipped { token, expected } => {
                        traverse_skipped_token(visitor, &mut path, token, *expected)
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
        fn enter_expression(&mut self, _path: &mut NodePath) {
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
