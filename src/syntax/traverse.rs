use std::rc::Rc;

use crate::syntax::tree::*;
use crate::syntax::Token;

use super::{Trivia, TriviaKind};

pub struct NodePath {
    skipped: bool,
    node: Rc<Node>,
    parent: Option<Rc<NodePath>>,
}

impl NodePath {
    pub fn child(node: &Rc<Node>, parent: Option<Rc<NodePath>>) -> Rc<Self> {
        Rc::new(Self {
            skipped: false,
            node: Rc::clone(node),
            parent,
        })
    }

    pub fn node(&self) -> Rc<Node> {
        Rc::clone(&self.node)
    }

    /// skips traversing the children and `exit` of the current path.
    pub fn skip(&mut self) {
        self.skipped = true;
    }

    pub fn parent(&self) -> Option<Rc<NodePath>> {
        self.parent.as_ref().map(Rc::clone)
    }
}

#[allow(unused_variables, unused_mut)]
pub trait Visitor {
    // Token
    fn enter_whitespace(&mut self, path: &mut Rc<NodePath>, token: &Token, trivia: &Trivia) {}
    fn exit_whitespace(&mut self, path: &mut Rc<NodePath>, token: &Token, trivia: &Trivia) {}

    fn enter_line_comment(
        &mut self,
        path: &mut Rc<NodePath>,
        token: &Token,
        trivia: &Trivia,
        comment: &str,
    ) {
    }
    fn exit_line_comment(
        &mut self,
        path: &mut Rc<NodePath>,
        token: &Token,
        trivia: &Trivia,
        comment: &str,
    ) {
    }

    fn enter_interpreted_token(&mut self, path: &mut Rc<NodePath>, token: &Token) {}
    fn exit_interpreted_token(&mut self, path: &mut Rc<NodePath>, token: &Token) {}

    fn enter_missing_token(&mut self, path: &mut Rc<NodePath>, token: &Token) {}
    fn exit_missing_token(&mut self, path: &mut Rc<NodePath>, token: &Token) {}

    fn enter_skipped_token(&mut self, path: &mut Rc<NodePath>, token: &Token, expected: &str) {}
    fn exit_skipped_token(&mut self, path: &mut Rc<NodePath>, token: &Token, expected: &str) {}

    // Node
    fn enter_program(&mut self, path: &mut Rc<NodePath>) {}
    fn exit_program(&mut self, path: &mut Rc<NodePath>) {}

    fn enter_name(&mut self, path: &mut Rc<NodePath>) {}
    fn exit_name(&mut self, path: &mut Rc<NodePath>) {}

    fn enter_struct_definition(&mut self, path: &mut Rc<NodePath>) {}
    fn exit_struct_definition(&mut self, path: &mut Rc<NodePath>) {}

    fn enter_function_definition(&mut self, path: &mut Rc<NodePath>) {}
    fn exit_function_definition(&mut self, path: &mut Rc<NodePath>) {}

    fn enter_function_parameter(&mut self, path: &mut Rc<NodePath>) {}
    fn exit_function_parameter(&mut self, path: &mut Rc<NodePath>) {}

    fn enter_type_field(&mut self, path: &mut Rc<NodePath>) {}
    fn exit_type_field(&mut self, path: &mut Rc<NodePath>) {}

    fn enter_type_annotation(&mut self, path: &mut Rc<NodePath>) {}
    fn exit_type_annotation(&mut self, path: &mut Rc<NodePath>) {}

    fn enter_unknown_token(&mut self, path: &mut Rc<NodePath>) {}
    fn exit_unknown_token(&mut self, path: &mut Rc<NodePath>) {}

    fn enter_statement(&mut self, path: &mut Rc<NodePath>) {}
    fn exit_statement(&mut self, path: &mut Rc<NodePath>) {}

    fn enter_expression(&mut self, path: &mut Rc<NodePath>) {}
    fn exit_expression(&mut self, path: &mut Rc<NodePath>) {}

    fn enter_integer_literal(&mut self, path: &mut Rc<NodePath>, literal: &IntegerLiteral) {}
    fn exit_integer_literal(&mut self, path: &mut Rc<NodePath>, literal: &IntegerLiteral) {}

    fn enter_string_literal(&mut self, path: &mut Rc<NodePath>, literal: &StringLiteral) {}
    fn exit_string_literal(&mut self, path: &mut Rc<NodePath>, literal: &StringLiteral) {}

    fn enter_identifier(&mut self, path: &mut Rc<NodePath>, expr: &Identifier) {}
    fn exit_identifier(&mut self, path: &mut Rc<NodePath>, expr: &Identifier) {}

    fn enter_call_expression(&mut self, path: &mut Rc<NodePath>, expr: &CallExpression) {}
    fn exit_call_expression(&mut self, path: &mut Rc<NodePath>, expr: &CallExpression) {}

    fn enter_binary_expression(&mut self, path: &mut Rc<NodePath>, expr: &BinaryExpression) {}
    fn exit_binary_expression(&mut self, path: &mut Rc<NodePath>, expr: &BinaryExpression) {}

    fn enter_unary_expression(&mut self, path: &mut Rc<NodePath>, expr: &UnaryExpression) {}
    fn exit_unary_expression(&mut self, path: &mut Rc<NodePath>, expr: &UnaryExpression) {}

    fn enter_subscript_expression(&mut self, path: &mut Rc<NodePath>, expr: &SubscriptExpression) {}

    fn exit_subscript_expression(&mut self, path: &mut Rc<NodePath>, expr: &SubscriptExpression) {}
}

pub fn traverse(visitor: &mut dyn Visitor, node: &Rc<Node>, parent: Option<Rc<NodePath>>) {
    let mut path = NodePath::child(node, parent);

    if !path.skipped {
        dispatch_enter(visitor, &mut path);
    }
    if !path.skipped {
        traverse_children(visitor, &mut path);
    }
    if !path.skipped {
        dispatch_exit(visitor, &mut path);
    }
}

fn dispatch_enter(visitor: &mut dyn Visitor, path: &mut Rc<NodePath>) {
    let node = path.node();

    match node.kind() {
        NodeKind::Program(_) => {
            visitor.enter_program(path);
        }
        NodeKind::Name(_) => {
            visitor.enter_name(path);
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

            if !path.skipped {
                match kind {
                    ExpressionKind::IntegerLiteral(expr) => {
                        visitor.enter_integer_literal(path, expr);
                    }
                    ExpressionKind::StringLiteral(expr) => {
                        visitor.enter_string_literal(path, expr);
                    }
                    ExpressionKind::Identifier(expr) => {
                        visitor.enter_identifier(path, expr);
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

fn dispatch_exit(visitor: &mut dyn Visitor, path: &mut Rc<NodePath>) {
    let node = path.node();

    match node.kind() {
        NodeKind::Program(_) => {
            visitor.exit_program(path);
        }
        NodeKind::Name(_) => {
            visitor.exit_name(path);
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

            if !path.skipped {
                match kind {
                    ExpressionKind::IntegerLiteral(expr) => {
                        visitor.exit_integer_literal(path, expr);
                    }
                    ExpressionKind::StringLiteral(expr) => {
                        visitor.exit_string_literal(path, expr);
                    }
                    ExpressionKind::Identifier(expr) => {
                        visitor.exit_identifier(path, expr);
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

fn traverse_children(visitor: &mut dyn Visitor, path: &mut Rc<NodePath>) {
    let node = path.node();

    for kind in node.code() {
        match kind {
            CodeKind::Node(node) => traverse(visitor, node, Some(Rc::clone(path))),
            CodeKind::SyntaxToken(token) => match token {
                super::SyntaxToken::Interpreted(token) => {
                    traverse_interpreted_token(visitor, path, token)
                }
                super::SyntaxToken::Missing(token) => traverse_missing_token(visitor, path, token),
                super::SyntaxToken::Skipped { token, expected } => {
                    traverse_skipped_token(visitor, path, token, expected)
                }
            },
        }
    }
}

fn traverse_token_trivia(visitor: &mut dyn Visitor, path: &mut Rc<NodePath>, token: &Token) {
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

fn traverse_interpreted_token(visitor: &mut dyn Visitor, path: &mut Rc<NodePath>, token: &Token) {
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

fn traverse_missing_token(visitor: &mut dyn Visitor, path: &mut Rc<NodePath>, token: &Token) {
    if !path.skipped {
        traverse_token_trivia(visitor, path, token);
    }
    if !path.skipped {
        visitor.enter_missing_token(path, token);
    }
    if !path.skipped {
        visitor.exit_missing_token(path, token);
    }
}

fn traverse_skipped_token(
    visitor: &mut dyn Visitor,
    path: &mut Rc<NodePath>,
    token: &Token,
    expected: &str,
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
        fn enter_expression(&mut self, _path: &mut Rc<NodePath>) {
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
