use crate::syntax::tree::*;
use crate::syntax::Token;

use super::{Trivia, TriviaKind};

pub struct Path<'a, T> {
    skipped: bool,
    node: &'a T,
}

impl<'a, T> Path<'a, T> {
    pub fn new(node: &'a T) -> Self {
        Self {
            skipped: false,
            node,
        }
    }

    pub fn node(&self) -> &T {
        self.node
    }

    /// skips traversing the children and `exit` of the current path.
    pub fn skip(&mut self) {
        self.skipped = true;
    }
}

#[allow(unused_variables, unused_mut)]
pub trait Visitor {
    // Token
    fn enter_whitespace(&mut self, path: &mut Path<Trivia>) {}
    fn exit_whitespace(&mut self, path: &mut Path<Trivia>) {}

    fn enter_line_comment(&mut self, path: &mut Path<Trivia>, comment: &str) {}
    fn exit_line_comment(&mut self, path: &mut Path<Trivia>, comment: &str) {}

    fn enter_token(&mut self, path: &mut Path<Token>) {}
    fn exit_token(&mut self, path: &mut Path<Token>) {}

    fn enter_missing_token(&mut self, path: &mut Path<Token>) {}
    fn exit_missing_token(&mut self, path: &mut Path<Token>) {}

    fn enter_skipped_token(&mut self, path: &mut Path<Token>, expected: &str) {}
    fn exit_skipped_token(&mut self, path: &mut Path<Token>, expected: &str) {}

    // Node
    fn enter_program(&mut self, path: &mut Path<Program>) {}
    fn exit_program(&mut self, path: &mut Path<Program>) {}

    fn enter_name(&mut self, path: &mut Path<Name>) {}
    fn exit_name(&mut self, path: &mut Path<Name>) {}

    fn enter_struct_definition(&mut self, path: &mut Path<StructDefinition>) {}
    fn exit_struct_definition(&mut self, path: &mut Path<StructDefinition>) {}

    fn enter_function_definition(&mut self, path: &mut Path<FunctionDefinition>) {}
    fn exit_function_definition(&mut self, path: &mut Path<FunctionDefinition>) {}

    fn enter_function_parameter(&mut self, path: &mut Path<FunctionParameter>) {}
    fn exit_function_parameter(&mut self, path: &mut Path<FunctionParameter>) {}

    fn enter_type_field(&mut self, path: &mut Path<TypeField>) {}
    fn exit_type_field(&mut self, path: &mut Path<TypeField>) {}

    fn enter_type_annotation(&mut self, path: &mut Path<TypeAnnotation>) {}
    fn exit_type_annotation(&mut self, path: &mut Path<TypeAnnotation>) {}

    fn enter_unknown_token(&mut self, path: &mut Path<Token>) {}
    fn exit_unknown_token(&mut self, path: &mut Path<Token>) {}

    fn enter_statement(&mut self, path: &mut Path<Statement>) {}
    fn exit_statement(&mut self, path: &mut Path<Statement>) {}

    fn enter_expression(&mut self, path: &mut Path<Expression>) {}
    fn exit_expression(&mut self, path: &mut Path<Expression>) {}

    fn enter_integer_literal(&mut self, path: &mut Path<Expression>, literal: &IntegerLiteral) {}
    fn exit_integer_literal(&mut self, path: &mut Path<Expression>, literal: &IntegerLiteral) {}

    fn enter_string_literal(&mut self, path: &mut Path<Expression>, literal: &StringLiteral) {}
    fn exit_string_literal(&mut self, path: &mut Path<Expression>, literal: &StringLiteral) {}

    fn enter_identifier(&mut self, path: &mut Path<Expression>, expr: &Identifier) {}
    fn exit_identifier(&mut self, path: &mut Path<Expression>, expr: &Identifier) {}

    fn enter_call_expression(&mut self, path: &mut Path<Expression>, expr: &CallExpression) {}
    fn exit_call_expression(&mut self, path: &mut Path<Expression>, expr: &CallExpression) {}

    fn enter_binary_expression(&mut self, path: &mut Path<Expression>, expr: &BinaryExpression) {}
    fn exit_binary_expression(&mut self, path: &mut Path<Expression>, expr: &BinaryExpression) {}

    fn enter_unary_expression(&mut self, path: &mut Path<Expression>, expr: &UnaryExpression) {}
    fn exit_unary_expression(&mut self, path: &mut Path<Expression>, expr: &UnaryExpression) {}

    fn enter_subscript_expression(
        &mut self,
        path: &mut Path<Expression>,
        expr: &SubscriptExpression,
    ) {
    }

    fn exit_subscript_expression(
        &mut self,
        path: &mut Path<Expression>,
        expr: &SubscriptExpression,
    ) {
    }
}

pub fn traverse(visitor: &mut dyn Visitor, node: &Node) {
    match node.kind() {
        NodeKind::Program(node) => {
            if let Some(node) = node.upgrade() {
                traverse_program(visitor, &node);
            }
        }
        NodeKind::Name(node) => {
            if let Some(node) = node.upgrade() {
                traverse_name(visitor, &node);
            }
        }
        NodeKind::StructDefinition(node) => {
            if let Some(node) = node.upgrade() {
                traverse_struct_definition(visitor, &node);
            }
        }
        NodeKind::FunctionDefinition(node) => {
            if let Some(node) = node.upgrade() {
                traverse_function_definition(visitor, &node);
            }
        }
        NodeKind::TypeField(node) => {
            if let Some(node) = node.upgrade() {
                traverse_type_field(visitor, &node);
            }
        }
        NodeKind::TypeAnnotation(node) => {
            if let Some(node) = node.upgrade() {
                traverse_type_annotation(visitor, &node);
            }
        }
        NodeKind::FunctionParameter(node) => {
            if let Some(node) = node.upgrade() {
                traverse_function_parameter(visitor, &node);
            }
        }
        NodeKind::Statement(node) => {
            if let Some(node) = node.upgrade() {
                traverse_statement(visitor, &node);
            }
        }
        NodeKind::Expression(node) => {
            if let Some(node) = node.upgrade() {
                traverse_expression(visitor, &node);
            }
        }
    }
}

fn traverse_children<T: CodeIterable>(visitor: &mut dyn Visitor, node: &T) {
    for kind in node.code() {
        match kind {
            CodeKind::Node(node) => traverse(visitor, node),
            CodeKind::SyntaxToken(token) => match token {
                super::SyntaxToken::Interpreted(token) => {
                    traverse_interpreted_token(visitor, token)
                }
                super::SyntaxToken::Missing(token) => traverse_missing_token(visitor, token),
                super::SyntaxToken::Skipped { token, expected } => {
                    traverse_skipped_token(visitor, token, expected)
                }
            },
        }
    }
}

fn traverse_token_trivia(visitor: &mut dyn Visitor, token: &Token) {
    for trivia in &token.leading_trivia {
        let mut path = Path::new(trivia);

        match &trivia.kind {
            TriviaKind::LineComment(comment) => {
                if !path.skipped {
                    visitor.enter_line_comment(&mut path, comment);
                }
                if !path.skipped {
                    visitor.exit_line_comment(&mut path, comment);
                }
            }
            TriviaKind::Whitespace => {
                if !path.skipped {
                    visitor.enter_whitespace(&mut path);
                }
                if !path.skipped {
                    visitor.exit_whitespace(&mut path);
                }
            }
        }
    }
}

fn traverse_interpreted_token(visitor: &mut dyn Visitor, token: &Token) {
    let mut path = Path::new(token);

    if !path.skipped {
        traverse_token_trivia(visitor, token);
    }
    if !path.skipped {
        visitor.enter_token(&mut path);
    }
    if !path.skipped {
        visitor.exit_token(&mut path);
    }
}

fn traverse_missing_token(visitor: &mut dyn Visitor, token: &Token) {
    let mut path = Path::new(token);

    if !path.skipped {
        traverse_token_trivia(visitor, token);
    }
    if !path.skipped {
        visitor.enter_missing_token(&mut path);
    }
    if !path.skipped {
        visitor.exit_missing_token(&mut path);
    }
}

fn traverse_skipped_token(visitor: &mut dyn Visitor, token: &Token, expected: &str) {
    let mut path = Path::new(token);

    if !path.skipped {
        traverse_token_trivia(visitor, token);
    }
    if !path.skipped {
        visitor.enter_skipped_token(&mut path, expected);
    }
    if !path.skipped {
        visitor.exit_skipped_token(&mut path, expected);
    }
}

pub fn traverse_program(visitor: &mut dyn Visitor, node: &Program) {
    let mut path = Path::new(node);

    if !path.skipped {
        visitor.enter_program(&mut path);
    }
    if !path.skipped {
        traverse_children(visitor, node);
    }
    if !path.skipped {
        visitor.exit_program(&mut path);
    }
}

pub fn traverse_struct_definition(visitor: &mut dyn Visitor, node: &StructDefinition) {
    let mut path = Path::new(node);

    if !path.skipped {
        visitor.enter_struct_definition(&mut path);
    }
    if !path.skipped {
        traverse_children(visitor, node);
    }
    if !path.skipped {
        visitor.exit_struct_definition(&mut path);
    }
}

pub fn traverse_name(visitor: &mut dyn Visitor, node: &Name) {
    let mut path = Path::new(node);

    if !path.skipped {
        visitor.enter_name(&mut path);
    }
    if !path.skipped {
        traverse_children(visitor, node);
    }
    if !path.skipped {
        visitor.exit_name(&mut path);
    }
}

pub fn traverse_function_definition(visitor: &mut dyn Visitor, node: &FunctionDefinition) {
    let mut path = Path::new(node);

    if !path.skipped {
        visitor.enter_function_definition(&mut path);
    }
    if !path.skipped {
        traverse_children(visitor, node);
    }
    if !path.skipped {
        visitor.exit_function_definition(&mut path);
    }
}

pub fn traverse_function_parameter(visitor: &mut dyn Visitor, node: &FunctionParameter) {
    let mut path = Path::new(node);

    if !path.skipped {
        visitor.enter_function_parameter(&mut path);
    }
    if !path.skipped {
        traverse_children(visitor, node);
    }
    if !path.skipped {
        visitor.exit_function_parameter(&mut path);
    }
}

pub fn traverse_type_field(visitor: &mut dyn Visitor, node: &TypeField) {
    let mut path = Path::new(node);

    if !path.skipped {
        visitor.enter_type_field(&mut path);
    }
    if !path.skipped {
        traverse_children(visitor, node);
    }
    if !path.skipped {
        visitor.exit_type_field(&mut path);
    }
}

pub fn traverse_type_annotation(visitor: &mut dyn Visitor, node: &TypeAnnotation) {
    let mut path = Path::new(node);

    if !path.skipped {
        visitor.enter_type_annotation(&mut path);
    }
    if !path.skipped {
        traverse_children(visitor, node);
    }
    if !path.skipped {
        visitor.exit_type_annotation(&mut path);
    }
}

pub fn traverse_statement(visitor: &mut dyn Visitor, node: &Statement) {
    let mut path = Path::new(node);

    if !path.skipped {
        visitor.enter_statement(&mut path);
    }
    if !path.skipped {
        traverse_children(visitor, node);
    }
    if !path.skipped {
        visitor.exit_statement(&mut path);
    }
}

pub fn traverse_expression(visitor: &mut dyn Visitor, node: &Expression) {
    let mut path = Path::new(node);

    if !path.skipped {
        visitor.enter_expression(&mut path);
    }

    if !path.skipped {
        match &node.kind {
            ExpressionKind::IntegerLiteral(literal) => {
                _traverse_integer_literal(visitor, &mut path, literal);
            }
            ExpressionKind::StringLiteral(literal) => {
                _traverse_string_literal(visitor, &mut path, literal);
            }
            ExpressionKind::Identifier(expr) => {
                _traverse_identifier(visitor, &mut path, expr);
            }
            ExpressionKind::CallExpression(expr) => {
                _traverse_call_expression(visitor, &mut path, expr);
            }
            ExpressionKind::BinaryExpression(expr) => {
                _traverse_binary_expression(visitor, &mut path, expr);
            }
            ExpressionKind::UnaryExpression(expr) => {
                _traverse_unary_expression(visitor, &mut path, expr);
            }
            ExpressionKind::SubscriptExpression(expr) => {
                _traverse_subscript_expression(visitor, &mut path, expr);
            }
        }
    }

    if !path.skipped {
        visitor.exit_expression(&mut path);
    }
}

fn _traverse_integer_literal(
    visitor: &mut dyn Visitor,
    path: &mut Path<Expression>,
    literal: &IntegerLiteral,
) {
    if !path.skipped {
        visitor.enter_integer_literal(path, literal);
    }
    if !path.skipped {
        traverse_children(visitor, path.node());
    }
    if !path.skipped {
        visitor.exit_integer_literal(path, literal);
    }
}

fn _traverse_string_literal(
    visitor: &mut dyn Visitor,
    path: &mut Path<Expression>,
    literal: &StringLiteral,
) {
    if !path.skipped {
        visitor.enter_string_literal(path, literal);
    }
    if !path.skipped {
        traverse_children(visitor, path.node());
    }
    if !path.skipped {
        visitor.exit_string_literal(path, literal);
    }
}

fn _traverse_identifier(visitor: &mut dyn Visitor, path: &mut Path<Expression>, expr: &Identifier) {
    if !path.skipped {
        visitor.enter_identifier(path, expr);
    }
    if !path.skipped {
        traverse_children(visitor, path.node());
    }
    if !path.skipped {
        visitor.exit_identifier(path, expr);
    }
}

fn _traverse_binary_expression(
    visitor: &mut dyn Visitor,
    path: &mut Path<Expression>,
    expr: &BinaryExpression,
) {
    if !path.skipped {
        visitor.enter_binary_expression(path, expr);
    }
    if !path.skipped {
        traverse_children(visitor, path.node());
    }
    if !path.skipped {
        visitor.exit_binary_expression(path, expr);
    }
}

fn _traverse_unary_expression(
    visitor: &mut dyn Visitor,
    path: &mut Path<Expression>,
    expr: &UnaryExpression,
) {
    if !path.skipped {
        visitor.enter_unary_expression(path, expr);
    }
    if !path.skipped {
        traverse_children(visitor, path.node());
    }
    if !path.skipped {
        visitor.exit_unary_expression(path, expr);
    }
}

fn _traverse_subscript_expression(
    visitor: &mut dyn Visitor,
    path: &mut Path<Expression>,
    expr: &SubscriptExpression,
) {
    if !path.skipped {
        visitor.enter_subscript_expression(path, expr);
    }
    if !path.skipped {
        traverse_children(visitor, path.node());
    }
    if !path.skipped {
        visitor.exit_subscript_expression(path, expr);
    }
}
fn _traverse_call_expression(
    visitor: &mut dyn Visitor,
    path: &mut Path<Expression>,
    expr: &CallExpression,
) {
    if !path.skipped {
        visitor.enter_call_expression(path, expr);
    }
    if !path.skipped {
        traverse_children(visitor, path.node());
    }
    if !path.skipped {
        visitor.exit_call_expression(path, expr);
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
        fn enter_expression(&mut self, _path: &mut Path<Expression>) {
            self.number_of_expressions += 1;
        }
    }

    #[test]
    fn number_integer() {
        let mut visitor = NodeCounter::default();
        let program = Parser::parse_string("42");

        traverse_program(&mut visitor, &program);

        assert_eq!(visitor.number_of_expressions, 1);
    }
}
