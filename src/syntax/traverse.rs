use crate::syntax::tree::*;
use crate::tokenizer::Token;

pub struct Path<'a, T> {
    stopped: bool,
    skip_children: bool,
    node: &'a T,
}

impl<'a, T> Path<'a, T> {
    pub fn new(node: &'a T) -> Self {
        Self {
            stopped: false,
            skip_children: false,
            node,
        }
    }

    pub fn node(&self) -> &T {
        self.node
    }

    /// stops traversal entirely.
    pub fn stop(&mut self) {
        self.stopped = true;
    }

    /// skips traversing the children of the current path.
    pub fn skip(&mut self) {
        self.skip_children = true;
    }
}

#[allow(unused_variables, unused_mut)]
pub trait Visitor {
    fn enter_program(&mut self, path: &mut Path<Program>) {}
    fn exit_program(&mut self, path: &mut Path<Program>) {}

    fn enter_struct_definition(&mut self, path: &mut Path<StructDefinition>) {}
    fn exit_struct_definition(&mut self, path: &mut Path<StructDefinition>) {}

    fn enter_function_definition(&mut self, path: &mut Path<FunctionDefinition>) {}
    fn exit_function_definition(&mut self, path: &mut Path<FunctionDefinition>) {}

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

    fn enter_call_expression(&mut self, path: &mut Path<Expression>, expr: &CallExpression) {}
    fn exit_call_expression(&mut self, path: &mut Path<Expression>, expr: &CallExpression) {}
}

pub fn traverse_program(visitor: &mut dyn Visitor, node: &Program) {
    let mut path = Path::new(node);

    if !path.stopped {
        visitor.enter_program(&mut path);
    }

    if !path.skip_children {
        for node in &node.body {
            match node {
                TopLevelKind::StructDefinition(child) => traverse_struct_definition(visitor, child),
                TopLevelKind::FunctionDefinition(child) => {
                    traverse_function_definition(visitor, child)
                }
                TopLevelKind::Statement(child) => traverse_statement(visitor, child),
                TopLevelKind::Unknown(token) => traverse_unknown_token(visitor, token),
            }
        }
    }

    if !path.stopped {
        visitor.exit_program(&mut path);
    }
}

pub fn traverse_struct_definition(visitor: &mut dyn Visitor, node: &StructDefinition) {
    let mut path = Path::new(node);

    if !path.stopped {
        visitor.enter_struct_definition(&mut path);
    }
    if !path.stopped {
        visitor.exit_struct_definition(&mut path);
    }
}

pub fn traverse_function_definition(visitor: &mut dyn Visitor, node: &FunctionDefinition) {
    let mut path = Path::new(node);

    if !path.stopped {
        visitor.enter_function_definition(&mut path);
    }
    if !path.stopped {
        visitor.exit_function_definition(&mut path);
    }
}

pub fn traverse_unknown_token(visitor: &mut dyn Visitor, token: &Token) {
    let mut path = Path::new(token);

    if !path.stopped {
        visitor.enter_unknown_token(&mut path);
    }
    if !path.stopped {
        visitor.exit_unknown_token(&mut path);
    }
}

pub fn traverse_statement(visitor: &mut dyn Visitor, node: &Statement) {
    let mut path = Path::new(node);

    if !path.stopped {
        visitor.enter_statement(&mut path);
    }

    if !path.skip_children {
        traverse_expression(visitor, &node.expression);
    }

    if !path.stopped {
        visitor.exit_statement(&mut path);
    }
}

pub fn traverse_expression(visitor: &mut dyn Visitor, node: &Expression) {
    let mut path = Path::new(node);

    if !path.stopped {
        visitor.enter_expression(&mut path);
    }

    if !path.skip_children {
        match node.kind {
            ExpressionKind::IntegerLiteral(ref literal) => {
                traverse_integer_literal(visitor, node, literal);
            }
            ExpressionKind::StringLiteral(ref literal) => {
                traverse_string_literal(visitor, node, literal);
            }
            ExpressionKind::CallExpression(ref expr) => {
                traverse_call_expression(visitor, node, expr);
            }
            _ => {}
        }
    }

    if !path.stopped {
        visitor.exit_expression(&mut path);
    }
}

fn traverse_integer_literal(
    visitor: &mut dyn Visitor,
    node: &Expression,
    literal: &IntegerLiteral,
) {
    let mut path = Path::new(node);

    if !path.stopped {
        visitor.enter_integer_literal(&mut path, literal);
    }
    if !path.stopped {
        visitor.exit_integer_literal(&mut path, literal);
    }
}

fn traverse_string_literal(visitor: &mut dyn Visitor, node: &Expression, literal: &StringLiteral) {
    let mut path = Path::new(node);

    if !path.stopped {
        visitor.enter_string_literal(&mut path, literal);
    }
    if !path.stopped {
        visitor.exit_string_literal(&mut path, literal);
    }
}

fn traverse_call_expression(visitor: &mut dyn Visitor, node: &Expression, expr: &CallExpression) {
    let mut path = Path::new(node);

    if !path.stopped {
        visitor.enter_call_expression(&mut path, expr);
    }

    if !path.skip_children {
        traverse_expression(visitor, &expr.callee);
        for arg in &expr.arguments {
            traverse_expression(visitor, arg);
        }
    }

    if !path.stopped {
        visitor.exit_call_expression(&mut path, expr);
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
        let program = Parser::parse_string("42").unwrap();

        traverse_program(&mut visitor, &program);

        assert_eq!(visitor.number_of_expressions, 1);
    }
}
