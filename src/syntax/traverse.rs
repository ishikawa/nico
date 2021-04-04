use crate::syntax::tree::*;
use crate::syntax::Token;

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
    fn enter_program(&mut self, path: &mut Path<Program>) {}
    fn exit_program(&mut self, path: &mut Path<Program>) {}

    fn enter_struct_definition(&mut self, path: &mut Path<StructDefinition>) {}
    fn exit_struct_definition(&mut self, path: &mut Path<StructDefinition>) {}

    fn enter_function_definition(&mut self, path: &mut Path<FunctionDefinition>) {}
    fn exit_function_definition(&mut self, path: &mut Path<FunctionDefinition>) {}

    fn enter_function_parameter(&mut self, path: &mut Path<FunctionParameter>) {}
    fn exit_function_parameter(&mut self, path: &mut Path<FunctionParameter>) {}

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

    if !path.skipped {
        visitor.enter_program(&mut path);
    }

    if !path.skipped {
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
        visitor.exit_struct_definition(&mut path);
    }
}

pub fn traverse_function_definition(visitor: &mut dyn Visitor, node: &FunctionDefinition) {
    let mut path = Path::new(node);

    if !path.skipped {
        visitor.enter_function_definition(&mut path);
    }

    if !path.skipped {
        for param in &node.parameters {
            traverse_function_parameter(visitor, param);
        }
    }

    if !path.skipped {
        for stmt in &node.body {
            traverse_statement(visitor, stmt);
        }
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
        visitor.exit_function_parameter(&mut path);
    }
}

pub fn traverse_unknown_token(visitor: &mut dyn Visitor, token: &Token) {
    let mut path = Path::new(token);

    if !path.skipped {
        visitor.enter_unknown_token(&mut path);
    }
    if !path.skipped {
        visitor.exit_unknown_token(&mut path);
    }
}

pub fn traverse_statement(visitor: &mut dyn Visitor, node: &Statement) {
    let mut path = Path::new(node);

    if !path.skipped {
        visitor.enter_statement(&mut path);
    }

    if !path.skipped {
        traverse_expression(visitor, &node.expression);
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
        match node.kind {
            ExpressionKind::IntegerLiteral(ref literal) => {
                _traverse_integer_literal(visitor, &mut path, literal);
            }
            ExpressionKind::StringLiteral(ref literal) => {
                _traverse_string_literal(visitor, &mut path, literal);
            }
            ExpressionKind::CallExpression(ref expr) => {
                _traverse_call_expression(visitor, &mut path, expr);
            }
            _ => {}
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
        visitor.exit_string_literal(path, literal);
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
        traverse_expression(visitor, &expr.callee);
        for arg in &expr.arguments {
            traverse_expression(visitor, arg);
        }
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
