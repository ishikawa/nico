use crate::parser;
use crate::parser::Expr;
use crate::sem::{Binding, SemanticAnalyzer, Type};

#[derive(Debug, Default)]
pub struct TypeValidator {}

impl SemanticAnalyzer for TypeValidator {
    fn analyze(&mut self, module: &mut parser::Module) {
        // All types should be resolved. Run validation.
        for function in &mut module.functions {
            self.validate_function(function);
        }
        if let Some(ref mut function) = module.main {
            self.validate_function(function);
        }
    }
}

impl TypeValidator {
    pub fn new() -> Self {
        Self::default()
    }

    fn validate_function(&self, function: &mut parser::Function) {
        for binding in &function.params {
            match *binding.borrow_mut() {
                Binding::Variable { ref mut r#type, .. } => *r#type = Type::fixed_type(r#type),
                _ => panic!("Invalid binding or allocation"),
            };
        }

        self.validate_body(&mut function.body);

        function.r#type = Type::fixed_type(&function.r#type);

        match *function.r#type.borrow() {
            Type::Function {
                ref return_type, ..
            } => match &*return_type.borrow() {
                Type::Array(_) => {
                    panic!(
                        "Attempt to return array {} from function `{}`",
                        return_type.borrow(),
                        function.name
                    );
                }
                Type::TypeVariable { .. } => {
                    panic!(
                        "Type of return value of function `{}` is unresolved: {:?}",
                        function.name, function
                    );
                }
                _ => {}
            },
            _ => panic!(
                "Expected function type but was {}",
                function.r#type.borrow()
            ),
        };
    }

    fn validate_body(&self, body: &mut Vec<parser::Node>) {
        for node in body {
            self.validate_expr(node);
        }
    }

    fn validate_expr(&self, node: &mut parser::Node) {
        node.r#type = Type::fixed_type(&node.r#type);

        match &mut node.expr {
            Expr::Stmt(expr) => {
                self.validate_expr(expr);
            }
            Expr::Integer(_) => {}
            Expr::String { .. } => {}
            Expr::Array {
                ref mut elements, ..
            } => {
                for element in elements {
                    self.validate_expr(element);
                }
            }
            Expr::Subscript { operand, index } => {
                self.validate_expr(operand);
                self.validate_expr(index);
            }
            Expr::Identifier { .. } => {}
            Expr::Invocation { arguments, .. } => {
                for argument in arguments {
                    self.validate_expr(argument);
                }
            }
            // binop
            Expr::Add(lhs, rhs, ..)
            | Expr::Sub(lhs, rhs, ..)
            | Expr::Rem(lhs, rhs, ..)
            | Expr::Mul(lhs, rhs, ..)
            | Expr::Div(lhs, rhs, ..)
            | Expr::LT(lhs, rhs, ..)
            | Expr::GT(lhs, rhs, ..)
            | Expr::LE(lhs, rhs, ..)
            | Expr::GE(lhs, rhs, ..)
            | Expr::EQ(lhs, rhs, ..)
            | Expr::NE(lhs, rhs, ..) => {
                self.validate_expr(lhs);
                self.validate_expr(rhs);
            }
            Expr::If {
                condition,
                then_body,
                else_body,
            } => {
                self.validate_expr(condition);
                self.validate_body(then_body);
                self.validate_body(else_body);
            }
            Expr::Case {
                arms,
                else_body,
                head,
                head_storage: _,
            } => {
                self.validate_expr(head);

                for parser::CaseArm {
                    condition,
                    then_body,
                    pattern,
                } in arms
                {
                    self.validate_pattern(pattern);

                    if let Some(condition) = condition {
                        self.validate_expr(condition);
                    }

                    self.validate_body(then_body);
                }

                self.validate_body(else_body);
            }
            Expr::Var { pattern, init } => {
                self.validate_expr(init);
                self.validate_pattern(pattern);
            }
        };
    }

    fn validate_pattern(&self, pattern: &mut parser::Pattern) {
        // Currntly, only "Variable pattern" is supported.
        match pattern {
            parser::Pattern::Variable(ref name, ref mut binding) => {
                let binding = binding
                    .as_ref()
                    .unwrap_or_else(|| panic!("Unbound pattern `{}`", name));

                match *(binding.borrow_mut()) {
                    Binding::Variable { ref mut r#type, .. } => {
                        *r#type = Type::fixed_type(r#type);
                    }
                    Binding::Function { .. } => panic!("Unexpected binding"),
                }
            }
        };
    }
}
