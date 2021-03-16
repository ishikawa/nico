use crate::parser;
use crate::parser::Expr;
use crate::sem;
use crate::sem::{SemanticAnalyzer, Type};

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
        self.validate_body(&mut function.body);

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
            Expr::Subscript { operand, index, .. } => {
                self.validate_expr(operand);
                self.validate_expr(index);
            }
            Expr::Access { .. } => todo!(),
            Expr::Struct { .. } => todo!(),
            Expr::Identifier { .. } => {}
            Expr::Invocation { arguments, .. } => {
                for argument in arguments {
                    self.validate_expr(argument);
                }
            }
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
            Expr::Plus(operand, _) | Expr::Minus(operand, _) => {
                self.validate_expr(operand);
            }
            Expr::If {
                condition,
                then_body,
                else_body,
            } => {
                self.validate_expr(condition);
                self.validate_body(then_body);
                if let Some(else_body) = else_body {
                    self.validate_body(else_body);
                }
            }
            Expr::Case {
                arms,
                else_body,
                head,
                head_storage: _,
            } => {
                self.validate_expr(head);

                // If the expression node were a constant, we could convert it to a space containing
                // all the actual values, but we won't do that. This is because I want the conversion to
                // space to be completed only in the type system.
                let head_space = sem::Space::from_type(&head.r#type);
                let mut arms_space = sem::Space::Empty;

                for parser::CaseArm {
                    condition,
                    then_body,
                    pattern,
                } in arms
                {
                    // exhaustivity check
                    if head_space.is_subspace_of(&arms_space) {
                        panic!("Unreachable pattern.: {:?}", pattern)
                    }

                    self.validate_pattern(pattern);

                    let space = if let Some(condition) = condition {
                        self.validate_expr(condition);

                        // If the arm has a guard, I can't express pattern as
                        // type space. Or can I express it in some guards?
                        sem::Space::Empty
                    } else {
                        sem::Space::from_pattern(pattern)
                    };

                    arms_space = arms_space.union(&space);

                    self.validate_body(then_body);
                }

                if let Some(else_body) = else_body {
                    // exhaustivity check for `else`
                    if head_space.is_subspace_of(&arms_space) {
                        panic!("Unreachable `else` clause");
                    }
                    arms_space = arms_space.union(&head_space);
                    self.validate_body(else_body);
                }

                // exhaustivity check
                if !head_space.is_subspace_of(&arms_space) {
                    panic!("Missing match arm. non-exhaustive patterns");
                }
            }
            Expr::Var { pattern, init } => {
                self.validate_expr(init);
                self.validate_pattern(pattern);

                // assignable?
                if let parser::Pattern::Integer(_) = pattern {
                    panic!("Can't assign value to `int`.");
                }

                // exhaustivity check
                let right_space = sem::Space::from_type(&init.r#type);
                let pattern_space = sem::Space::from_pattern(&pattern);

                if !right_space.is_subspace_of(&pattern_space) {
                    panic!("refutable pattern in local binding");
                }
            }
        };
    }

    fn validate_pattern(&self, _: &mut parser::Pattern) {}
}
