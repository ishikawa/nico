use super::wrap;
use super::{Binding, Environment, SemanticAnalyzer, Type};
use crate::parser;
use parser::{Expr, Node};
use std::cell::RefCell;
use std::rc::Rc;

// Analyze the AST and assign variable and function bindings.
#[derive(Debug, Default)]
pub struct Binder {}

impl SemanticAnalyzer for Binder {
    fn analyze(&mut self, module: &mut parser::Module) {
        let env = wrap(Environment::prelude());
        let mut env = Environment::with_parent(env);

        // First, register functions defined in this module (except for `main`).
        for function in &module.functions {
            env.insert(wrap(Binding::defined_function(
                &function.name,
                &function.r#type,
            )));
        }

        let env = wrap(env);

        for function in &mut module.functions {
            self.analyze_function(function, &env);
        }

        if let Some(ref mut main) = module.main {
            self.analyze_function(main, &env);
        }
    }
}

impl Binder {
    pub fn new() -> Self {
        Binder::default()
    }

    fn analyze_function(&self, function: &mut parser::Function, env: &Rc<RefCell<Environment>>) {
        // Construct a scope that is valid when this function is called.
        // This contains a reference to the parent scope and the arguments.
        let mut env = Environment::with_parent(Rc::clone(env));

        // Bindings for parameters
        for binding in &function.params {
            env.insert(Rc::clone(binding));
        }

        let env = wrap(env);

        for node in &mut function.body {
            self.analyze_expr(node, &env);
        }
    }

    fn analyze_expr(&self, node: &mut Node, env: &Rc<RefCell<Environment>>) {
        match &mut node.expr {
            Expr::Stmt(node) => {
                self.analyze_expr(node, env);
            }
            Expr::Integer(_) => {}
            Expr::String { .. } => {}
            Expr::Array { elements, .. } => {
                for node in elements {
                    self.analyze_expr(node, env);
                }
            }
            Expr::Subscript { operand, index } => {
                self.analyze_expr(operand, env);
                self.analyze_expr(index, env);
            }
            Expr::Identifier { ref name, binding } => {
                match env.borrow().get(&name) {
                    None => panic!("Undefined variable `{}`", name),
                    Some(ref b) => {
                        binding.replace(Rc::clone(&b));
                        node.r#type = Rc::clone(&b.borrow().r#type);
                    }
                };
            }
            Expr::Invocation {
                ref name,
                arguments,
                binding,
            } => {
                match env.borrow().get(&name) {
                    None => panic!("Undefined function `{}`", name),
                    Some(ref b) => {
                        match *b.borrow().r#type.borrow() {
                            Type::Function {
                                ref params,
                                ref return_type,
                                ..
                            } => {
                                if params.len() != arguments.len() {
                                    panic!("Wrong number of arguments. The function `{}` takes {} arguments, but {} given.", name, params.len(), arguments.len());
                                }

                                node.r#type = Rc::clone(return_type);
                            }
                            ref ty => panic!("function type expected, but was {:?}", ty),
                        };
                        binding.replace(Rc::clone(&b));
                    }
                };

                for a in arguments {
                    self.analyze_expr(a, env);
                }
            }
            // binary op
            Expr::Add(lhs, rhs, binding) => self.bind_binary_op("+", lhs, rhs, binding, env),
            Expr::Sub(lhs, rhs, binding) => self.bind_binary_op("-", lhs, rhs, binding, env),
            Expr::Rem(lhs, rhs, binding) => self.bind_binary_op("%", lhs, rhs, binding, env),
            Expr::Mul(lhs, rhs, binding) => self.bind_binary_op("*", lhs, rhs, binding, env),
            Expr::Div(lhs, rhs, binding) => self.bind_binary_op("/", lhs, rhs, binding, env),
            Expr::LT(lhs, rhs, binding) => self.bind_binary_op("<", lhs, rhs, binding, env),
            Expr::GT(lhs, rhs, binding) => self.bind_binary_op(">", lhs, rhs, binding, env),
            Expr::LE(lhs, rhs, binding) => self.bind_binary_op("<=", lhs, rhs, binding, env),
            Expr::GE(lhs, rhs, binding) => self.bind_binary_op(">=", lhs, rhs, binding, env),
            Expr::EQ(lhs, rhs, binding) => self.bind_binary_op("==", lhs, rhs, binding, env),
            Expr::NE(lhs, rhs, binding) => self.bind_binary_op("!=", lhs, rhs, binding, env),
            Expr::If {
                condition,
                then_body,
                else_body,
            } => {
                let node_env = wrap(Environment::with_parent(Rc::clone(env)));
                let then_env = wrap(Environment::with_parent(Rc::clone(&node_env)));

                self.analyze_expr(condition, &node_env);
                for node in then_body {
                    self.analyze_expr(node, &then_env);
                }
                if let Some(else_body) = else_body {
                    let else_env = wrap(Environment::with_parent(Rc::clone(&node_env)));

                    for node in else_body {
                        self.analyze_expr(node, &else_env);
                    }
                }
            }
            Expr::Case {
                head,
                arms,
                else_body,
                ..
            } => {
                let node_env = wrap(Environment::with_parent(Rc::clone(env)));

                self.analyze_expr(head, &node_env);

                // else
                if let Some(else_body) = else_body {
                    for node in else_body {
                        let else_env = wrap(Environment::with_parent(Rc::clone(&node_env)));
                        self.analyze_expr(node, &else_env);
                    }
                }

                for parser::CaseArm {
                    pattern,
                    condition,
                    then_body,
                } in arms
                {
                    let mut arm_env = Environment::with_parent(Rc::clone(&node_env));
                    self.bind_pattern(pattern, head, &mut arm_env);

                    let arm_env = wrap(arm_env);

                    // guard
                    if let Some(condition) = condition {
                        self.analyze_expr(condition, &arm_env);
                    }

                    for node in then_body {
                        self.analyze_expr(node, &arm_env);
                    }
                }
            }
            Expr::Var { pattern, init } => {
                self.analyze_expr(init, env);
                self.bind_pattern(pattern, init, &mut *env.borrow_mut());
            }
        };
    }

    fn bind_pattern(&self, pattern: &mut parser::Pattern, target: &Node, env: &mut Environment) {
        match pattern {
            // - A variable pattern introduces a new environment into arm body.
            // - The type of a this kind of pattern is always equal to the type of head.
            parser::Pattern::Variable(_name, ref binding) => {
                env.insert(Rc::clone(binding));
            }
            parser::Pattern::Integer(_) => {}
            parser::Pattern::Array(patterns) => {
                for pattern in patterns {
                    self.bind_pattern(pattern, target, env);
                }
            }
        };
    }

    fn bind_binary_op(
        &self,
        operator: &str,
        lhs: &mut Node,
        rhs: &mut Node,
        binding: &mut Option<Rc<RefCell<Binding>>>,
        env: &Rc<RefCell<Environment>>,
    ) {
        match env.borrow().get(operator) {
            None => panic!(
                "Prelude not installed. Missing binary operator `{}`",
                operator
            ),
            Some(ref b) => match *b.borrow() {
                Binding { ref r#type, .. } => match *r#type.borrow() {
                    Type::Function { .. } => binding.replace(Rc::clone(&b)),
                    ref ty => panic!(
                        "Binary operator `{}` must be function, but was `{:?}`",
                        operator, ty
                    ),
                },
            },
        };
        self.analyze_expr(lhs, env);
        self.analyze_expr(rhs, env);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;

    #[test]
    fn param_and_variable() {
        let mut module = parser::parse_string(
            "
            fun foo(i)
                i
            end
            ",
        );

        analyze(&mut module);

        let function = &module.functions[0];
        let body = &function.body;

        assert_matches!(body[0].expr, parser::Expr::Identifier { binding: Some(ref binding), .. } => {
            let binding = binding.borrow();
            let var_type = binding.r#type.borrow();
            let param0 = function.params[0].borrow();
            let param_type = param0.r#type.borrow();

            assert_eq!(*var_type, *body[0].r#type.borrow(), "variable and node has the same type");
            assert_eq!(*var_type, *param_type, "variable and params[0] has the same type");
        });
    }

    #[test]
    fn case_head_and_variable_type() {
        let mut module = parser::parse_string(
            "
            fun foo(i)
                case i
                when x
                    x
                end
            end
            ",
        );

        analyze(&mut module);

        let function = &module.functions[0];
        let body = &function.body;

        assert_matches!(body[0].expr, Expr::Case { ref head, ref arms, ..} => {
            let param0 = function.params[0].borrow();
            let param_type = param0.r#type.borrow();
            assert_eq!(*head.r#type.borrow(), *param_type, "head and param[0] has the same type");

            assert_matches!(arms[0].pattern, parser::Pattern::Variable(ref _name, ref binding) => {
                let binding = binding.borrow();

                assert_eq!(
                    *binding.r#type.borrow(),
                    *arms[0].then_body[0].r#type.borrow(),
                    "variable pattern type and reference to it"
                );
            });
        });
    }

    fn analyze(module: &mut parser::Module) {
        let mut binder = Binder::new();
        binder.analyze(module);
    }
}
