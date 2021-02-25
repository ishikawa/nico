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
            env.insert(wrap(Binding::Function {
                name: function.name.clone(),
                r#type: Rc::clone(&function.r#type),
            }));
        }

        let env = wrap(env);

        for function in &mut module.functions {
            self.analyze_function(function, &env);
        }

        if let Some(ref mut main) = module.main {
            self.analyze_function(main, &env);
        }

        module.env = env;
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

        function.env = env;
    }

    fn analyze_expr(&self, node: &mut Node, env: &Rc<RefCell<Environment>>) {
        match &mut node.expr {
            Expr::Stmt(node) => {
                self.analyze_expr(node, env);
            }
            Expr::Integer(_) => {}
            Expr::String { .. } => {}
            Expr::Identifier {
                ref name,
                ref mut binding,
            } => {
                match env.borrow().get(&name) {
                    None => panic!("Undefined variable `{}`", name),
                    Some(ref b) => match *b.borrow() {
                        Binding::Variable { r#type: ref ty, .. } => {
                            binding.replace(Rc::clone(&b));
                            node.r#type = Rc::clone(ty);
                        }
                        _ => panic!("Invalid bound variable `{}`", name),
                    },
                };
            }
            Expr::Invocation {
                name,
                ref mut arguments,
                ref mut binding,
            } => {
                match env.borrow().get(&name) {
                    None => panic!("Undefined function `{}`", name),
                    Some(ref b) => match *b.borrow() {
                        Binding::Function {
                            r#type: ref function_type,
                            ..
                        } => {
                            match *function_type.borrow() {
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
                        _ => panic!("Invalid bound function `{}`", name),
                    },
                };

                for a in arguments {
                    self.analyze_expr(a, env);
                }
            }
            // binary op
            Expr::Add(ref mut lhs, ref mut rhs, ref mut binding) => {
                self.bind_binary_op("+", lhs, rhs, binding, env)
            }
            Expr::Sub(ref mut lhs, ref mut rhs, ref mut binding) => {
                self.bind_binary_op("-", lhs, rhs, binding, env)
            }
            Expr::Rem(ref mut lhs, ref mut rhs, ref mut binding) => {
                self.bind_binary_op("%", lhs, rhs, binding, env)
            }
            Expr::Mul(ref mut lhs, ref mut rhs, ref mut binding) => {
                self.bind_binary_op("*", lhs, rhs, binding, env)
            }
            Expr::Div(ref mut lhs, ref mut rhs, ref mut binding) => {
                self.bind_binary_op("/", lhs, rhs, binding, env)
            }
            Expr::LT(ref mut lhs, ref mut rhs, ref mut binding) => {
                self.bind_binary_op("<", lhs, rhs, binding, env)
            }
            Expr::GT(ref mut lhs, ref mut rhs, ref mut binding) => {
                self.bind_binary_op(">", lhs, rhs, binding, env)
            }
            Expr::LE(ref mut lhs, ref mut rhs, ref mut binding) => {
                self.bind_binary_op("<=", lhs, rhs, binding, env)
            }
            Expr::GE(ref mut lhs, ref mut rhs, ref mut binding) => {
                self.bind_binary_op(">=", lhs, rhs, binding, env)
            }
            Expr::EQ(ref mut lhs, ref mut rhs, ref mut binding) => {
                self.bind_binary_op("==", lhs, rhs, binding, env)
            }
            Expr::NE(ref mut lhs, ref mut rhs, ref mut binding) => {
                self.bind_binary_op("!=", lhs, rhs, binding, env)
            }
            Expr::If {
                ref mut condition,
                ref mut then_body,
                ref mut else_body,
            } => {
                self.analyze_expr(condition, env);
                for node in then_body {
                    self.analyze_expr(node, env);
                }
                for node in else_body {
                    self.analyze_expr(node, env);
                }
            }
            Expr::Case {
                ref mut head,
                ref mut arms,
                ref mut else_body,
                ..
            } => {
                self.analyze_expr(head, env);

                // else
                for node in else_body {
                    self.analyze_expr(node, env);
                }

                for parser::CaseArm {
                    ref mut pattern,
                    ref mut condition,
                    ref mut then_body,
                } in arms
                {
                    // Currntly, only "Variable pattern" is supported.
                    // - A variable pattern introduces a new environment into arm body.
                    // - The type of a this kind of pattern is always equal to the type of head.
                    let mut arm_env = Environment::with_parent(Rc::clone(env));

                    match pattern {
                        parser::Pattern::Variable(ref name, ref mut binding) => {
                            let b = wrap(Binding::Variable {
                                name: name.clone(),
                                r#type: Rc::clone(&head.r#type),
                                storage: None,
                            });

                            binding.replace(Rc::clone(&b));
                            arm_env.insert(Rc::clone(&b));
                        }
                    };

                    let arm_env = wrap(arm_env);

                    // guard
                    if let Some(ref mut condition) = condition {
                        self.analyze_expr(condition, &arm_env);
                    }

                    for node in then_body {
                        self.analyze_expr(node, &arm_env);
                    }
                }
            }
            Expr::Var { .. } => {
                panic!("not implemented")
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
                Binding::Function { .. } => binding.replace(Rc::clone(&b)),
                _ => panic!(
                    "Prelude not installed. Missing binary operator `{}`",
                    operator
                ),
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
            assert_matches!(*binding.borrow(), Binding::Variable { r#type: ref var_type, ..} => {
                assert_eq!(*var_type.borrow(), *body[0].r#type.borrow(), "variable and node has the same type");
                assert_matches!(*function.params[0].borrow(), Binding::Variable { r#type: ref param_type, ..} => {
                    assert_eq!(*var_type.borrow(), *param_type.borrow(), "variable and params[0] has the same type");
                });
            });
        });
    }

    #[test]
    fn case_head_and_variable_type() {
        let mut module = parser::parse_string(
            "
            fun foo(i)
                case i
                when x if x == 5
                    10
                else
                    20
                end
            end
            ",
        );

        analyze(&mut module);

        let function = &module.functions[0];
        let body = &function.body;

        assert_matches!(body[0].expr, Expr::Case { ref head, ref arms, ..} => {
            assert_matches!(arms[0].pattern, parser::Pattern::Variable(ref _name, ref binding) => {
                assert!(!binding.is_none());

                let binding = binding.as_ref().unwrap();

                assert_matches!(*function.params[0].borrow(), Binding::Variable { r#type: ref param_type, ..} => {
                    assert_eq!(*head.r#type.borrow(), *param_type.borrow(), "head and param[0] has the same type");
                });

                assert_matches!(*binding.borrow(), Binding::Variable { ref r#type, ..} => {
                    assert_eq!(*head.r#type.borrow(), *r#type.borrow(), "head and variable pattern has the same type");
                });
            });
        });
    }

    fn analyze(module: &mut parser::Module) {
        let mut binder = Binder::new();
        binder.analyze(module);
    }
}
