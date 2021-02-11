use super::parser;
use super::sem;
use parser::Expr;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

pub struct Semantic {
    // Type environment
    environment: HashMap<String, Rc<sem::Type>>,
    non_generic: HashMap<String, Rc<sem::Type>>,
    type_variable_index: i32,
}

fn prune(ty: Rc<RefCell<sem::Type>>) -> Rc<RefCell<sem::Type>> {
    match *ty.borrow_mut() {
        sem::Type::TypeVariable {
            instance: Some(ref mut instance),
            ..
        } => {
            *instance = prune(Rc::clone(instance));
            Rc::clone(&instance)
        }
        _ => Rc::clone(&ty),
    }
}

/*
// Check if the type given by the 2nd argument appears in the type given by the 1st argument.
fn occurs_in(ty1: Rc<RefCell<sem::Type>>, ty2: Rc<RefCell<sem::Type>>) -> bool {
    let ty1 = prune(ty1);

    let x = match *ty1.borrow() {
        sem::Type::TypeVariable { .. } => *ty1 == *ty2,
        sem::Type::Function {
            params,
            return_type,
        } => false,
        _ => false,
    };
    x
}
*/

#[allow(unused_variables)]
impl Semantic {
    pub fn new() -> Semantic {
        Semantic {
            environment: HashMap::new(),
            non_generic: HashMap::new(),
            type_variable_index: 0,
        }
    }

    pub fn analyze(&mut self, module: &mut parser::Module) {
        module.name = Some("main".to_string());

        if let Some(ref mut function) = module.function {
            self.analyze_function(function);
        }
        if let Some(ref mut expr) = module.expr {
            self.analyze_expr(expr);
        }
    }

    fn new_type_variable(&mut self) -> Rc<sem::Type> {
        self.type_variable_index += 1;

        let ty = sem::Type::TypeVariable {
            name: format!("${}", self.type_variable_index),
            instance: None,
        };
        Rc::new(ty)
    }

    fn fresh(&self, ty: &sem::Type) -> Option<sem::Type> {
        None
    }

    fn lookup(&self, name: &str) -> Option<sem::Type> {
        if let Some(ty) = self.environment.get(name) {
            self.fresh(ty)
        } else {
            None
        }
    }

    fn analyze_function(&mut self, function: &mut parser::Function) {
        for param in function.params.iter() {
            let var = self.new_type_variable();

            //self.prune(var);
            self.environment.insert(param.clone(), var);
        }

        self.analyze_expr(&mut function.body);
        self.environment.clear();
    }

    fn analyze_expr(&mut self, node: &mut parser::Node) {
        match node.expr {
            Expr::Integer(_) => {
                node.r#type = Some(Rc::new(sem::Type::Int32));
            }
            Expr::String(_) => {
                node.r#type = Some(Rc::new(sem::Type::String));
            }
            Expr::Identifier(ref name) => {
                if let Some(ty) = self.environment.get(name) {
                    node.r#type = Some(Rc::clone(ty));
                } else {
                    panic!("Undefined variable `{}`", name);
                }
            }
            Expr::Invocation {
                name: _,
                arguments: _,
            } => panic!("not implemented yet."),
            // binop
            Expr::Add(ref mut lhs, ref mut rhs) => {
                self.analyze_expr(lhs);
                self.analyze_expr(rhs);

                expect_type(lhs, sem::Type::Int32);
                expect_type(rhs, sem::Type::Int32);
                node.r#type = Some(Rc::new(sem::Type::Int32));
            }
            Expr::Sub(ref mut lhs, ref mut rhs) => {}
            Expr::Mul(ref mut lhs, ref mut rhs) => {}
            Expr::Div(ref mut lhs, ref mut rhs) => {}
            // relation
            Expr::LT(ref mut lhs, ref mut rhs) => {}
            Expr::GT(ref mut lhs, ref mut rhs) => {}
            Expr::LE(ref mut lhs, ref mut rhs) => {}
            Expr::GE(ref mut lhs, ref mut rhs) => {}
            Expr::EQ(ref mut lhs, ref mut rhs) => {}
            Expr::NE(ref mut lhs, ref mut rhs) => {}
            Expr::If {
                ref mut condition,
                ref mut then_body,
                ref mut else_body,
            } => {}
        }
    }
}

impl Default for Semantic {
    fn default() -> Self {
        Semantic::new()
    }
}

fn expect_type(node: &parser::Node, expected_type: sem::Type) {
    match &node.r#type {
        Some(ty) if **ty == expected_type => {}
        Some(ty) => panic!("Expected {:?}, but was {:?}", expected_type, ty),
        None => panic!("Type can't be inferred."),
    };
}
#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;
    //use parser;

    #[test]
    fn prune_0() {
        let ty0 = sem::Type::TypeVariable {
            name: "$1".to_string(),
            instance: None,
        };

        let pty0 = Rc::new(RefCell::new(ty0));
        let pty1 = prune(Rc::clone(&pty0));

        assert_matches!(*pty0.borrow(), sem::Type::TypeVariable {
            ref name,
            ref instance,
        } => {
            assert_eq!(name, "$1");
            assert!(instance.is_none());
        });
        assert_matches!(*pty1.borrow(), sem::Type::TypeVariable {
            ref name,
            ref instance,
        } => {
            assert_eq!(name, "$1");
            assert!(instance.is_none());
        });
    }

    #[test]
    fn prune_1() {
        let ty0 = sem::Type::TypeVariable {
            name: "$1".to_string(),
            instance: Some(Rc::new(RefCell::new(sem::Type::Int32))),
        };

        let pty0 = Rc::new(RefCell::new(ty0));
        let pty1 = prune(Rc::clone(&pty0));

        assert_matches!(*pty0.borrow(), sem::Type::TypeVariable {
            ref name,
            instance: Some(ref instance)
        } => {
            assert_eq!(name, "$1");
            assert_eq!(*instance.borrow(), sem::Type::Int32);
        });
        assert_matches!(*pty1.borrow(), sem::Type::Int32);
    }

    /*
        #[test]
        fn number_integer() {
            let mut module = parser::parse_string("42");
            let mut semantic = Semantic::new();

            semantic.analyze(&mut module);

            let node = module.expr.unwrap();
            assert_matches!(node.r#type, Some(ty) => {
                assert_eq!(*ty, sem::Type::Int32)
            });
        }

        #[test]
        fn add_operation() {
            let mut module = parser::parse_string("1 + 2");
            let mut semantic = Semantic::new();

            semantic.analyze(&mut module);

            let node = module.expr.unwrap();
            assert_matches!(node.expr, Expr::Add(lhs, rhs) => {
                assert_matches!(lhs.r#type, Some(ty) => {
                    assert_eq!(*ty, sem::Type::Int32);
                });
                assert_matches!(rhs.r#type, Some(ty) => {
                    assert_eq!(*ty, sem::Type::Int32);
                });
            });
        }
        #[test]
        fn fun1() {
            let mut module = parser::parse_string(
                "
                fun plus10(n)
                    n + 10
                end
                ",
            );
            let mut semantic = Semantic::new();

            semantic.analyze(&mut module);

            let function = module.function.unwrap();

            assert_eq!(function.name, "plus10");

            assert_matches!(function.r#type, Some(ty) => {
                assert_matches!(*ty, sem::Type::Function{ params, return_type } => {
                    assert_eq!(*params[0], sem::Type::Int32);
                    assert_eq!(*return_type, sem::Type::Int32);
                });
            });
        }
    */
}