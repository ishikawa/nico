use super::parser;
use super::sem;
use parser::Expr;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

pub struct Semantic {
    // Type environment
    environment: HashMap<String, Rc<sem::Type>>,
    type_var_index: i32,
}

#[allow(unused_variables)]
impl Semantic {
    pub fn new() -> Semantic {
        Semantic {
            environment: HashMap::new(),
            type_var_index: 0,
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
        self.type_var_index += 1;

        let ty = sem::Type::TypeVariable {
            name: format!("${}", self.type_var_index),
            instance: None,
        };
        Rc::new(ty)
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

impl Semantic {
    fn new_type_var(&mut self) -> sem::Type {
        let i = self.type_var_index;

        self.type_var_index += 1;

        sem::Type::TypeVariable {
            name: format!("{}", i),
            instance: None,
        }
    }

    /// Type operator and generic variables are duplicated; non-generic variables are shared.
    fn fresh(
        &mut self,
        ty: &Rc<RefCell<sem::Type>>,
        non_generic_vars: &mut HashSet<String>,
    ) -> Rc<RefCell<sem::Type>> {
        let mut mappings = HashMap::new();
        self.freshrec(ty, non_generic_vars, &mut mappings)
    }

    fn freshrec(
        &mut self,
        ty: &Rc<RefCell<sem::Type>>,
        non_generic_vars: &mut HashSet<String>,
        mappings: &mut HashMap<String, Rc<RefCell<sem::Type>>>,
    ) -> Rc<RefCell<sem::Type>> {
        let ty = self.prune(ty);

        let freshed = match *ty.borrow() {
            sem::Type::TypeVariable { ref name, .. } => {
                if non_generic_vars.contains(name) {
                    return Rc::clone(&ty);
                } else {
                    if let Some(cached) = mappings.get(name) {
                        return Rc::clone(cached);
                    } else {
                        let cached = self.new_type_var();
                        let cached = Rc::new(RefCell::new(cached));

                        mappings.insert(name.clone(), Rc::clone(&cached));
                        return cached;
                    }
                }
            }
            // Type operators
            sem::Type::Int32 => sem::Type::Int32,
            sem::Type::Boolean => sem::Type::Boolean,
            sem::Type::String => sem::Type::String,
            sem::Type::Function {
                ref params,
                ref return_type,
            } => {
                let params = params
                    .iter()
                    .map(|x| self.freshrec(x, non_generic_vars, mappings))
                    .collect();
                let return_type = self.freshrec(&return_type, non_generic_vars, mappings);

                sem::Type::Function {
                    params,
                    return_type,
                }
            }
        };

        Rc::new(RefCell::new(freshed))
    }

    fn prune(&mut self, ty: &Rc<RefCell<sem::Type>>) -> Rc<RefCell<sem::Type>> {
        match *ty.borrow_mut() {
            sem::Type::TypeVariable {
                instance: Some(ref mut instance),
                ..
            } => {
                *instance = self.prune(instance);
                Rc::clone(&instance)
            }
            _ => Rc::clone(ty),
        }
    }

    fn unify(&mut self, ty1: &Rc<RefCell<sem::Type>>, ty2: &Rc<RefCell<sem::Type>>) {
        let ty1 = self.prune(ty1);
        let ty2 = self.prune(ty2);

        let new_instance = match *ty1.borrow() {
            sem::Type::TypeVariable { .. } => {
                if *ty1 != *ty2 {
                    if (*ty1).borrow().contains(&*ty2.borrow()) {
                        panic!("recursive unification");
                    }
                    Some(&ty2)
                } else {
                    None
                }
            }
            sem::Type::Int32 => match *ty2.borrow() {
                sem::Type::Int32 => None,
                sem::Type::TypeVariable { .. } => {
                    self.unify(&ty2, &ty1);
                    None
                }
                _ => {
                    panic!("type error: {:?}", *ty1);
                }
            },
            sem::Type::Boolean => match *ty2.borrow() {
                sem::Type::Boolean => None,
                sem::Type::TypeVariable { .. } => {
                    self.unify(&ty2, &ty1);
                    None
                }
                _ => panic!("type error: {:?}", *ty1),
            },
            sem::Type::String => match *ty2.borrow() {
                sem::Type::String => None,
                sem::Type::TypeVariable { .. } => {
                    self.unify(&ty2, &ty1);
                    None
                }
                _ => panic!("type error: {:?}", *ty1),
            },
            sem::Type::Function {
                params: ref params1,
                return_type: ref return_type1,
            } => match *ty2.borrow() {
                sem::Type::Function {
                    params: ref params2,
                    return_type: ref return_type2,
                } => {
                    if params1.len() != params2.len() {
                        panic!("The number of params differs: {:?}", *ty1);
                    }

                    for (x, y) in params1.iter().zip(params2.iter()) {
                        self.unify(x, y);
                    }

                    self.unify(return_type1, return_type2);
                    None
                }
                sem::Type::TypeVariable { .. } => {
                    self.unify(&ty2, &ty1);
                    None
                }
                _ => panic!("type error: {:?}", *ty1),
            },
        };

        if let Some(new_instance) = new_instance {
            match *ty1.borrow_mut() {
                sem::Type::TypeVariable {
                    ref mut instance, ..
                } => {
                    instance.replace(Rc::clone(new_instance));
                }
                _ => {}
            }
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
        let mut semantic = Semantic::new();

        let ty0 = sem::Type::TypeVariable {
            name: "$1".to_string(),
            instance: None,
        };

        let pty0 = Rc::new(RefCell::new(ty0));
        let pty1 = semantic.prune(&pty0);

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
        let mut semantic = Semantic::new();
        let ty0 = sem::Type::TypeVariable {
            name: "$1".to_string(),
            instance: Some(Rc::new(RefCell::new(sem::Type::Int32))),
        };

        let pty0 = Rc::new(RefCell::new(ty0));
        let pty1 = semantic.prune(&pty0);

        assert_matches!(*pty0.borrow(), sem::Type::TypeVariable {
            ref name,
            instance: Some(ref instance)
        } => {
            assert_eq!(name, "$1");
            assert_eq!(*instance.borrow(), sem::Type::Int32);
        });
        assert_matches!(*pty1.borrow(), sem::Type::Int32);
    }

    #[test]
    fn unify_int32() {
        let mut semantic = Semantic::new();
        let pty0 = Rc::new(RefCell::new(sem::Type::Int32));
        let pty1 = Rc::new(RefCell::new(sem::Type::Int32));

        semantic.unify(&pty0, &pty1);

        assert_matches!(*pty0.borrow(), sem::Type::Int32);
        assert_matches!(*pty1.borrow(), sem::Type::Int32);
    }
    #[test]
    fn unify_boolean() {
        let mut semantic = Semantic::new();
        let pty0 = Rc::new(RefCell::new(sem::Type::Boolean));
        let pty1 = Rc::new(RefCell::new(sem::Type::Boolean));

        semantic.unify(&pty0, &pty1);

        assert_matches!(*pty0.borrow(), sem::Type::Boolean);
        assert_matches!(*pty1.borrow(), sem::Type::Boolean);
    }
    #[test]
    fn unify_string() {
        let mut semantic = Semantic::new();
        let pty0 = Rc::new(RefCell::new(sem::Type::String));
        let pty1 = Rc::new(RefCell::new(sem::Type::String));

        semantic.unify(&pty0, &pty1);

        assert_matches!(*pty0.borrow(), sem::Type::String);
        assert_matches!(*pty1.borrow(), sem::Type::String);
    }

    #[test]
    fn unify_type_variable_same() {
        let mut semantic = Semantic::new();
        let pty0 = Rc::new(RefCell::new(sem::Type::TypeVariable {
            name: "a".to_string(),
            instance: None,
        }));
        let pty1 = Rc::new(RefCell::new(sem::Type::TypeVariable {
            name: "a".to_string(),
            instance: None,
        }));

        semantic.unify(&pty0, &pty1);

        assert_matches!(*pty0.borrow(), sem::Type::TypeVariable {
            ref name,
            ref instance,
        } => {
            assert_eq!(name, "a");
            assert!(instance.is_none());
        });
        assert_matches!(*pty1.borrow(), sem::Type::TypeVariable {
            ref name,
            ref instance,
        } => {
            assert_eq!(name, "a");
            assert!(instance.is_none());
        });
    }
    #[test]
    fn unify_undetermined_type_variables() {
        let mut semantic = Semantic::new();
        let pty0 = Rc::new(RefCell::new(sem::Type::TypeVariable {
            name: "a".to_string(),
            instance: None,
        }));
        let pty1 = Rc::new(RefCell::new(sem::Type::TypeVariable {
            name: "b".to_string(),
            instance: None,
        }));

        semantic.unify(&pty0, &pty1);

        assert_matches!(*pty0.borrow(), sem::Type::TypeVariable {
            ref name,
            ref instance,
        } => {
            assert_eq!(name, "a");
            assert_matches!(instance, Some(instance) => {
                assert_matches!(*instance.borrow(), sem::Type::TypeVariable {
                    ref name,
                    ref instance,
                } => {
                    assert_eq!(name, "b");
                    assert!(instance.is_none());
                });
            })
        });
        assert_matches!(*pty1.borrow(), sem::Type::TypeVariable {
            ref name,
            ref instance,
        } => {
            assert_eq!(name, "b");
            assert!(instance.is_none());
        });
    }

    #[test]
    fn fresh_int32() {
        let mut semantic = Semantic::new();
        let mut non_generic_vars = HashSet::new();
        let pty0 = Rc::new(RefCell::new(sem::Type::Int32));
        let pty1 = semantic.fresh(&pty0, &mut non_generic_vars);

        assert_eq!(pty0, pty1);
    }

    #[test]
    fn fresh_function() {
        let mut semantic = Semantic::new();
        let mut non_generic_vars = HashSet::new();

        let pty0 = Rc::new(RefCell::new(sem::Type::Function {
            params: vec![],
            return_type: Rc::new(RefCell::new(sem::Type::Boolean)),
        }));
        let pty1 = semantic.fresh(&pty0, &mut non_generic_vars);

        assert_eq!(pty0, pty1);
    }

    #[test]
    fn fresh_typevar() {
        let mut semantic = Semantic::new();
        let mut non_generic_vars = HashSet::new();
        let mut mappings = HashMap::new();

        // fresh type variable
        let pty0 = Rc::new(RefCell::new(sem::Type::TypeVariable {
            name: "$1".to_string(),
            instance: None,
        }));
        let pty1 = Rc::new(RefCell::new(sem::Type::TypeVariable {
            name: "$2".to_string(),
            instance: None,
        }));

        let fresh0 = semantic.freshrec(&pty0, &mut non_generic_vars, &mut mappings);
        let fresh1 = semantic.freshrec(&pty1, &mut non_generic_vars, &mut mappings);

        // should be cached
        let cache0 = semantic.freshrec(&pty0, &mut non_generic_vars, &mut mappings);
        let cache1 = semantic.freshrec(&pty1, &mut non_generic_vars, &mut mappings);

        assert_ne!(pty0, fresh0);
        assert_ne!(pty1, fresh1);
        assert_ne!(fresh0, fresh1);
        assert_eq!(fresh0, cache0);
        assert_eq!(fresh1, cache1);
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
