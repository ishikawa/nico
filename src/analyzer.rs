use super::parser;
use super::sem;
use parser::Expr;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

pub fn wrap(ty: sem::Type) -> Rc<RefCell<sem::Type>> {
    Rc::new(RefCell::new(ty))
}

pub struct Semantic {
    type_var_index: i32,
}

impl Semantic {
    pub fn new() -> Semantic {
        Semantic { type_var_index: 0 }
    }

    pub fn analyze(&mut self, module: &mut parser::Module) {
        let mut non_generic_vars = HashSet::new();
        let mut env = HashMap::new();

        module.name = Some("main".to_string());

        if let Some(ref mut function) = module.function {
            self.analyze_function(function, &mut non_generic_vars, &mut env);
        }
        if let Some(ref mut expr) = module.expr {
            self.analyze_expr(expr, &mut non_generic_vars, &mut env);
        }
    }

    fn analyze_function(
        &mut self,
        function: &mut parser::Function,
        non_generic_vars: &mut HashSet<String>,
        env: &HashMap<String, Rc<RefCell<sem::Type>>>,
    ) {
        let mut scoped_ng = non_generic_vars.clone();
        let mut scoped_env = env.clone();
        let mut arg_types = vec![];

        for param in function.params.iter() {
            let name = self.next_type_var_name();
            let var = wrap(sem::Type::new_type_var(&name));

            scoped_env.insert(param.clone(), Rc::clone(&var));
            scoped_ng.insert(name);

            arg_types.push(Rc::clone(&var));
        }

        let retty = self.analyze_expr(&mut function.body, &mut scoped_ng, &mut scoped_env);

        println!(
            "Function({}): {:?} -> {:?}",
            function.name, arg_types, retty
        );
    }

    fn analyze_expr(
        &mut self,
        node: &mut parser::Node,
        non_generic_vars: &mut HashSet<String>,
        env: &HashMap<String, Rc<RefCell<sem::Type>>>,
    ) -> Option<Rc<RefCell<sem::Type>>> {
        match node.expr {
            Expr::Integer(_) => {
                let ty = wrap(sem::Type::Int32);

                node.r#type = Some(Rc::clone(&ty));
                Some(Rc::clone(&ty))
            }
            Expr::String(_) => {
                let ty = wrap(sem::Type::String);

                node.r#type = Some(Rc::clone(&ty));
                Some(Rc::clone(&ty))
            }
            Expr::Identifier(ref name) => match self.lookup(name, non_generic_vars, env) {
                None => panic!("Undefined variable `{}`", name),
                Some(ty) => {
                    let ty = self.instantiate(&ty);
                    node.r#type = Some(Rc::clone(&ty));
                    Some(Rc::clone(&ty))
                }
            },
            Expr::Invocation {
                name: _,
                arguments: _,
            } => panic!("not implemented yet."),
            // binop
            Expr::Add(ref mut lhs, ref mut rhs) => {
                let function = wrap(sem::Type::Function {
                    params: vec![wrap(sem::Type::Int32), wrap(sem::Type::Int32)],
                    return_type: wrap(sem::Type::Int32),
                });

                let arg1 = self.analyze_expr(lhs, non_generic_vars, env).unwrap();
                let arg2 = self.analyze_expr(rhs, non_generic_vars, env).unwrap();
                let retty = wrap(sem::Type::new_type_var(&self.next_type_var_name()));
                let callsite = wrap(sem::Type::Function {
                    params: vec![Rc::clone(&arg1), Rc::clone(&arg2)],
                    return_type: Rc::clone(&retty),
                });

                self.unify(&function, &callsite);

                let retty = self.instantiate(&retty);

                node.r#type = Some(Rc::clone(&retty));
                Some(Rc::clone(&retty))
            }
            Expr::Sub(..) => None,
            Expr::Mul(..) => None,
            Expr::Div(..) => None,
            // relation
            Expr::LT(..) => None,
            Expr::GT(..) => None,
            Expr::LE(..) => None,
            Expr::GE(..) => None,
            Expr::EQ(..) => None,
            Expr::NE(..) => None,
            Expr::If { .. } => None,
        }
    }
}

enum Unification {
    Instantiate(Rc<RefCell<sem::Type>>),
    Unify(Rc<RefCell<sem::Type>>, Rc<RefCell<sem::Type>>),
    Done,
}

impl Semantic {
    /// Generates a new type variable.
    fn next_type_var_name(&mut self) -> String {
        let i = self.type_var_index;
        self.type_var_index += 1;
        format!("{}", i)
    }

    fn lookup(
        &mut self,
        name: &String,
        non_generic_vars: &mut HashSet<String>,
        env: &HashMap<String, Rc<RefCell<sem::Type>>>,
    ) -> Option<Rc<RefCell<sem::Type>>> {
        if let Some(ty) = env.get(name) {
            Some(self.fresh(ty, non_generic_vars))
        } else {
            None
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
                        let cached = Rc::new(RefCell::new(sem::Type::new_type_var(
                            &self.next_type_var_name(),
                        )));

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

        wrap(freshed)
    }

    fn prune(&mut self, ty: &Rc<RefCell<sem::Type>>) -> Rc<RefCell<sem::Type>> {
        match *ty.borrow_mut() {
            sem::Type::TypeVariable {
                instance: Some(ref mut instance),
                ..
            } => {
                *instance = self.instantiate(instance);
                Rc::clone(&instance)
            }
            _ => Rc::clone(ty),
        }
    }

    fn instantiate(&self, ty: &Rc<RefCell<sem::Type>>) -> Rc<RefCell<sem::Type>> {
        match *ty.borrow() {
            sem::Type::TypeVariable {
                instance: Some(ref instance),
                ..
            } => self.instantiate(instance),
            _ => Rc::clone(ty),
        }
    }

    fn unify(&mut self, ty1: &Rc<RefCell<sem::Type>>, ty2: &Rc<RefCell<sem::Type>>) {
        let pty1 = self.prune(ty1);
        let pty2 = self.prune(ty2);

        let action = match *pty1.borrow() {
            sem::Type::TypeVariable { .. } => {
                if *pty1 != *pty2 {
                    if (*pty1).borrow().contains(&*pty2.borrow()) {
                        panic!("recursive unification");
                    }
                    Unification::Instantiate(Rc::clone(&pty2))
                } else {
                    Unification::Done
                }
            }
            sem::Type::Int32 => match *pty2.borrow() {
                sem::Type::Int32 => Unification::Done,
                sem::Type::TypeVariable { .. } => {
                    Unification::Unify(Rc::clone(&pty2), Rc::clone(&pty1))
                }
                _ => {
                    panic!("type error: {:?}", *pty1);
                }
            },
            sem::Type::Boolean => match *pty2.borrow() {
                sem::Type::Boolean => Unification::Done,
                sem::Type::TypeVariable { .. } => {
                    Unification::Unify(Rc::clone(&pty2), Rc::clone(&pty1))
                }
                _ => panic!("type error: {:?}", *pty1),
            },
            sem::Type::String => match *pty2.borrow() {
                sem::Type::String => Unification::Done,
                sem::Type::TypeVariable { .. } => {
                    Unification::Unify(Rc::clone(&pty2), Rc::clone(&pty1))
                }
                _ => panic!("type error: {:?}", *pty1),
            },
            sem::Type::Function {
                params: ref params1,
                return_type: ref return_type1,
            } => match *pty2.borrow() {
                sem::Type::Function {
                    params: ref params2,
                    return_type: ref return_type2,
                } => {
                    if params1.len() != params2.len() {
                        panic!("The number of params differs: {:?}", *pty1);
                    }

                    for (x, y) in params1.iter().zip(params2.iter()) {
                        self.unify(x, y);
                    }

                    self.unify(return_type1, return_type2);
                    Unification::Done
                }
                sem::Type::TypeVariable { .. } => {
                    Unification::Unify(Rc::clone(&pty2), Rc::clone(&pty1))
                }
                _ => panic!("type error: {:?}", *pty1),
            },
        };

        match action {
            Unification::Instantiate(new_instance) => match *pty1.borrow_mut() {
                sem::Type::TypeVariable {
                    ref mut instance, ..
                } => {
                    instance.replace(Rc::clone(&new_instance));
                }
                _ => {}
            },
            Unification::Unify(ref ty1, ref ty2) => self.unify(&Rc::clone(ty1), &Rc::clone(ty2)),
            Unification::Done => {}
        };
    }
}

impl Default for Semantic {
    fn default() -> Self {
        Semantic::new()
    }
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

    #[test]
    fn infer_i32() {
        let mut module = parser::parse_string("42");
        let mut semantic = Semantic::new();

        semantic.analyze(&mut module);

        let node = module.expr.unwrap();
        assert_matches!(node.r#type, Some(ref ty) => {
            assert_eq!(*ty.borrow(), sem::Type::Int32)
        });
    }

    #[test]
    fn infer_string() {
        let mut module = parser::parse_string("\"\"");
        let mut semantic = Semantic::new();

        semantic.analyze(&mut module);

        let node = module.expr.unwrap();
        assert_matches!(node.r#type, Some(ref ty) => {
            assert_eq!(*ty.borrow(), sem::Type::String)
        });
    }

    #[test]
    fn infer_add_i32() {
        let mut module = parser::parse_string("1 + 2");
        let mut semantic = Semantic::new();

        semantic.analyze(&mut module);

        let node = module.expr.unwrap();
        assert_matches!(node.r#type, Some(ref ty) => {
            assert_eq!(*ty.borrow(), sem::Type::Int32)
        });
    }
    /*

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
