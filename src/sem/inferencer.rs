use crate::parser;
use crate::parser::Expr;
use crate::sem::{Binding, SemanticAnalyzer, Type};
use crate::util::naming::PrefixNaming;
use crate::util::wrap;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

#[derive(Debug)]
pub struct TypeInferencer {
    generic_type_var_naming: PrefixNaming,
}

impl SemanticAnalyzer for TypeInferencer {
    fn analyze(&mut self, module: &mut parser::Module) {
        for function in &mut module.functions {
            let mut non_generic_vars = HashSet::new();
            self.analyze_function(function, &mut non_generic_vars);
        }
        if let Some(ref mut function) = module.main {
            let mut non_generic_vars = HashSet::new();
            self.analyze_function(function, &mut non_generic_vars);
        }
    }
}

impl TypeInferencer {
    pub fn new() -> TypeInferencer {
        TypeInferencer {
            generic_type_var_naming: PrefixNaming::new("$GENERIC"),
        }
    }

    // `non_generic_vars` - Non-generic type var names
    // `vars` - Identifier, Type
    fn analyze_function(
        &mut self,
        function: &mut parser::Function,
        non_generic_vars: &mut HashSet<String>,
    ) -> Rc<RefCell<Type>> {
        let mut scoped_ng = non_generic_vars.clone();

        // Register local bindings including parameters into
        // non generic variables.
        for binding in function.env.borrow().bindings() {
            if let Binding::Variable { r#type: ref ty, .. } = *binding.borrow() {
                if let Type::TypeVariable { ref name, .. } = *ty.borrow() {
                    scoped_ng.insert(name.clone());
                }
            }
        }

        // Iterates expressions. Type::Void for empty expression.
        let retty = function
            .body
            .iter_mut()
            .fold(wrap(Type::Void), |_retty, node| {
                self.analyze_expr(node, &mut scoped_ng)
            });

        // Unify return type from body.
        match *function.r#type.borrow() {
            Type::Function {
                ref return_type, ..
            } => {
                self.unify(&retty, return_type);
            }
            _ => unreachable!(),
        }

        Rc::clone(&function.r#type)
    }

    fn analyze_invocation(
        &mut self,
        function_type: Rc<RefCell<Type>>,
        retty: &Rc<RefCell<Type>>,
        args: &mut [&mut parser::Node],
        non_generic_vars: &mut HashSet<String>,
    ) -> Rc<RefCell<Type>> {
        let arg_types = args
            .iter_mut()
            .map(|nd| self.analyze_expr(nd, non_generic_vars))
            .collect::<Vec<_>>();
        let callsite = wrap(Type::Function {
            params: arg_types,
            return_type: Rc::clone(retty),
        });

        self.unify(&function_type, &callsite);
        Rc::clone(retty)
    }

    fn analyze_expr(
        &mut self,
        node: &mut parser::Node,
        non_generic_vars: &mut HashSet<String>,
    ) -> Rc<RefCell<Type>> {
        match node.expr {
            Expr::Integer(_) => Rc::clone(&node.r#type),
            Expr::String { .. } => Rc::clone(&node.r#type),
            Expr::Identifier {
                ref name,
                ref binding,
            } => self
                .lookup(binding, non_generic_vars)
                .unwrap_or_else(|| panic!("Unbound variable `{}`", name)),
            Expr::Invocation {
                ref name,
                ref binding,
                ref mut arguments,
            } => match self.lookup_function(binding, non_generic_vars) {
                None => panic!("Unbound function `{}`", name),
                Some(function_type) => {
                    let mut m = arguments.iter_mut().collect::<Vec<_>>();
                    self.analyze_invocation(
                        Rc::clone(&function_type),
                        &node.r#type,
                        &mut m,
                        non_generic_vars,
                    )
                }
            },
            // binop
            Expr::Add(ref mut lhs, ref mut rhs, ref mut binding)
            | Expr::Sub(ref mut lhs, ref mut rhs, ref mut binding)
            | Expr::Rem(ref mut lhs, ref mut rhs, ref mut binding)
            | Expr::Mul(ref mut lhs, ref mut rhs, ref mut binding)
            | Expr::Div(ref mut lhs, ref mut rhs, ref mut binding)
            | Expr::LT(ref mut lhs, ref mut rhs, ref mut binding)
            | Expr::GT(ref mut lhs, ref mut rhs, ref mut binding)
            | Expr::LE(ref mut lhs, ref mut rhs, ref mut binding)
            | Expr::GE(ref mut lhs, ref mut rhs, ref mut binding)
            | Expr::EQ(ref mut lhs, ref mut rhs, ref mut binding)
            | Expr::NE(ref mut lhs, ref mut rhs, ref mut binding) => {
                match self.lookup_function(binding, non_generic_vars) {
                    None => panic!("Prelude not installed"),
                    Some(function_type) => self.analyze_invocation(
                        Rc::clone(&function_type),
                        &node.r#type,
                        &mut [lhs.as_mut(), rhs.as_mut()],
                        non_generic_vars,
                    ),
                }
            }

            Expr::If {
                ref mut condition,
                ref mut then_body,
                ref mut else_body,
            } => {
                let cond_type = self.analyze_expr(condition, non_generic_vars);

                self.unify(&cond_type, &wrap(Type::Boolean));

                let then_type = self.analyze_expr(then_body, non_generic_vars);

                if let Some(else_body) = else_body {
                    let else_type = self.analyze_expr(else_body, non_generic_vars);
                    self.unify(&then_type, &else_type);
                }

                self.unify(&then_type, &node.r#type);
                then_type
            }
            Expr::Case {
                ref mut arms,
                ref mut else_body,
                ..
            } => {
                // arms
                let mut body_types = vec![];

                for parser::CaseArm {
                    ref mut condition,
                    ref mut then_body,
                    ..
                } in arms
                {
                    // guard
                    if let Some(ref mut condition) = condition {
                        let cond_type = self.analyze_expr(condition, non_generic_vars);
                        self.unify(&cond_type, &wrap(Type::Boolean));
                    }

                    // body - unify each arm body with else body
                    let body_type = self.analyze_expr(then_body, non_generic_vars);
                    body_types.push(body_type);
                }

                let else_type = if let Some(else_body) = else_body {
                    self.analyze_expr(else_body, non_generic_vars)
                } else {
                    panic!("Missing else clause. A case expression must contain it.");
                };

                // Unify body types with else clause's type
                let case_type = body_types.iter().fold(&else_type, |previous, ty| {
                    self.unify(previous, ty);
                    ty
                });

                self.unify(case_type, &node.r#type);
                Rc::clone(case_type)
            }
        }
    }
}

enum Unification {
    ReplaceInstance(Rc<RefCell<Type>>),
    Unify(Rc<RefCell<Type>>, Rc<RefCell<Type>>),
    Done,
}

impl TypeInferencer {
    fn lookup(
        &mut self,
        binding: &Option<Rc<RefCell<Binding>>>,
        non_generic_vars: &mut HashSet<String>,
    ) -> Option<Rc<RefCell<Type>>> {
        if let Some(binding) = binding {
            if let Binding::Variable { r#type: ref ty, .. } = *binding.borrow() {
                return Some(self.fresh(ty, non_generic_vars));
                //return Some(Rc::clone(&ty));
            }
        };

        None
    }

    fn lookup_function(
        &mut self,
        binding: &Option<Rc<RefCell<Binding>>>,
        non_generic_vars: &mut HashSet<String>,
    ) -> Option<Rc<RefCell<Type>>> {
        if let Some(binding) = binding {
            if let Binding::Function { r#type: ref ty, .. } = *binding.borrow() {
                return Some(self.fresh(ty, non_generic_vars));
            }
        };

        None
    }

    /// Type operator and generic variables are duplicated; non-generic variables are shared.
    fn fresh(
        &mut self,
        ty: &Rc<RefCell<Type>>,
        non_generic_vars: &mut HashSet<String>,
    ) -> Rc<RefCell<Type>> {
        let mut mappings = HashMap::new();
        self.freshrec(ty, non_generic_vars, &mut mappings)
    }

    /// If the argument `ty` is a generic type variable, recreate a new type variable.
    fn freshrec(
        &mut self,
        ty: &Rc<RefCell<Type>>,
        non_generic_vars: &mut HashSet<String>,
        mappings: &mut HashMap<String, Rc<RefCell<Type>>>,
    ) -> Rc<RefCell<Type>> {
        self.prune(ty);

        let freshed = match *ty.borrow() {
            Type::TypeVariable { ref name, .. } => {
                if non_generic_vars.contains(name) {
                    return Rc::clone(&ty);
                } else if let Some(cached) = mappings.get(name) {
                    return Rc::clone(cached);
                } else {
                    let cached = wrap(Type::new_type_var(&self.generic_type_var_naming.next()));

                    mappings.insert(name.clone(), Rc::clone(&cached));
                    return cached;
                }
            }
            // Type operators
            Type::Int32 => Type::Int32,
            Type::Boolean => Type::Boolean,
            Type::String => Type::String,
            Type::Void => Type::Void,
            Type::Function {
                ref params,
                ref return_type,
            } => {
                let params = params
                    .iter()
                    .map(|x| self.freshrec(x, non_generic_vars, mappings))
                    .collect();
                let return_type = self.freshrec(&return_type, non_generic_vars, mappings);

                Type::Function {
                    params,
                    return_type,
                }
            }
        };

        wrap(freshed)
    }

    /// Prune the instance chain of type variables as much as possible.
    /// Note, this function leaves unresolvable variable like T -> U -> None.
    fn prune(&mut self, ty: &Rc<RefCell<Type>>) {
        // 1. Roll up instance chain until meets primitive type.
        // 2. Replace the content of RefCall with primitive type.
        let ty2 = match *ty.borrow_mut() {
            Type::TypeVariable {
                instance: Some(ref mut instance),
                ..
            } => {
                self.prune(instance);
                *instance = Rc::clone(instance);

                match *instance.borrow() {
                    Type::Int32 => Type::Int32,
                    Type::String => Type::String,
                    Type::Boolean => Type::Boolean,
                    Type::Void => Type::Void,
                    _ => return,
                }
            }
            _ => {
                return;
            }
        };

        *ty.borrow_mut() = ty2;
    }

    fn unify(&mut self, ty1: &Rc<RefCell<Type>>, ty2: &Rc<RefCell<Type>>) {
        self.prune(ty1);
        self.prune(ty2);

        let action = match *ty1.borrow() {
            Type::TypeVariable { .. } => {
                if *ty1 != *ty2 {
                    if (*ty1).borrow().contains(&*ty2.borrow()) {
                        panic!("recursive unification");
                    }
                    Unification::ReplaceInstance(Rc::clone(&ty2))
                } else {
                    Unification::Done
                }
            }
            Type::Function {
                params: ref params1,
                return_type: ref return_type1,
            } => match *ty2.borrow() {
                Type::Function {
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
                    Unification::Done
                }
                Type::TypeVariable { .. } => Unification::Unify(Rc::clone(&ty2), Rc::clone(&ty1)),
                _ => panic!("type error: {:?}", *ty1),
            },
            _ => match *ty2.borrow() {
                ref t2 if t2.eq(&*ty1.borrow()) => Unification::Done,
                Type::TypeVariable { .. } => Unification::Unify(Rc::clone(&ty2), Rc::clone(&ty1)),
                _ => panic!("type error: {:?}", *ty1),
            },
        };

        match action {
            Unification::ReplaceInstance(new_instance) => {
                if let Type::TypeVariable {
                    ref mut instance, ..
                } = *ty1.borrow_mut()
                {
                    instance.replace(Rc::clone(&new_instance));
                }
                self.prune(ty1);
            }
            Unification::Unify(ref ty1, ref ty2) => self.unify(&Rc::clone(ty1), &Rc::clone(ty2)),
            Unification::Done => {}
        };
    }
}

impl Default for TypeInferencer {
    fn default() -> Self {
        TypeInferencer::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sem::*;
    use assert_matches::assert_matches;
    //use parser;

    #[test]
    fn prune_typevar_unresolved() {
        let mut inferencer = TypeInferencer::new();

        let ty0 = Type::TypeVariable {
            name: "$1".to_string(),
            instance: None,
        };

        let pty0 = wrap(ty0);
        inferencer.prune(&pty0);

        assert_matches!(*pty0.borrow(), Type::TypeVariable {
            ref name,
            ref instance,
        } => {
            assert_eq!(name, "$1");
            assert!(instance.is_none());
        });
    }

    #[test]
    fn prune_typevar_resolved() {
        let mut inferencer = TypeInferencer::new();
        let ty0 = Type::TypeVariable {
            name: "$1".to_string(),
            instance: Some(wrap(Type::Int32)),
        };

        let pty0 = wrap(ty0);
        inferencer.prune(&pty0);

        assert_matches!(*pty0.borrow(), Type::Int32);
    }

    #[test]
    fn prune_typevar_resolved_alias() {
        let mut inferencer = TypeInferencer::new();
        let ty0 = Type::TypeVariable {
            name: "$1".to_string(),
            instance: Some(wrap(Type::Int32)),
        };
        let pty0 = wrap(ty0);

        let ty1 = Type::TypeVariable {
            name: "$2".to_string(),
            instance: Some(Rc::clone(&pty0)),
        };
        let pty1 = wrap(ty1);

        inferencer.prune(&pty0);
        inferencer.prune(&pty1);

        assert_matches!(*pty0.borrow(), Type::Int32);
        assert_matches!(*pty1.borrow(), Type::Int32);
    }

    #[test]
    fn prune_typevar_resolved_alias2() {
        let mut inferencer = TypeInferencer::new();
        let ty0 = Type::TypeVariable {
            name: "$1".to_string(),
            instance: Some(wrap(Type::Int32)),
        };
        let pty0 = wrap(ty0);

        let ty1 = Type::TypeVariable {
            name: "$2".to_string(),
            instance: Some(Rc::clone(&pty0)),
        };
        let pty1 = wrap(ty1);

        let ty2 = Type::TypeVariable {
            name: "$3".to_string(),
            instance: Some(Rc::clone(&pty1)),
        };
        let pty2 = wrap(ty2);

        inferencer.prune(&pty0);
        inferencer.prune(&pty1);
        inferencer.prune(&pty2);

        assert_matches!(*pty0.borrow(), Type::Int32);
        assert_matches!(*pty1.borrow(), Type::Int32);
        assert_matches!(*pty2.borrow(), Type::Int32);
    }

    #[test]
    fn prune_typevar_unresolved_alias2() {
        let mut inferencer = TypeInferencer::new();
        let ty0 = Type::TypeVariable {
            name: "$1".to_string(),
            instance: None,
        };
        let pty0 = wrap(ty0);

        let ty1 = Type::TypeVariable {
            name: "$2".to_string(),
            instance: Some(Rc::clone(&pty0)),
        };
        let pty1 = wrap(ty1);

        let ty2 = Type::TypeVariable {
            name: "$3".to_string(),
            instance: Some(Rc::clone(&pty1)),
        };
        let pty2 = wrap(ty2);

        inferencer.prune(&pty0);
        inferencer.prune(&pty1);
        inferencer.prune(&pty2);

        assert_matches!(*pty0.borrow(), Type::TypeVariable {..});
        assert_matches!(*pty1.borrow(), Type::TypeVariable {..});
        assert_matches!(*pty2.borrow(), Type::TypeVariable {..});
    }

    #[test]
    fn prune_typevar_function() {
        let mut inferencer = TypeInferencer::new();

        let ty0 = wrap(Type::TypeVariable {
            name: "$1".to_string(),
            instance: Some(wrap(Type::String)),
        });
        let ty1 = wrap(Type::TypeVariable {
            name: "$2".to_string(),
            instance: Some(wrap(Type::Boolean)),
        });
        let fun_ty = wrap(Type::Function {
            params: vec![Rc::clone(&ty0)],
            return_type: Rc::clone(&ty1),
        });

        inferencer.prune(&ty0);
        inferencer.prune(&ty1);
        inferencer.prune(&fun_ty);

        assert_matches!(*ty0.borrow(), Type::String);
        assert_matches!(*ty1.borrow(), Type::Boolean);
        assert_matches!(*fun_ty.borrow(), Type::Function {ref params, ref return_type} => {
            assert_matches!(*params[0].borrow(), Type::String);
            assert_matches!(*return_type.borrow(), Type::Boolean);
        });
    }

    #[test]
    fn unify_int32() {
        let mut inferencer = TypeInferencer::new();
        let pty0 = wrap(Type::Int32);
        let pty1 = wrap(Type::Int32);

        inferencer.unify(&pty0, &pty1);

        assert_matches!(*pty0.borrow(), Type::Int32);
        assert_matches!(*pty1.borrow(), Type::Int32);
    }

    #[test]
    fn unify_boolean() {
        let mut inferencer = TypeInferencer::new();
        let pty0 = wrap(Type::Boolean);
        let pty1 = wrap(Type::Boolean);

        inferencer.unify(&pty0, &pty1);

        assert_matches!(*pty0.borrow(), Type::Boolean);
        assert_matches!(*pty1.borrow(), Type::Boolean);
    }

    #[test]
    fn unify_string() {
        let mut inferencer = TypeInferencer::new();
        let pty0 = wrap(Type::String);
        let pty1 = wrap(Type::String);

        inferencer.unify(&pty0, &pty1);

        assert_matches!(*pty0.borrow(), Type::String);
        assert_matches!(*pty1.borrow(), Type::String);
    }

    #[test]
    fn unify_type_variable_same() {
        let mut inferencer = TypeInferencer::new();
        let pty0 = Rc::new(RefCell::new(Type::TypeVariable {
            name: "a".to_string(),
            instance: None,
        }));
        let pty1 = Rc::new(RefCell::new(Type::TypeVariable {
            name: "a".to_string(),
            instance: None,
        }));

        inferencer.unify(&pty0, &pty1);

        assert_matches!(*pty0.borrow(), Type::TypeVariable {
            ref name,
            ref instance,
        } => {
            assert_eq!(name, "a");
            assert!(instance.is_none());
        });
        assert_matches!(*pty1.borrow(), Type::TypeVariable {
            ref name,
            ref instance,
        } => {
            assert_eq!(name, "a");
            assert!(instance.is_none());
        });
    }
    #[test]
    fn unify_undetermined_type_variables() {
        let mut inferencer = TypeInferencer::new();
        let pty0 = Rc::new(RefCell::new(Type::TypeVariable {
            name: "a".to_string(),
            instance: None,
        }));
        let pty1 = Rc::new(RefCell::new(Type::TypeVariable {
            name: "b".to_string(),
            instance: None,
        }));

        inferencer.unify(&pty0, &pty1);

        assert_matches!(*pty0.borrow(), Type::TypeVariable {
            ref name,
            ref instance,
        } => {
            assert_eq!(name, "a");
            assert_matches!(instance, Some(instance) => {
                assert_matches!(*instance.borrow(), Type::TypeVariable {
                    ref name,
                    ref instance,
                } => {
                    assert_eq!(name, "b");
                    assert!(instance.is_none());
                });
            })
        });
        assert_matches!(*pty1.borrow(), Type::TypeVariable {
            ref name,
            ref instance,
        } => {
            assert_eq!(name, "b");
            assert!(instance.is_none());
        });
    }

    #[test]
    fn fresh_int32() {
        let mut inferencer = TypeInferencer::new();
        let mut non_generic_vars = HashSet::new();
        let pty0 = wrap(Type::Int32);
        let pty1 = inferencer.fresh(&pty0, &mut non_generic_vars);

        assert_eq!(pty0, pty1);
    }

    #[test]
    fn fresh_function() {
        let mut inferencer = TypeInferencer::new();
        let mut non_generic_vars = HashSet::new();

        let pty0 = Rc::new(RefCell::new(Type::Function {
            params: vec![],
            return_type: wrap(Type::Boolean),
        }));
        let pty1 = inferencer.fresh(&pty0, &mut non_generic_vars);

        assert_eq!(pty0, pty1);
    }

    #[test]
    fn fresh_typevar() {
        let mut inferencer = TypeInferencer::new();
        let mut non_generic_vars = HashSet::new();
        let mut mappings = HashMap::new();

        // fresh type variable
        let pty0 = Rc::new(RefCell::new(Type::TypeVariable {
            name: "$1".to_string(),
            instance: None,
        }));
        let pty1 = Rc::new(RefCell::new(Type::TypeVariable {
            name: "$2".to_string(),
            instance: None,
        }));

        let fresh0 = inferencer.freshrec(&pty0, &mut non_generic_vars, &mut mappings);
        let fresh1 = inferencer.freshrec(&pty1, &mut non_generic_vars, &mut mappings);

        // should be cached
        let cache0 = inferencer.freshrec(&pty0, &mut non_generic_vars, &mut mappings);
        let cache1 = inferencer.freshrec(&pty1, &mut non_generic_vars, &mut mappings);

        assert_ne!(pty0, fresh0);
        assert_ne!(pty1, fresh1);
        assert_ne!(fresh0, fresh1);
        assert_eq!(fresh0, cache0);
        assert_eq!(fresh1, cache1);
    }

    #[test]
    fn infer_i32() {
        let mut module = parser::parse_string("42");
        analyze(&mut module);

        let body = module.main.unwrap().body;
        assert_matches!(body[0].r#type, ref ty => {
            assert_eq!(*ty.borrow(), Type::Int32)
        });
    }

    #[test]
    fn infer_string() {
        let mut module = parser::parse_string("\"\"");
        analyze(&mut module);

        let body = module.main.unwrap().body;
        assert_matches!(body[0].r#type, ref ty => {
            assert_eq!(*ty.borrow(), Type::String)
        });
    }

    #[test]
    fn infer_add_i32() {
        let mut module = parser::parse_string("1 + 2");
        analyze(&mut module);

        let body = module.main.unwrap().body;
        assert_matches!(body[0].r#type, ref ty => {
            assert_eq!(*ty.borrow(), Type::Int32)
        });
    }

    #[test]
    fn fun_plus10() {
        let mut module = parser::parse_string(
            "
            fun plus10(n)
                n + 10
            end
            ",
        );

        analyze(&mut module);

        let function = &module.functions[0];
        assert_eq!(function.name, "plus10");

        assert_matches!(function.r#type, ref ty => {
            assert_matches!(*ty.borrow(), Type::Function{ ref params, ref return_type } => {
                assert_eq!(*(params[0]).borrow(), Type::Int32);
                assert_eq!(*return_type.borrow(), Type::Int32);
            });
        });
    }

    #[test]
    fn fun_minus10() {
        let mut module = parser::parse_string(
            "
            fun minus10(n)
                n - 10
            end
            ",
        );

        analyze(&mut module);

        let function = &module.functions[0];
        assert_eq!(function.name, "minus10");

        assert_matches!(function.r#type, ref ty => {
            assert_matches!(*ty.borrow(), Type::Function{ ref params, ref return_type } => {
                assert_eq!(*(params[0]).borrow(), Type::Int32);
                assert_eq!(*return_type.borrow(), Type::Int32);
            });
        });
    }

    #[test]
    fn fun_invoke() {
        let mut module = parser::parse_string(
            "
            fun plus10(n)
                n + 10
            end
            plus10(5)
            ",
        );

        analyze(&mut module);

        let function = &module.functions[0];

        assert_matches!(function.r#type, ref ty => {
            assert_matches!(*ty.borrow(), Type::Function{ ref params, ref return_type } => {
                assert_eq!(*(params[0]).borrow(), Type::Int32);
                assert_eq!(*return_type.borrow(), Type::Int32);
            });
        });
    }

    #[test]
    fn fun_recursive_fun() {
        let mut module = parser::parse_string(
            "
            fun recr(n)
                if n < 1
                    0
                else
                    recr(n) - 1
                end
            end
            ",
        );

        analyze(&mut module);

        let function = &module.functions[0];
        let body = &function.body;

        assert_matches!(function.r#type, ref ty => {
            assert_matches!(*ty.borrow(), Type::Function{ ref params, ref return_type } => {
                assert_eq!(*(params[0]).borrow(), Type::Int32);
                assert_eq!(*return_type.borrow(), Type::Int32);
            });
        });

        assert_matches!(body[0].r#type, ref ty => {
            assert_eq!(*ty.borrow(), Type::Int32);
        });
    }

    #[test]
    fn case_0() {
        let mut module = parser::parse_string(
            "
            fun foo(n)
                case n
                when x if x == 5
                    x * 3
                else
                    n
                end
            end
            ",
        );

        analyze(&mut module);

        let function = &module.functions[0];
        let body = &function.body;

        assert_matches!(function.r#type, ref ty => {
            assert_matches!(*ty.borrow(), Type::Function{ ref params, ref return_type } => {
                assert_eq!(*(params[0]).borrow(), Type::Int32);
                assert_eq!(*return_type.borrow(), Type::Int32);
            });
        });

        assert_matches!(body[0].r#type, ref ty => {
            assert_eq!(*ty.borrow(), Type::Int32);
        });
    }

    #[test]
    fn case_return_constant() {
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

        assert_matches!(function.r#type, ref ty => {
            assert_matches!(*ty.borrow(), Type::Function{ ref params, ref return_type } => {
                assert_eq!(*(params[0]).borrow(), Type::Int32);
                assert_eq!(*return_type.borrow(), Type::Int32);
            });
        });

        assert_matches!(body[0].r#type, ref ty => {
            assert_eq!(*ty.borrow(), Type::Int32);
        });
    }

    fn analyze(module: &mut parser::Module) -> TypeInferencer {
        let mut binder = Binder::new();
        let mut inferencer = TypeInferencer::new();

        binder.analyze(module);
        inferencer.analyze(module);

        inferencer
    }
}
