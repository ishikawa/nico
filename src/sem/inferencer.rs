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
            self.analyze_function(function);
        }
        if let Some(ref mut function) = module.main {
            self.analyze_function(function);
        }
    }
}

impl TypeInferencer {
    pub fn new() -> TypeInferencer {
        TypeInferencer {
            generic_type_var_naming: PrefixNaming::new("$GENERIC"),
        }
    }

    // `generic_vars` - Non
    // `vars` - Identifier, Type
    fn analyze_function(&mut self, function: &mut parser::Function) -> Rc<RefCell<Type>> {
        // Generic type var names. Nico doesn't support generic type vars though.
        // See `freshrec()` funciton.
        let mut generic_vars = HashSet::new();

        // Iterates expressions. Type::Void for empty expression.
        let retty = self.analyze_body(&mut function.body, &mut generic_vars);

        // Unify return type from body.
        match &*function.r#type.borrow() {
            Type::Function { return_type, .. } => self.unify(&retty, return_type),
            ty => panic!("Expected function type but was {:?}", ty),
        }

        Rc::clone(&function.r#type)
    }

    fn analyze_invocation(
        &mut self,
        function_type: Rc<RefCell<Type>>,
        retty: &Rc<RefCell<Type>>,
        args: &mut [&mut parser::Node],
        generic_vars: &mut HashSet<String>,
    ) -> Rc<RefCell<Type>> {
        let arg_types = args
            .iter_mut()
            .map(|nd| self.analyze_expr(nd, generic_vars))
            .collect::<Vec<_>>();
        let callsite = wrap(Type::Function {
            params: arg_types,
            return_type: Rc::clone(retty),
        });

        self.unify(&function_type, &callsite);
        Rc::clone(retty)
    }

    fn analyze_body(
        &mut self,
        body: &mut Vec<parser::Node>,
        generic_vars: &mut HashSet<String>,
    ) -> Rc<RefCell<Type>> {
        // Iterates expressions. Type::Void for empty expression.
        body.iter_mut().fold(wrap(Type::Void), |_retty, node| {
            self.analyze_expr(node, generic_vars)
        })
    }

    fn analyze_expr(
        &mut self,
        node: &mut parser::Node,
        generic_vars: &mut HashSet<String>,
    ) -> Rc<RefCell<Type>> {
        let ty = match &mut node.expr {
            Expr::Stmt(expr) => {
                self.analyze_expr(expr, generic_vars);
                Rc::clone(&node.r#type)
            }
            Expr::Integer(_) => Rc::clone(&node.r#type),
            Expr::String { .. } => Rc::clone(&node.r#type),
            Expr::Array {
                ref mut elements, ..
            } => {
                if elements.is_empty() {
                    return wrap(Type::Array(wrap(self.new_type_var())));
                }

                let mut element_types = elements
                    .iter_mut()
                    .map(|element| self.analyze_expr(element, generic_vars))
                    .collect::<Vec<_>>();

                let first_type = element_types.remove(0);
                let element_type =
                    element_types
                        .iter_mut()
                        .fold(&first_type, |previous_type, current_type| {
                            self.unify(&previous_type, &current_type);
                            current_type
                        });

                wrap(Type::Array(Rc::clone(element_type)))
            }
            Expr::Subscript { .. } => panic!("not implemented"),
            Expr::Identifier {
                ref name,
                ref binding,
            } => self
                .lookup(binding, generic_vars)
                .unwrap_or_else(|| panic!("Unbound variable `{}`", name)),
            Expr::Invocation {
                ref name,
                ref binding,
                arguments,
            } => match self.lookup_function(binding, generic_vars) {
                None => panic!("Unbound function `{}`", name),
                Some(function_type) => {
                    let mut m = arguments.iter_mut().collect::<Vec<_>>();
                    self.analyze_invocation(
                        Rc::clone(&function_type),
                        &node.r#type,
                        &mut m,
                        generic_vars,
                    )
                }
            },
            // binop
            Expr::Add(lhs, rhs, binding)
            | Expr::Sub(lhs, rhs, binding)
            | Expr::Rem(lhs, rhs, binding)
            | Expr::Mul(lhs, rhs, binding)
            | Expr::Div(lhs, rhs, binding)
            | Expr::LT(lhs, rhs, binding)
            | Expr::GT(lhs, rhs, binding)
            | Expr::LE(lhs, rhs, binding)
            | Expr::GE(lhs, rhs, binding)
            | Expr::EQ(lhs, rhs, binding)
            | Expr::NE(lhs, rhs, binding) => match self.lookup_function(binding, generic_vars) {
                None => panic!("Prelude not installed"),
                Some(function_type) => self.analyze_invocation(
                    Rc::clone(&function_type),
                    &node.r#type,
                    &mut [lhs.as_mut(), rhs.as_mut()],
                    generic_vars,
                ),
            },

            Expr::If {
                condition,
                then_body,
                else_body,
            } => {
                let cond_type = self.analyze_expr(condition, generic_vars);

                self.unify(&cond_type, &wrap(Type::Boolean));

                let then_type = self.analyze_body(then_body, generic_vars);
                let else_type = self.analyze_body(else_body, generic_vars);

                self.unify(&then_type, &else_type);
                self.unify(&then_type, &node.r#type);

                then_type
            }
            Expr::Case {
                arms,
                else_body,
                head,
                head_storage: _,
            } => {
                self.analyze_expr(head, generic_vars);

                // arms
                let mut body_types = vec![];

                for parser::CaseArm {
                    condition,
                    then_body,
                    ..
                } in arms
                {
                    // guard
                    if let Some(condition) = condition {
                        let cond_type = self.analyze_expr(condition, generic_vars);
                        self.unify(&cond_type, &wrap(Type::Boolean));
                    }

                    // body - unify each arm body with else body
                    let body_type = self.analyze_body(then_body, generic_vars);
                    body_types.push(body_type);
                }

                let else_type = self.analyze_body(else_body, generic_vars);

                // Unify body types with else clause's type.
                let case_type =
                    body_types
                        .iter()
                        .fold(&else_type, |previous_type, current_type| {
                            self.unify(previous_type, current_type);
                            current_type
                        });

                Rc::clone(case_type)
            }
            Expr::Var { pattern: _, init } => {
                self.analyze_expr(init, generic_vars);

                // Variable binding pattern always succeeds and its type is boolean.
                wrap(Type::Boolean)
            }
        };

        // To update node's type
        self.unify(&ty, &node.r#type);
        ty
    }
}

#[derive(Debug)]
enum Unification {
    ReplaceInstance(Rc<RefCell<Type>>),
    Unify(Rc<RefCell<Type>>, Rc<RefCell<Type>>),
    Done,
}

#[derive(Debug, PartialEq, Clone)]
enum UnificationError {
    RecursiveReference(Rc<RefCell<Type>>, Rc<RefCell<Type>>),
    NumberOfParamsMismatch(Rc<RefCell<Type>>, Rc<RefCell<Type>>, usize, usize),
    TypeMismatch(Rc<RefCell<Type>>, Rc<RefCell<Type>>),
}

impl TypeInferencer {
    fn lookup(
        &mut self,
        binding: &Option<Rc<RefCell<Binding>>>,
        generic_vars: &mut HashSet<String>,
    ) -> Option<Rc<RefCell<Type>>> {
        if let Some(binding) = binding {
            if let Binding::Variable { r#type: ref ty, .. } = *binding.borrow() {
                return Some(self.fresh(ty, generic_vars));
            }
        };

        None
    }

    fn lookup_function(
        &mut self,
        binding: &Option<Rc<RefCell<Binding>>>,
        generic_vars: &mut HashSet<String>,
    ) -> Option<Rc<RefCell<Type>>> {
        if let Some(binding) = binding {
            if let Binding::Function { r#type: ref ty, .. } = *binding.borrow() {
                return Some(self.fresh(ty, generic_vars));
            }
        };

        None
    }

    /// Several operations, for example type scheme instantiation, require
    /// fresh names for newly introduced type variables.
    /// This is implemented in both `fresh()` and `freshrec()` function, currently
    /// Nico doesn't support type scheme (generic type variable) though.
    ///
    /// Type operator and generic variables are duplicated; non-generic variables are shared.
    /// If the argument `ty` is a generic type variable, recreate a new type variable.
    fn fresh(
        &mut self,
        ty: &Rc<RefCell<Type>>,
        generic_vars: &mut HashSet<String>,
    ) -> Rc<RefCell<Type>> {
        let mut mappings = HashMap::new();
        self.freshrec(ty, generic_vars, &mut mappings)
    }

    fn freshrec(
        &mut self,
        ty: &Rc<RefCell<Type>>,
        generic_vars: &mut HashSet<String>,
        type_var_cache: &mut HashMap<String, Rc<RefCell<Type>>>,
    ) -> Rc<RefCell<Type>> {
        self.prune(ty);

        let freshed = match *ty.borrow() {
            Type::TypeVariable { ref name, .. } => {
                if !generic_vars.contains(name) {
                    return Rc::clone(&ty);
                } else if let Some(cached) = type_var_cache.get(name) {
                    return Rc::clone(cached);
                } else {
                    let cached = wrap(self.new_type_var());

                    type_var_cache.insert(name.clone(), Rc::clone(&cached));
                    return cached;
                }
            }
            // Type operators
            Type::Int32 => Type::Int32,
            Type::Boolean => Type::Boolean,
            Type::String => Type::String,
            Type::Void => Type::Void,
            Type::Array(ref element_type) => {
                let element_type = self.freshrec(element_type, generic_vars, type_var_cache);
                Type::Array(element_type)
            }
            Type::Function {
                ref params,
                ref return_type,
            } => {
                let params = params
                    .iter()
                    .map(|x| self.freshrec(x, generic_vars, type_var_cache))
                    .collect();
                let return_type = self.freshrec(return_type, generic_vars, type_var_cache);

                Type::Function {
                    params,
                    return_type,
                }
            }
        };

        wrap(freshed)
    }

    /// Prune the instance chain of type variables as much as possible.
    /// Note, this function leaves unresolvable variable like
    /// - `T -> U -> (None)`
    /// - `T -> (Not primitive type)`
    fn prune(&mut self, ty: &Rc<RefCell<Type>>) {
        // 1. Roll up instance chain until meets primitive type.
        // 2. Replace the content of RefCall with an instance if it is primitive type.
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

    fn new_type_var(&mut self) -> Type {
        Type::new_type_var(&self.generic_type_var_naming.next())
    }

    fn unify(&mut self, ty1: &Rc<RefCell<Type>>, ty2: &Rc<RefCell<Type>>) {
        match self._unify(ty1, ty2) {
            None => return,
            Some(error) => match error {
                UnificationError::RecursiveReference(_ty1, _ty2) => {
                    panic!("Recursive type reference detected.");
                }
                UnificationError::NumberOfParamsMismatch(ty1, ty2, n1, n2) => {
                    panic!(
                        "Wrong number of parameters. Expected {} but was {} in `{:?}` and `{:?}`",
                        n1, n2, ty1, ty2
                    );
                }
                UnificationError::TypeMismatch(ty1, ty2) => {
                    panic!("Type mismatch in `{:?}` and `{:?}`", ty1, ty2);
                }
            },
        }
    }

    fn _unify(
        &mut self,
        ty1: &Rc<RefCell<Type>>,
        ty2: &Rc<RefCell<Type>>,
    ) -> Option<UnificationError> {
        self.prune(ty1);
        self.prune(ty2);

        let action = match *ty1.borrow() {
            Type::TypeVariable { .. } => {
                if *ty1 != *ty2 {
                    if (*ty1).borrow().contains(&*ty2.borrow()) {
                        return Some(UnificationError::RecursiveReference(
                            Rc::clone(ty1),
                            Rc::clone(ty2),
                        ));
                    }
                    Unification::ReplaceInstance(Rc::clone(ty2))
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
                        return Some(UnificationError::NumberOfParamsMismatch(
                            Rc::clone(ty1),
                            Rc::clone(ty2),
                            params1.len(),
                            params2.len(),
                        ));
                    }

                    for (x, y) in params1.iter().zip(params2.iter()) {
                        if let Some(error) = self._unify(x, y) {
                            return Some(error);
                        }
                    }
                    if let Some(error) = self._unify(return_type1, return_type2) {
                        return Some(error);
                    }
                    Unification::Done
                }
                Type::TypeVariable { .. } => Unification::Unify(Rc::clone(ty2), Rc::clone(ty1)),
                _ => {
                    return Some(UnificationError::TypeMismatch(
                        Rc::clone(ty1),
                        Rc::clone(ty2),
                    ));
                }
            },
            _ => match *ty2.borrow() {
                ref t2 if t2.eq(&*ty1.borrow()) => Unification::Done,
                Type::TypeVariable { .. } => Unification::Unify(Rc::clone(ty2), Rc::clone(ty1)),
                _ => {
                    return Some(UnificationError::TypeMismatch(
                        Rc::clone(ty1),
                        Rc::clone(ty2),
                    ));
                }
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
                None
            }
            Unification::Unify(ref ty1, ref ty2) => self._unify(&Rc::clone(ty1), &Rc::clone(ty2)),
            Unification::Done => None,
        }
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

        let error = inferencer._unify(&pty0, &pty1);
        assert!(error.is_none());

        assert_matches!(*pty0.borrow(), Type::Int32);
        assert_matches!(*pty1.borrow(), Type::Int32);
    }

    #[test]
    fn unify_boolean() {
        let mut inferencer = TypeInferencer::new();
        let pty0 = wrap(Type::Boolean);
        let pty1 = wrap(Type::Boolean);

        let error = inferencer._unify(&pty0, &pty1);
        assert!(error.is_none());

        assert_matches!(*pty0.borrow(), Type::Boolean);
        assert_matches!(*pty1.borrow(), Type::Boolean);
    }

    #[test]
    fn unify_string() {
        let mut inferencer = TypeInferencer::new();
        let pty0 = wrap(Type::String);
        let pty1 = wrap(Type::String);

        let error = inferencer._unify(&pty0, &pty1);
        assert!(error.is_none());

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

        let error = inferencer._unify(&pty0, &pty1);
        assert!(error.is_none());

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

        let error = inferencer._unify(&pty0, &pty1);
        assert!(error.is_none());

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
        let mut generic_vars = HashSet::new();
        let pty0 = wrap(Type::Int32);
        let pty1 = inferencer.fresh(&pty0, &mut generic_vars);

        assert_eq!(pty0, pty1);
    }

    #[test]
    fn fresh_function() {
        let mut inferencer = TypeInferencer::new();
        let mut generic_vars = HashSet::new();

        let pty0 = Rc::new(RefCell::new(Type::Function {
            params: vec![],
            return_type: wrap(Type::Boolean),
        }));
        let pty1 = inferencer.fresh(&pty0, &mut generic_vars);

        assert_eq!(pty0, pty1);
    }

    #[test]
    fn fresh_typevar() {
        let mut inferencer = TypeInferencer::new();
        let mut generic_vars = HashSet::new();
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

        generic_vars.insert("$1".to_string());
        generic_vars.insert("$2".to_string());

        let fresh0 = inferencer.freshrec(&pty0, &mut generic_vars, &mut mappings);
        let fresh1 = inferencer.freshrec(&pty1, &mut generic_vars, &mut mappings);

        // should be cached
        let cache0 = inferencer.freshrec(&pty0, &mut generic_vars, &mut mappings);
        let cache1 = inferencer.freshrec(&pty1, &mut generic_vars, &mut mappings);

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

    #[test]
    fn array_1() {
        let mut module = parser::parse_string("[1, 2]");

        analyze(&mut module);

        let function = &module.main.unwrap();
        let body = &function.body;

        assert_matches!(function.r#type, ref ty => {
            assert_matches!(*ty.borrow(), Type::Function{ ref return_type, .. } => {
                let return_type = Type::unwrap(return_type);

                assert_matches!(*return_type.borrow(), Type::Array( ref element_type ) => {
                    assert_eq!(*element_type.borrow(), Type::Int32);
                });
            });
        });

        assert_matches!(body[0].r#type, ref ty => {
            let ty = Type::unwrap(ty);

            assert_matches!(*ty.borrow(), Type::Array( ref element_type ) => {
                assert_eq!(*element_type.borrow(), Type::Int32);
            });
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
