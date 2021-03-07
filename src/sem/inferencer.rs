//! Implements type inference.
//!
//! Hindley–Milner type system and Algorithm W
//! https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system#Algorithm_W
use crate::parser;
use crate::parser::Expr;
use crate::sem::{Binding, SemanticAnalyzer, Type};
use crate::util::naming::PrefixNaming;
use crate::util::wrap;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

const DEBUG: bool = false;

#[derive(Debug)]
pub struct TypeInferencer {
    generic_type_var_naming: PrefixNaming,
}

impl Default for TypeInferencer {
    fn default() -> Self {
        TypeInferencer::new()
    }
}

impl SemanticAnalyzer for TypeInferencer {
    fn analyze(&mut self, module: &mut parser::Module) {
        for function in &mut module.functions {
            self.analyze_function(function);
        }
        if let Some(ref mut function) = module.main {
            self.analyze_function(function);
        }

        // Replace type variables whose actual type is fixed with the actual type.
        for function in &mut module.functions {
            self.fix_function(function);
        }
        if let Some(ref mut function) = module.main {
            self.fix_function(function);
        }
    }
}

impl TypeInferencer {
    pub fn new() -> TypeInferencer {
        TypeInferencer {
            generic_type_var_naming: PrefixNaming::new("$GENERIC"),
        }
    }

    fn analyze_function(&mut self, function: &mut parser::Function) -> Rc<RefCell<Type>> {
        // Generic type var names. Nico doesn't support generic type vars though.
        // See `freshrec()` funciton.
        let mut generic_vars = HashSet::new();

        // Iterates expressions. Type::Void for empty expression.
        let retty = self.analyze_body(&mut function.body, &mut generic_vars);

        // Unify return type from body.
        match &*function.r#type.borrow() {
            Type::Function { return_type, .. } => {
                self.unify_and_log(
                    format!("return type of fun `{}` (body, ret)", function.name),
                    &retty,
                    return_type,
                );
            }
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

        self.unify_and_log("type of invocation (f, call)", &function_type, &callsite);
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

                // The type of a statement is always `Void`.
                wrap(Type::Void)
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
            Expr::Subscript { operand, index } => {
                let operand_type = {
                    let generic_element_typename = self.generic_type_var_naming.next();

                    //scoped_generic_vars.insert(generic_element_typename.clone());

                    let operand_type = self.analyze_expr(operand, generic_vars);

                    self.unify_and_log(
                        "subscript (operand, T[])",
                        &operand_type,
                        &wrap(Type::Array(wrap(Type::new_type_var(
                            &generic_element_typename,
                        )))),
                    );

                    fixed_type(&operand_type)
                };

                let element_type = match &*operand_type.borrow() {
                    Type::Array(element_type) => Rc::clone(element_type),
                    ty => panic!("Operand must be an array, but was {:?}", ty),
                };

                // `index` must be an integer
                let index_type = self.analyze_expr(index, generic_vars);
                self.unify_and_log("subscript (index, i32)", &index_type, &wrap(Type::Int32));

                element_type
            }
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

                if let Some(else_body) = else_body {
                    let else_type = self.analyze_body(else_body, generic_vars);
                    self.unify(&then_type, &else_type);
                    then_type
                } else {
                    // The return type of a `if` expression without `else` is
                    // always `Void`.
                    wrap(Type::Void)
                }
            }
            Expr::Case {
                arms,
                else_body,
                head,
                head_storage: _,
            } => {
                self.analyze_expr(head, generic_vars);

                // arms
                let mut case_type = None;

                for parser::CaseArm {
                    condition,
                    then_body,
                    pattern,
                } in arms
                {
                    // Type check for pattern match
                    match pattern {
                        parser::Pattern::Variable(_name, ref mut binding) => {
                            // Variable patern's type must be identical to head expression.
                            let binding_type = &binding.borrow().r#type;
                            self.unify(binding_type, &head.r#type);
                        }
                        parser::Pattern::Integer(_) => {
                            self.unify(&wrap(Type::Int32), &head.r#type);
                        }
                        parser::Pattern::Array(_) => todo!(),
                    };

                    // Guard' type must be boolean.
                    if let Some(condition) = condition {
                        let cond_type = self.analyze_expr(condition, generic_vars);
                        self.unify(&cond_type, &wrap(Type::Boolean));
                    }

                    let body_type = self.analyze_body(then_body, generic_vars);

                    if let Some(ref case_type) = case_type {
                        self.unify(case_type, &body_type);
                    } else {
                        case_type = Some(body_type)
                    }
                }

                let case_type = case_type.unwrap();

                if let Some(else_body) = else_body {
                    let else_type = self.analyze_body(else_body, generic_vars);

                    self.unify(&case_type, &else_type);
                }

                Rc::clone(&case_type)
            }
            Expr::Var {
                ref mut pattern,
                init,
            } => {
                self.analyze_expr(init, generic_vars);

                match pattern {
                    parser::Pattern::Variable(_name, ref mut binding) => {
                        // Variable patern's type must be identical to init expression.
                        let binding_type = &binding.borrow().r#type;
                        self.unify(binding_type, &init.r#type);
                    }
                    parser::Pattern::Array(_) => todo!(),
                    _ => {}
                };

                // Variable binding pattern always succeeds and its type is boolean.
                wrap(Type::Boolean)
            }
        };

        // To update node's type
        self.unify_and_log("(ty, node)", &ty, &node.r#type);
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
            let binding = binding.borrow();
            return Some(self.fresh(&binding.r#type, generic_vars));
        };

        None
    }

    fn lookup_function(
        &mut self,
        binding: &Option<Rc<RefCell<Binding>>>,
        generic_vars: &mut HashSet<String>,
    ) -> Option<Rc<RefCell<Type>>> {
        if let Some(binding) = binding {
            let binding = binding.borrow();

            match *binding.r#type.borrow() {
                Type::Function { .. } => {}
                ref ty => panic!(
                    "Missing function named `{}` found type `{}`",
                    binding.name, ty
                ),
            }
            return Some(self.fresh(&binding.r#type, generic_vars));
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
        let ty = self.prune(ty);

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
    /// However this function can't replace top TypeVariable with
    /// a composite type (like Function, Array).
    ///
    /// This function returns the instance type of top TypeVariable instead.
    fn prune(&mut self, ty: &Rc<RefCell<Type>>) -> Rc<RefCell<Type>> {
        // Prune descendants and retrieve the type at the deepest level.
        let terminal = match *ty.borrow_mut() {
            Type::TypeVariable {
                ref mut instance, ..
            } => match instance {
                None => return Rc::clone(ty),
                Some(ref i) => {
                    let n = self.prune(i);

                    instance.replace(Rc::clone(&n));
                    Rc::clone(&n)
                }
            },
            _ => {
                // We don't need to prune anymore.
                return Rc::clone(ty);
            }
        };

        // Replace instance with terminal type if it is
        // a primitive type.
        match *terminal.borrow() {
            Type::Int32 => ty.replace(Type::Int32),
            Type::Boolean => ty.replace(Type::Boolean),
            Type::String => ty.replace(Type::String),
            Type::Void => ty.replace(Type::Void),
            _ => {
                return Rc::clone(&terminal);
            }
        };

        Rc::clone(ty)
    }

    fn new_type_var(&mut self) -> Type {
        Type::new_type_var(&self.generic_type_var_naming.next())
    }

    fn unify_and_log<S: AsRef<str>>(
        &mut self,
        message: S,
        ty1: &Rc<RefCell<Type>>,
        ty2: &Rc<RefCell<Type>>,
    ) {
        if DEBUG {
            eprintln!(
                "[unify] {}: {}, {}",
                message.as_ref(),
                ty1.borrow(),
                ty2.borrow()
            );
        }

        self.unify(ty1, ty2);

        if DEBUG {
            eprintln!(
                "[unify] --> {}: {}, {}",
                message.as_ref(),
                ty1.borrow(),
                ty2.borrow()
            );
        }
    }

    fn unify(&mut self, ty1: &Rc<RefCell<Type>>, ty2: &Rc<RefCell<Type>>) {
        if let Some(error) = self._unify(ty1, ty2) {
            match error {
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
            };
        }
    }

    fn _unify(
        &mut self,
        ty1: &Rc<RefCell<Type>>,
        ty2: &Rc<RefCell<Type>>,
    ) -> Option<UnificationError> {
        let ty1 = &self.prune(ty1);
        let ty2 = &self.prune(ty2);

        let action = match &*ty1.borrow() {
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
            Type::Array(element_type1) => match &*ty2.borrow() {
                Type::Array(element_type2) => {
                    if let Some(error) = self._unify(element_type1, element_type2) {
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

        match &action {
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
            Unification::Unify(ty1, ty2) => self._unify(&Rc::clone(ty1), &Rc::clone(ty2)),
            Unification::Done => None,
        }
    }
}

// Prune fixed type variables and remove indirection.
pub fn fixed_type(ty: &Rc<RefCell<Type>>) -> Rc<RefCell<Type>> {
    match &*ty.borrow() {
        Type::Array(element_type) => wrap(Type::Array(fixed_type(&element_type))),
        Type::Function {
            params,
            return_type,
        } => wrap(Type::Function {
            params: params.iter().map(|p| fixed_type(p)).collect(),
            return_type: fixed_type(return_type),
        }),
        Type::TypeVariable {
            instance: Some(instance),
            ..
        } => fixed_type(instance),

        Type::TypeVariable { instance: None, .. } => {
            // If the type is not yet fixed, returns it.
            Rc::clone(ty)
        }
        _ => Rc::clone(ty),
    }
}

impl TypeInferencer {
    fn fix_function(&self, function: &mut parser::Function) {
        for binding in &mut function.params {
            match *binding.borrow_mut() {
                Binding { ref mut r#type, .. } => *r#type = fixed_type(r#type),
            };
        }

        self.fix_body(&mut function.body);
        function.r#type = fixed_type(&function.r#type);
    }

    fn fix_body(&self, body: &mut Vec<parser::Node>) {
        for node in body {
            self.fix_expr(node);
        }
    }

    fn fix_expr(&self, node: &mut parser::Node) {
        node.r#type = fixed_type(&node.r#type);

        match &mut node.expr {
            Expr::Stmt(expr) => {
                self.fix_expr(expr);
            }
            Expr::Integer(_) => {}
            Expr::String { .. } => {}
            Expr::Array {
                ref mut elements, ..
            } => {
                for element in elements {
                    self.fix_expr(element);
                }
            }
            Expr::Subscript { operand, index } => {
                self.fix_expr(operand);
                self.fix_expr(index);
            }
            Expr::Identifier { .. } => {}
            Expr::Invocation { arguments, .. } => {
                for argument in arguments {
                    self.fix_expr(argument);
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
                self.fix_expr(lhs);
                self.fix_expr(rhs);
            }
            Expr::If {
                condition,
                then_body,
                else_body,
            } => {
                self.fix_expr(condition);
                self.fix_body(then_body);
                if let Some(else_body) = else_body {
                    self.fix_body(else_body);
                }
            }
            Expr::Case {
                arms,
                else_body,
                head,
                head_storage: _,
            } => {
                self.fix_expr(head);

                for parser::CaseArm {
                    condition,
                    then_body,
                    pattern,
                } in arms
                {
                    self.fix_pattern(pattern);

                    if let Some(condition) = condition {
                        self.fix_expr(condition);
                    }

                    self.fix_body(then_body);
                }

                if let Some(else_body) = else_body {
                    self.fix_body(else_body);
                }
            }
            Expr::Var { pattern, init } => {
                self.fix_expr(init);
                self.fix_pattern(pattern);
            }
        };
    }

    fn fix_pattern(&self, pattern: &mut parser::Pattern) {
        match pattern {
            parser::Pattern::Variable(_name, ref mut binding) => match *binding.borrow_mut() {
                Binding { ref mut r#type, .. } => {
                    *r#type = fixed_type(r#type);
                }
            },
            parser::Pattern::Integer(_) => {}
            parser::Pattern::Array(_) => todo!(),
        };
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
            assert!(instance.is_some());
            assert_matches!(*instance.as_ref().unwrap().borrow(), Type::TypeVariable {
                ref name,
                ref instance,
            } => {
                assert_eq!(name, "b");
                assert!(instance.is_none());
            });
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

    fn analyze(module: &mut parser::Module) -> TypeInferencer {
        let mut binder = Binder::new();
        let mut inferencer = TypeInferencer::new();

        binder.analyze(module);
        inferencer.analyze(module);

        inferencer
    }
}
