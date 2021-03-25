//! Implements type inference.
//!
//! Hindley–Milner type system and Algorithm W
//! https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system#Algorithm_W
use crate::parser;
use crate::parser::Expr;
use crate::sem;
use crate::sem::{Binding, Type};
use crate::util::naming::PrefixNaming;
use crate::util::wrap;
use std::cell::RefCell;
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

impl sem::SemanticAnalyzer for TypeInferencer {
    fn analyze(&mut self, module: &mut parser::Module) {
        if let Some(ref mut function) = module.main {
            self.analyze_function(function);
        }
        for function in &mut module.functions {
            self.analyze_function(function);
        }

        // Replace type variables whose actual type is fixed with the actual type.
        let fixer = TypeFixer::default();

        if let Some(ref mut function) = module.main {
            fixer.fix_function(function);
        }
        for function in &mut module.functions {
            fixer.fix_function(function);
        }
    }
}

impl TypeInferencer {
    pub fn new() -> TypeInferencer {
        TypeInferencer {
            // Assign a different prefix from parser.
            // TODO: Create a compiler context and passing it to parser, inferencer and others.
            generic_type_var_naming: PrefixNaming::new("$."),
        }
    }

    fn analyze_function(&mut self, function: &mut parser::Function) -> Rc<RefCell<Type>> {
        // Iterates expressions. Type::Void for empty expression.
        let retty = self.analyze_body(&mut function.body);

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
        binding: &Option<Rc<RefCell<Binding>>>,
        function_type: Rc<RefCell<Type>>,
        retty: &Rc<RefCell<Type>>,
        args: &mut [&mut parser::Node],
    ) -> Rc<RefCell<Type>> {
        let arg_types = args
            .iter_mut()
            .map(|nd| self.analyze_expr(nd))
            .collect::<Vec<_>>();
        let call_site = wrap(Type::Function {
            params: arg_types,
            return_type: Rc::clone(retty),
        });

        // invocation must have a binding
        let binding = binding.as_ref().unwrap().borrow();
        let name = binding.name.as_ref().unwrap();

        self.unify_and_log(
            format!("invocation `{}` (fun, caller)", name),
            &function_type,
            &call_site,
        );
        Rc::clone(retty)
    }

    fn analyze_body(&mut self, body: &mut Vec<parser::Node>) -> Rc<RefCell<Type>> {
        // Iterates expressions. Type::Void for empty expression.
        body.iter_mut()
            .fold(wrap(Type::Void), |_retty, node| self.analyze_expr(node))
    }

    fn analyze_expr(&mut self, node: &mut parser::Node) -> Rc<RefCell<Type>> {
        let ty = match &mut node.expr {
            Expr::Stmt(expr) => {
                self.analyze_expr(expr);

                // The type of a statement is always `Void`.
                wrap(Type::Void)
            }
            Expr::Integer(_) => Rc::clone(&node.r#type),
            Expr::String { .. } => Rc::clone(&node.r#type),
            Expr::Array {
                ref mut elements, ..
            } => {
                let mut element_types = elements
                    .iter_mut()
                    .map(|element| self.analyze_expr(element))
                    .collect::<Vec<_>>();

                let element_type = if element_types.is_empty() {
                    wrap(self.new_type_var())
                } else {
                    let first_element = element_types.remove(0);

                    element_types
                        .iter()
                        .fold(first_element, |previous_type, current_type| {
                            self.unify(&previous_type, current_type);
                            Rc::clone(current_type)
                        })
                };

                wrap(Type::Array(element_type))
            }
            Expr::Struct {
                fields: value_fields,
                ..
            } => {
                let struct_type = node.r#type.borrow();
                let (struct_name, type_fields) = match *struct_type {
                    Type::Struct {
                        ref name,
                        ref fields,
                    } => (name, fields),
                    ref ty => panic!("Expected struct type, but was {}", ty),
                };

                for value_field in value_fields {
                    let field_type = type_fields.get(&value_field.name).unwrap_or_else(|| {
                        panic!(
                            "Unknown filed `{}` for struct {}",
                            value_field.name, struct_name
                        )
                    });

                    let value_type = self.analyze_expr(&mut value_field.value);
                    self.unify_and_log("field (type, value)", field_type, &value_type);
                }

                Rc::clone(&node.r#type)
            }
            Expr::Subscript { operand, index, .. } => {
                let operand_type = {
                    let operand_type = self.analyze_expr(operand);

                    // Operand must be Array<T>
                    let array_type = self.typed_array_constraint();

                    self.unify_and_log(
                        "subscript (operand, T[])",
                        &operand_type,
                        &wrap(array_type),
                    );

                    self.prune(&operand_type)
                };

                let element_type = Type::unwrap_element_type_or_else(&operand_type, |ty| {
                    panic!("Operand must be an array, but was {:?}", ty);
                });

                // `index` must be an integer
                let index_type = self.analyze_expr(index);
                self.unify_and_log("subscript (index, i32)", &index_type, &wrap(Type::Int32));

                element_type
            }
            Expr::Access { operand, ref field } => {
                let operand_type = {
                    let operand_type = self.analyze_expr(operand);

                    // Operand must be compatible with `struct { field: T }`
                    let struct_type = self.struct_fields_constraint(&[field]);

                    self.unify_and_log(
                        "access (operand, struct)",
                        &operand_type,
                        &wrap(struct_type),
                    );

                    self.prune(&operand_type)
                };
                let struct_type = operand_type.borrow();
                let type_fields = match &*struct_type {
                    Type::Struct { fields, .. } | Type::IncompleteStruct { fields, .. } => fields,
                    ref ty => panic!("Expected struct type, but was {}", ty),
                };

                let field_type = type_fields
                    .get(field)
                    .unwrap_or_else(|| panic!("No filed `{}` found in {}", field, struct_type));

                Rc::clone(field_type)
            }
            Expr::Identifier {
                ref name,
                ref binding,
            } => self
                .lookup(binding)
                .unwrap_or_else(|| panic!("Unbound variable `{}`", name)),
            Expr::Invocation {
                ref name,
                binding,
                arguments,
            } => match self.lookup_function(binding) {
                None => panic!("Unbound function `{}`", name),
                Some(function_type) => {
                    let mut m = arguments.iter_mut().collect::<Vec<_>>();
                    self.analyze_invocation(
                        binding,
                        Rc::clone(&function_type),
                        &node.r#type,
                        &mut m,
                    )
                }
            },
            Expr::Add(lhs, rhs, binding)
            | Expr::Sub(lhs, rhs, binding)
            | Expr::Rem(lhs, rhs, binding)
            | Expr::Mul(lhs, rhs, binding)
            | Expr::Div(lhs, rhs, binding)
            | Expr::Lt(lhs, rhs, binding)
            | Expr::Gt(lhs, rhs, binding)
            | Expr::Le(lhs, rhs, binding)
            | Expr::Ge(lhs, rhs, binding)
            | Expr::Eq(lhs, rhs, binding)
            | Expr::Ne(lhs, rhs, binding) => match self.lookup_function(binding) {
                None => panic!("Prelude not installed"),
                Some(function_type) => self.analyze_invocation(
                    binding,
                    Rc::clone(&function_type),
                    &node.r#type,
                    &mut [lhs.as_mut(), rhs.as_mut()],
                ),
            },
            Expr::Plus(operand, binding) | Expr::Minus(operand, binding) => {
                match self.lookup_function(binding) {
                    None => panic!("Prelude not installed"),
                    Some(function_type) => self.analyze_invocation(
                        binding,
                        Rc::clone(&function_type),
                        &node.r#type,
                        &mut [operand.as_mut()],
                    ),
                }
            }
            Expr::If {
                condition,
                then_body,
                else_body,
            } => {
                let cond_type = self.analyze_expr(condition);

                self.unify(&cond_type, &wrap(Type::Boolean));

                let then_type = self.analyze_body(then_body);

                if let Some(else_body) = else_body {
                    let else_type = self.analyze_body(else_body);
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
                self.analyze_expr(head);

                // arms
                let mut case_type = None;

                for parser::CaseArm {
                    condition,
                    then_body,
                    pattern,
                } in arms
                {
                    self.analyze_pattern(pattern, &head.r#type);

                    // Guard' type must be boolean.
                    if let Some(condition) = condition {
                        let cond_type = self.analyze_expr(condition);
                        self.unify(&cond_type, &wrap(Type::Boolean));
                    }

                    let body_type = self.analyze_body(then_body);

                    if let Some(ref case_type) = case_type {
                        self.unify(case_type, &body_type);
                    } else {
                        case_type = Some(body_type)
                    }
                }

                let case_type = case_type.unwrap();

                if let Some(else_body) = else_body {
                    let else_type = self.analyze_body(else_body);

                    self.unify(&case_type, &else_type);
                }

                Rc::clone(&case_type)
            }
            Expr::Var {
                ref mut pattern,
                init,
            } => {
                self.analyze_expr(init);
                self.analyze_pattern(pattern, &init.r#type);

                // Variable binding pattern always succeeds and its type is boolean.
                wrap(Type::Boolean)
            }
        };

        // To update node's type
        self.unify_and_log(
            format!("node: {}", node.expr.short_name()),
            &node.r#type,
            &ty,
        );
        Rc::clone(&node.r#type)
    }

    fn analyze_pattern(&mut self, pattern: &mut parser::Pattern, target_type: &Rc<RefCell<Type>>) {
        match pattern {
            parser::Pattern::Variable(_name, ref mut binding) => {
                // Variable pattern's type must be identical to head expression.
                let binding_type = &binding.borrow().r#type;
                self.unify_and_log(
                    "variable pattern (pattern, target)",
                    binding_type,
                    target_type,
                );
            }
            parser::Pattern::Integer(_) => {
                self.unify_and_log(
                    "i32 pattern (pattern, target)",
                    &wrap(Type::Int32),
                    target_type,
                );
            }
            parser::Pattern::Array(patterns) => {
                // Head expression's type must be Array<T>
                let array_type = self.typed_array_constraint();

                if let Some(err) = self._unify(&target_type, &wrap(array_type)) {
                    match err {
                        UnificationError::TypeMismatch(actual, _expected) => {
                            panic!("mismatched type: expected T[], found {}", actual.borrow());
                        }
                        _ => self._panic_unification_error(&err),
                    };
                };

                let target_type = self.prune(target_type);

                let element_type = Type::unwrap_element_type_or_else(&target_type, |ty| {
                    panic!("mismatched type: expected T[], found {}", ty);
                });

                for pattern in patterns {
                    self.analyze_pattern(pattern, &element_type);
                }
            }
            parser::Pattern::Struct { r#type, fields, .. } => {
                let struct_type = if let Some(struct_type) = r#type {
                    Rc::clone(struct_type)
                } else {
                    let fields = fields.iter().map(|x| x.name.as_ref()).collect::<Vec<_>>();
                    wrap(self.struct_fields_constraint(&fields))
                };

                self.unify_and_log("struct pattern", &target_type, &struct_type);

                r#type.replace(Rc::clone(&target_type));

                let target_type = self.prune(target_type);
                let target_type = target_type.borrow();

                let type_fields = match &*target_type {
                    Type::Struct { fields, .. } => fields,
                    ref ty => panic!("Expected struct type, but was {}", ty),
                };

                for field in fields {
                    let field_type = type_fields.get(&field.name).unwrap();
                    self.analyze_pattern(&mut field.pattern, field_type);
                }
            }
            parser::Pattern::Rest {
                ref mut binding, ..
            } => {
                // For rest pattern, the target type `T` must be an element type.
                // And then, the rest pattern's type must be `T[]`.
                let element_type = self.prune(target_type);
                let target_type = wrap(Type::Array(element_type));

                let binding_type = &binding.borrow().r#type;
                self.unify_and_log("rest pattern (pattern, target)", binding_type, &target_type);
            }
        };
    }
}

#[derive(Debug)]
enum Unification {
    ReplaceInstance(Rc<RefCell<Type>>),
    ReplaceIncompleteStruct(Rc<RefCell<Type>>),
    Unify(Rc<RefCell<Type>>, Rc<RefCell<Type>>),
    FallthroughGeneric,
    Done,
}

#[derive(Debug, PartialEq, Clone)]
enum UnificationError {
    RecursiveReference(Rc<RefCell<Type>>, Rc<RefCell<Type>>),
    NumberOfParamsMismatch(Rc<RefCell<Type>>, Rc<RefCell<Type>>, usize, usize),
    TypeMismatch(Rc<RefCell<Type>>, Rc<RefCell<Type>>),
}

impl TypeInferencer {
    fn lookup(&mut self, binding: &Option<Rc<RefCell<Binding>>>) -> Option<Rc<RefCell<Type>>> {
        binding.as_ref().map(|b| Rc::clone(&b.borrow().r#type))
    }

    fn lookup_function(
        &mut self,
        binding: &Option<Rc<RefCell<Binding>>>,
    ) -> Option<Rc<RefCell<Type>>> {
        if let Some(binding) = binding {
            let binding = binding.borrow();
            let name = binding.name.as_ref().map_or("(unknown)", |s| &s);

            match *binding.r#type.borrow() {
                Type::Function { .. } => {}
                ref ty => {
                    panic!("Missing function named `{}` found type `{}`", name, ty)
                }
            }
            return Some(Rc::clone(&binding.r#type));
        };

        None
    }

    /// Prunes a chain of type variables as much as possible, returning
    /// the "leaf" instance type or the type variable if an instance is
    /// not present.
    ///
    /// ```ignore
    /// T1 -> T2 -> T3
    /// ```
    ///
    /// to:
    ///
    /// ```ignore
    /// T1 -> T3
    /// T2 -> T3
    /// ```
    fn prune(&mut self, ty: &Rc<RefCell<Type>>) -> Rc<RefCell<Type>> {
        match *ty.borrow_mut() {
            Type::TypeVariable { instance: None, .. } => Rc::clone(ty),
            Type::TypeVariable {
                ref mut instance, ..
            } => {
                let pruned = self.prune(instance.as_ref().unwrap());

                instance.replace(Rc::clone(&pruned));
                pruned
            }
            _ => Rc::clone(ty),
        }
    }

    /// T
    fn new_type_var(&mut self) -> Type {
        Type::new_type_var(&self.generic_type_var_naming.next())
    }

    /// T -> C
    fn new_typed_var(&mut self, ty: &Rc<RefCell<Type>>) -> Type {
        Type::TypeVariable {
            name: self.generic_type_var_naming.next(),
            instance: Some(Rc::clone(ty)),
        }
    }

    /// Array<T>
    fn typed_array_constraint(&mut self) -> Type {
        let ty = self.new_type_var();
        Type::Array(wrap(ty))
    }

    // { field: T }
    fn struct_fields_constraint(&mut self, fields: &[&str]) -> Type {
        let fields = fields
            .iter()
            .map(|x| {
                let ty = self.new_type_var();
                (x.to_string(), wrap(ty))
            })
            .collect();

        Type::IncompleteStruct { fields }
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
            self._panic_unification_error(&error);
        }
    }

    fn _panic_unification_error(&self, error: &UnificationError) {
        match error {
            UnificationError::RecursiveReference(_ty1, _ty2) => {
                panic!("Recursive type reference detected.");
            }
            UnificationError::NumberOfParamsMismatch(ty1, ty2, n1, n2) => {
                panic!(
                    "Wrong number of parameters. Expected {} but was {} in `{}` and `{}`",
                    n1,
                    n2,
                    ty1.borrow(),
                    ty2.borrow()
                );
            }
            UnificationError::TypeMismatch(ty1, ty2) => {
                panic!("Type mismatch in `{}` and `{}`", ty1.borrow(), ty2.borrow());
            }
        };
    }

    fn _unify(
        &mut self,
        ty1: &Rc<RefCell<Type>>,
        ty2: &Rc<RefCell<Type>>,
    ) -> Option<UnificationError> {
        let ty1 = &self.prune(ty1);
        let ty2 = &self.prune(ty2);

        let mut action = match &*ty1.borrow() {
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
                _ => Unification::FallthroughGeneric,
            },
            Type::Struct {
                fields: fields1, ..
            } => match &*ty2.borrow() {
                Type::IncompleteStruct { fields: fields2 } => {
                    // Unify types in Fields2 with Fields1.
                    for (field_name2, field_type2) in fields2 {
                        if let Some(field_type1) = fields1.get(field_name2) {
                            // Both fields1 and fields2 contain same named field.
                            if let Some(error) = self._unify(field_type1, field_type2) {
                                return Some(error);
                            }
                        } else {
                            // Struct doesn't contain a field which is contained in the incomplete struct.
                            return Some(UnificationError::TypeMismatch(
                                Rc::clone(ty1),
                                Rc::clone(ty2),
                            ));
                        }
                    }

                    Unification::ReplaceIncompleteStruct(Rc::clone(&ty1))
                }
                _ => Unification::FallthroughGeneric,
            },
            Type::IncompleteStruct { fields: fields1 } => match &*ty2.borrow() {
                Type::IncompleteStruct { fields: fields2 } => {
                    let mut new_fields = fields1.clone();

                    // Unify types in (Fields1 & Fields2).
                    for (name2, ty2) in fields2 {
                        if let Some(ty1) = fields1.get(name2) {
                            // Both fields1 and fields2 contain same named field.
                            // Unifies types and it should be already added to new_fields.
                            if let Some(error) = self._unify(ty1, ty2) {
                                return Some(error);
                            }
                        } else {
                            // Fields2 contains a field which is not included in the Fields2.
                            new_fields.insert(name2.clone(), Rc::clone(ty2));
                        }
                    }

                    Unification::ReplaceIncompleteStruct(wrap(Type::IncompleteStruct {
                        fields: new_fields,
                    }))
                }
                Type::Struct { .. } => Unification::Unify(Rc::clone(ty2), Rc::clone(ty1)),
                _ => Unification::FallthroughGeneric,
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
                _ => Unification::FallthroughGeneric,
            },
            _ => Unification::FallthroughGeneric,
        };

        if let Unification::FallthroughGeneric = action {
            action = match *ty2.borrow() {
                ref t2 if t2.eq(&*ty1.borrow()) => Unification::Done,
                Type::TypeVariable { .. } => Unification::Unify(Rc::clone(ty2), Rc::clone(ty1)),
                _ => {
                    return Some(UnificationError::TypeMismatch(
                        Rc::clone(ty1),
                        Rc::clone(ty2),
                    ));
                }
            };
        }

        match action {
            Unification::ReplaceInstance(new_instance) => {
                if let Type::TypeVariable {
                    ref mut instance, ..
                } = *ty1.borrow_mut()
                {
                    instance.replace(Rc::clone(&new_instance));
                }
                None
            }
            Unification::ReplaceIncompleteStruct(ty) => {
                if matches!(*ty1.borrow(), Type::IncompleteStruct { .. }) {
                    ty1.replace(self.new_typed_var(&ty));
                }
                if matches!(*ty2.borrow(), Type::IncompleteStruct { .. }) {
                    ty2.replace(self.new_typed_var(&ty));
                }

                None
            }
            Unification::Unify(ty1, ty2) => self._unify(&ty1, &ty2),
            Unification::Done => None,
            Unification::FallthroughGeneric => unreachable!(),
        }
    }
}

#[derive(Debug, Default)]
struct TypeFixer {}

impl TypeFixer {
    fn fixed_type_and_log(&self, message: &str, ty: &Rc<RefCell<Type>>) -> Rc<RefCell<Type>> {
        let new_type = self.fixed_type(ty);

        if DEBUG {
            eprintln!("[fix] {} {} -> {}", message, ty.borrow(), new_type.borrow());
        }

        new_type
    }

    // Prune fixed type variables and remove indirection.
    pub fn fixed_type(&self, ty: &Rc<RefCell<Type>>) -> Rc<RefCell<Type>> {
        match &*ty.borrow() {
            Type::Array(element_type) => wrap(Type::Array(self.fixed_type(&element_type))),
            Type::Struct { name, fields } => {
                let fields = fields
                    .iter()
                    .map(|(name, ty)| (name.clone(), Rc::clone(ty)))
                    .collect();

                wrap(Type::Struct {
                    name: name.clone(),
                    fields,
                })
            }
            Type::Function {
                params,
                return_type,
            } => wrap(Type::Function {
                params: params.iter().map(|p| self.fixed_type(p)).collect(),
                return_type: self.fixed_type(return_type),
            }),
            Type::TypeVariable {
                instance: Some(instance),
                ..
            } => self.fixed_type(instance),

            Type::TypeVariable { instance: None, .. } => {
                // If the type is not yet fixed, returns it.
                Rc::clone(ty)
            }
            _ => Rc::clone(ty),
        }
    }

    fn fix_function(&self, function: &mut parser::Function) {
        for binding in &mut function.params {
            match *binding.borrow_mut() {
                Binding { ref mut r#type, .. } => *r#type = self.fixed_type(r#type),
            };
        }

        self.fix_body(&mut function.body);
        function.r#type = self.fixed_type(&function.r#type);
    }

    fn fix_body(&self, body: &mut Vec<parser::Node>) {
        for node in body {
            self.fix_expr(node);
        }
    }

    fn fix_expr(&self, node: &mut parser::Node) {
        node.r#type = self.fixed_type_and_log(&node.expr.short_name(), &node.r#type);

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
            Expr::Subscript { operand, index, .. } => {
                self.fix_expr(operand);
                self.fix_expr(index);
            }
            Expr::Access { operand, .. } => self.fix_expr(operand),
            Expr::Struct { fields, .. } => {
                for parser::ValueField { value, .. } in fields {
                    self.fix_expr(value);
                }
            }
            Expr::Identifier { .. } => {}
            Expr::Invocation { arguments, .. } => {
                for argument in arguments {
                    self.fix_expr(argument);
                }
            }
            Expr::Add(lhs, rhs, ..)
            | Expr::Sub(lhs, rhs, ..)
            | Expr::Rem(lhs, rhs, ..)
            | Expr::Mul(lhs, rhs, ..)
            | Expr::Div(lhs, rhs, ..)
            | Expr::Lt(lhs, rhs, ..)
            | Expr::Gt(lhs, rhs, ..)
            | Expr::Le(lhs, rhs, ..)
            | Expr::Ge(lhs, rhs, ..)
            | Expr::Eq(lhs, rhs, ..)
            | Expr::Ne(lhs, rhs, ..) => {
                self.fix_expr(lhs);
                self.fix_expr(rhs);
            }
            Expr::Plus(operand, _) | Expr::Minus(operand, _) => self.fix_expr(operand),
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
                    *r#type = self.fixed_type(r#type);
                }
            },
            parser::Pattern::Rest {
                ref mut binding, ..
            } => match *binding.borrow_mut() {
                Binding { ref mut r#type, .. } => {
                    *r#type = self.fixed_type(r#type);
                }
            },
            parser::Pattern::Integer(_) => {}
            parser::Pattern::Array(patterns) => {
                for pattern in patterns {
                    self.fix_pattern(pattern);
                }
            }
            parser::Pattern::Struct { fields, r#type, .. } => {
                if let Some(ty) = r#type {
                    *r#type = Some(self.fixed_type(&ty));
                }

                for field in fields {
                    self.fix_pattern(&mut field.pattern);
                }
            }
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
    fn prune_type_var_unresolved() {
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
    fn prune_type_var_resolved_alias() {
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

        assert_matches!(&*pty1.borrow(), Type::TypeVariable { name, instance: Some(instance) } => {
            assert_eq!(name, "$2");
            assert_matches!(*instance.borrow(), Type::Int32);
        });
    }

    #[test]
    fn prune_type_var_resolved_alias2() {
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

        assert_matches!(&*pty1.borrow(), Type::TypeVariable { name, instance: Some(instance) } => {
            assert_eq!(name, "$2");
            assert_matches!(*instance.borrow(), Type::Int32);
        });
        assert_matches!(&*pty2.borrow(), Type::TypeVariable { name, instance: Some(instance) } => {
            assert_eq!(name, "$3");
            assert_matches!(*instance.borrow(), Type::Int32);
        });
    }

    #[test]
    fn prune_type_var_unresolved_alias2() {
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

        assert_matches!(&*pty0.borrow(), Type::TypeVariable { name, instance } => {
            assert_eq!(name, "$1");
            assert_eq!(*instance, None);
        });
        assert_matches!(&*pty1.borrow(), Type::TypeVariable { name, instance: Some(instance) } => {
            assert_eq!(name, "$2");
            assert_matches!(&*instance.borrow(), Type::TypeVariable { name, .. } => {
                assert_eq!(name, "$1");
            });
        });
        assert_matches!(&*pty2.borrow(), Type::TypeVariable { name, instance: Some(instance) } => {
            assert_eq!(name, "$3");
            assert_matches!(&*instance.borrow(), Type::TypeVariable { name, .. } => {
                assert_eq!(name, "$1");
            });
        });
    }

    #[test]
    fn prune_type_var_function() {
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

        assert_matches!(&*ty0.borrow(), Type::TypeVariable { name, instance: Some(instance) } => {
            assert_eq!(name, "$1");
            assert_matches!(*instance.borrow(), Type::String);
        });

        assert_matches!(&*ty1.borrow(), Type::TypeVariable { name, instance: Some(instance) } => {
            assert_eq!(name, "$2");
            assert_matches!(*instance.borrow(), Type::Boolean);
        });

        assert_matches!(&*fun_ty.borrow(), Type::Function {params, return_type} => {
            assert_matches!(&*params[0].borrow(), Type::TypeVariable { name, instance: Some(instance) } => {
                assert_eq!(name, "$1");
                assert_matches!(*instance.borrow(), Type::String);
            });

            assert_matches!(&*return_type.borrow(), Type::TypeVariable { name, instance: Some(instance) } => {
                assert_eq!(name, "$2");
                assert_matches!(*instance.borrow(), Type::Boolean);
            });
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
