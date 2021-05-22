//! This module contains implementations of `Visitor` that assigns meta information that can be
//! determined solely from the structure of the abstract syntax tree.
use super::{
    traverse, Block, Builtin, CaseArm, DefinitionKind, Expression, FunctionDefinition,
    FunctionParameter, IntegerLiteral, NodeKind, NodePath, Pattern, Program, StringLiteral,
    StructDefinition, VariableDeclaration, Visitor,
};
use crate::sem::{self, Type};
use crate::util::wrap;
use std::{
    cell::RefCell,
    collections::HashMap,
    fmt,
    rc::{Rc, Weak},
};

#[derive(Debug, Clone)]
pub struct Binding<'a> {
    id: String,
    kind: DefinitionKind<'a>,
}

impl<'a> Binding<'a> {
    pub fn builtin_function<S: Into<String>>(name: S, function_type: Type) -> Self {
        Self::defined_function(name, &wrap(function_type))
    }

    pub fn defined_function<S: Into<String>>(name: S, function_type: &Rc<RefCell<Type>>) -> Self {
        let name = name.into();

        Self {
            id: name.clone(),
            kind: DefinitionKind::Builtin(Rc::new(Builtin::new(name, function_type))),
        }
    }

    pub fn id(&self) -> &str {
        &self.id
    }

    pub fn kind(&self) -> &DefinitionKind<'a> {
        &self.kind
    }
}

impl fmt::Display for Binding<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            DefinitionKind::Builtin(_) => write!(f, "builtin `{}`", self.id),
            DefinitionKind::StructDefinition(_) => write!(f, "struct `{}`", self.id),
            DefinitionKind::FunctionDefinition(_) => write!(f, "function `{}`", self.id),
            DefinitionKind::FunctionParameter(_) => write!(f, "function parameter `{}`", self.id),
            DefinitionKind::Pattern(_) => write!(f, "local variable `{}`", self.id),
        }
    }
}

#[derive(Debug, Default)]
pub struct Scope<'a> {
    bindings: HashMap<String, Rc<RefCell<Binding<'a>>>>,
    parent: Weak<RefCell<Scope<'a>>>,
}

impl<'a> Scope<'a> {
    pub fn prelude() -> Self {
        let mut scope = Self::new();

        // print
        scope.insert(Binding::builtin_function(
            "println_str",
            Type::Function {
                params: vec![wrap(Type::String)],
                return_type: wrap(Type::Int32),
            },
        ));
        scope.insert(Binding::builtin_function(
            "println_i32",
            Type::Function {
                params: vec![wrap(Type::Int32)],
                return_type: wrap(Type::Int32),
            },
        ));
        scope.insert(Binding::builtin_function(
            "debug_i32",
            Type::Function {
                params: vec![wrap(Type::String), wrap(Type::Int32)],
                return_type: wrap(Type::Int32),
            },
        ));

        scope
    }

    pub fn new() -> Self {
        Self::default()
    }

    pub fn parent(&self) -> &Weak<RefCell<Scope<'a>>> {
        &self.parent
    }

    fn insert(&mut self, binding: Binding<'a>) {
        self.bindings.insert(binding.id.to_string(), wrap(binding));
    }

    pub fn register_declaration(&mut self, declaration: &NodeKind<'a>) {
        if let Some(fun) = declaration.function_definition() {
            if let Some(name) = fun.name() {
                self.insert(Binding {
                    id: name.to_string(),
                    kind: DefinitionKind::FunctionDefinition(&fun),
                });
            }
        } else if let Some(param) = declaration.function_parameter() {
            self.insert(Binding {
                id: param.name().to_string(),
                kind: DefinitionKind::FunctionParameter(&param),
            });
        } else if let Some(def) = declaration.struct_definition() {
            if let Some(name) = def.name() {
                self.insert(Binding {
                    id: name.to_string(),
                    kind: DefinitionKind::StructDefinition(&def),
                });
            }
        } else if let Some(pattern) = declaration.pattern() {
            self.register_pattern(pattern);
        }
    }

    pub fn register_pattern(&mut self, pattern: &'a Pattern<'a>) {
        match pattern.kind() {
            super::PatternKind::IntegerPattern(_) => {}
            super::PatternKind::StringPattern(_) => {}
            super::PatternKind::VariablePattern(id) => {
                self.insert(Binding {
                    id: id.to_string(),
                    kind: DefinitionKind::Pattern(pattern),
                });
            }
            super::PatternKind::ArrayPattern(pat) => {
                for pat in pat.elements() {
                    self.register_pattern(pat);
                }
            }
            super::PatternKind::RestPattern(pat) => {
                if let Some(id) = pat.id() {
                    self.insert(Binding {
                        id: id.to_string(),
                        kind: DefinitionKind::Pattern(pattern),
                    });
                }
            }
            super::PatternKind::StructPattern(pat) => {
                for field in pat.fields() {
                    if let Some(value) = field.value() {
                        self.register_pattern(value);
                    } else {
                        // omitted
                        let pattern = field.omitted_value().unwrap();

                        self.insert(Binding {
                            id: field.name().to_string(),
                            kind: DefinitionKind::Pattern(pattern),
                        });
                    }
                }
            }
        }
    }

    pub fn get_binding(&self, name: &str) -> Option<Rc<RefCell<Binding<'a>>>> {
        if let Some(binding) = self.bindings.get(name) {
            return Some(Rc::clone(binding));
        }

        if let Some(parent) = self.parent.upgrade() {
            return parent.borrow().get_binding(name);
        }

        None
    }
}

/// A Visitor collects only top-level declarations in order to resolve forward references.
#[derive(Debug, Default)]
struct TopLevelDeclarationBinder<'a> {
    declarations: Option<Rc<RefCell<Scope<'a>>>>,
}

impl<'a> TopLevelDeclarationBinder<'a> {
    pub fn new() -> Self {
        Self::default()
    }

    fn register_declaration(&mut self, node: &NodeKind<'a>) {
        if let Some(declarations) = self.declarations {
            declarations.borrow_mut().register_declaration(node);
        }
    }
}

impl<'a> Visitor<'a> for TopLevelDeclarationBinder<'a> {
    fn enter_program(&mut self, _path: &mut NodePath<'a>, program: &'a Program<'a>) {
        self.declarations = Some(Rc::clone(program.declarations_scope()));
    }

    fn enter_struct_definition(
        &mut self,
        path: &mut NodePath<'a>,
        _definition: &'a StructDefinition<'a>,
    ) {
        self.register_declaration(path.node());
    }

    fn enter_function_definition(
        &mut self,
        path: &mut NodePath<'a>,
        _definition: &'a FunctionDefinition<'a>,
    ) {
        self.register_declaration(path.node());
    }
}

/// Constructs scope chain
#[derive(Debug, Default)]
struct ScopeChainBinder<'a> {
    scope: Weak<RefCell<Scope<'a>>>,
}

impl<'a> ScopeChainBinder<'a> {
    pub fn new() -> Self {
        Self::default()
    }

    fn _enter_scope(&mut self, _path: &mut NodePath<'a>, scope: &Rc<RefCell<Scope<'a>>>) {
        scope.borrow_mut().parent = Weak::clone(&self.scope);
        self.scope = Rc::downgrade(scope);
    }

    fn _exit_scope(&mut self, _path: &mut NodePath<'a>, _scope: &Rc<RefCell<Scope<'a>>>) {
        if let Some(scope) = self.scope.upgrade() {
            self.scope = Weak::clone(&scope.borrow().parent);
        }
    }
}

impl<'a> Visitor<'a> for ScopeChainBinder<'a> {
    fn enter_program(&mut self, _path: &mut NodePath<'a>, program: &'a Program<'a>) {
        program.main_scope().borrow_mut().parent = Rc::downgrade(program.declarations_scope());
        self.scope = Rc::downgrade(program.main_scope());
    }

    fn enter_block(&mut self, path: &mut NodePath<'a>, block: &'a Block<'a>) {
        self._enter_scope(path, block.scope());
    }

    fn exit_block(&mut self, path: &mut NodePath<'a>, block: &'a Block<'a>) {
        self._exit_scope(path, block.scope());
    }

    fn enter_case_arm(&mut self, path: &mut NodePath<'a>, arm: &'a CaseArm<'a>) {
        self._enter_scope(path, arm.scope());
    }

    fn exit_case_arm(&mut self, path: &mut NodePath<'a>, arm: &'a CaseArm<'a>) {
        self._exit_scope(path, &arm.scope());
    }
}

/// Register variables
#[derive(Debug, Default)]
struct VariableBinder {}

impl VariableBinder {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<'a> Visitor<'a> for VariableBinder {
    fn enter_function_parameter(
        &mut self,
        path: &mut NodePath<'a>,
        _param: &'a FunctionParameter<'a>,
    ) {
        let node = path.node();

        let parent_path = path.expect_parent();
        let parent_path = parent_path.borrow();
        let fun = parent_path.node().function_definition().unwrap();

        let mut scope = fun.body().scope().borrow_mut();
        scope.register_declaration(node);
    }

    fn enter_variable_declaration(
        &mut self,
        path: &mut NodePath<'a>,
        declaration: &'a VariableDeclaration<'a>,
    ) {
        if let Some(pattern) = declaration.pattern() {
            let scope = path.scope();

            scope
                .borrow_mut()
                .register_declaration(&NodeKind::Pattern(pattern));
        }
    }

    fn enter_case_arm(&mut self, _path: &mut NodePath<'a>, arm: &'a CaseArm<'a>) {
        if let Some(pattern) = arm.pattern() {
            let mut scope = arm.scope().borrow_mut();
            scope.register_declaration(&NodeKind::Pattern(pattern));
        }
    }
}

/// Assign types for primitives and declarations
#[derive(Debug, Default)]
struct TypeBinder {}

impl TypeBinder {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<'a> Visitor<'a> for TypeBinder {
    fn enter_integer_literal(
        &mut self,
        _path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        _literal: &'a IntegerLiteral,
    ) {
        let ty = expr.r#type();
        ty.replace(sem::Type::Int32);
    }

    fn enter_string_literal(
        &mut self,
        _path: &mut NodePath<'a>,
        expr: &'a Expression<'a>,
        _literal: &'a StringLiteral<'a>,
    ) {
        let ty = expr.r#type();
        ty.replace(sem::Type::String);
    }
}

pub fn bind<'a>(node: &'a Program<'a>) {
    let mut binder = TopLevelDeclarationBinder::new();
    traverse(&mut binder, node);

    let mut binder = ScopeChainBinder::new();
    traverse(&mut binder, node);

    let mut binder = VariableBinder::new();
    traverse(&mut binder, node);

    let mut binder = TypeBinder::new();
    traverse(&mut binder, node);
}

#[cfg(test)]
mod tests {
    use crate::syntax::{Ast, Parser};

    #[test]
    fn top_level_declarations() {
        let tree = Ast::new();
        let program = Parser::parse_string(&tree, "fun foo()\nend");

        let scope = program.declarations_scope().borrow();
        let binding = scope.get_binding("foo");

        assert!(binding.is_some());

        let binding = binding.unwrap();
        assert_eq!(binding.borrow().id(), "foo");
    }
}
