//! This module contains implementations of `Visitor` that assigns meta information that can be
//! determined solely from the structure of the abstract syntax tree.
use super::{
    traverse, Block, CaseArm, Expression, FunctionDefinition, FunctionParameter, NodeKind,
    NodePath, Pattern, Program, StructDefinition, VariableDeclaration, Visitor, AST,
};
use crate::sem::Type;
use crate::semantic::{self, SemanticValueKind};
use crate::util::wrap;
use std::{
    cell::RefCell,
    collections::HashMap,
    fmt,
    rc::{Rc, Weak},
};

#[derive(Debug)]
pub struct Binding {
    id: String,
    value: SemanticValueKind,
}

impl Binding {
    pub fn new<S: Into<String>>(id: S, value: SemanticValueKind) -> Self {
        Self {
            id: id.into(),
            value: value,
        }
    }

    pub fn id(&self) -> &str {
        &self.id
    }

    pub fn value(&self) -> &SemanticValueKind {
        &self.value
    }
}

impl fmt::Display for Binding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            SemanticValueKind::Function(_) => {
                write!(f, "function `{}`", self.id)
            }
            SemanticValueKind::Struct(_) => {
                write!(f, "struct `{}`", self.id)
            }
            SemanticValueKind::Variable(_) => {
                write!(f, "local variable `{}`", self.id)
            }
        }
    }
}

#[derive(Debug, Default)]
pub struct Scope {
    bindings: HashMap<String, Rc<RefCell<Binding>>>,
    parent: Weak<RefCell<Scope>>,
}

impl Scope {
    pub fn prelude() -> Self {
        let mut scope = Self::new();

        // print functions
        scope.define_function(semantic::Function::define_function(
            "println_str",
            vec![("str", Type::String)],
            Type::Int32,
        ));
        scope.define_function(semantic::Function::define_function(
            "println_i32",
            vec![("i", Type::Int32)],
            Type::Int32,
        ));
        scope.define_function(semantic::Function::define_function(
            "debug_i32",
            vec![("i", Type::Int32)],
            Type::Int32,
        ));

        scope
    }

    pub fn new() -> Self {
        Self::default()
    }

    pub fn parent(&self) -> &Weak<RefCell<Scope>> {
        &self.parent
    }

    pub fn insert<S: AsRef<str>>(&mut self, id: S, value: SemanticValueKind) {
        let id = id.as_ref().to_string();

        let binding = Binding::new(id.clone(), value);
        self.bindings.insert(id, wrap(binding));
    }

    fn register_declaration(&mut self, tree: &AST, declaration: &NodeKind) {
        if let Some(fun) = declaration.function_definition() {
            if let Some(value) = fun.semantic_value() {
                self.insert_function(Rc::clone(value));
            }
        } else if let Some(param) = declaration.function_parameter() {
            if let Some(value) = param.semantic_value() {
                self.insert_variable(Rc::clone(value));
            }
        } else if let Some(def) = declaration.struct_definition() {
            if let Some(value) = def.semantic_value() {
                self.insert_struct(Rc::clone(value));
            }
        } else if let Some(pattern) = declaration.pattern() {
            self.register_pattern(tree, pattern);
        }
    }

    pub fn register_pattern(&mut self, tree: &AST, pattern: &Pattern) {
        match &pattern.kind() {
            super::PatternKind::IntegerPattern(_) => {}
            super::PatternKind::StringPattern(_) => {}
            super::PatternKind::VariablePattern(id) => {
                if let Some(value) = id.semantic_value() {
                    self.insert_variable(Rc::clone(value));
                }
            }
            super::PatternKind::ArrayPattern(pat) => {
                for pat in pat.elements(tree) {
                    self.register_pattern(tree, pat);
                }
            }
            super::PatternKind::RestPattern(pat) => {
                if pat.id(tree).is_some() {
                    if let Some(value) = pat.semantic_value() {
                        self.insert_variable(Rc::clone(value));
                    }
                }
            }
            super::PatternKind::StructPattern(pat) => {
                for field in pat.fields(tree) {
                    if let Some(value) = field.value(tree) {
                        self.register_pattern(tree, value);
                    } else {
                        // omitted
                        let pattern = field.variable().unwrap();

                        if let Some(value) = pattern.semantic_value() {
                            self.insert_variable(Rc::clone(value));
                        }
                    }
                }
            }
        }
    }

    pub fn get_binding(&self, name: &str) -> Option<Rc<RefCell<Binding>>> {
        if let Some(binding) = self.bindings.get(name) {
            return Some(Rc::clone(binding));
        }

        if let Some(parent) = self.parent.upgrade() {
            return parent.borrow().get_binding(name);
        }

        None
    }

    fn define_function(&mut self, fun: semantic::Function) {
        self.insert_function(wrap(fun));
    }

    fn insert_function(&mut self, fun: Rc<RefCell<semantic::Function>>) {
        let name = fun.borrow().name().to_string();
        self.insert(name, SemanticValueKind::Function(fun));
    }

    fn insert_struct(&mut self, value: Rc<RefCell<semantic::Struct>>) {
        let name = value.borrow().name().to_string();
        self.insert(name, SemanticValueKind::Struct(value));
    }

    fn insert_variable(&mut self, value: Rc<RefCell<semantic::Variable>>) {
        let name = value.borrow().name().to_string();
        self.insert(name, SemanticValueKind::Variable(value));
    }
}

/// A Visitor collects only top-level declarations in order to resolve forward references.
#[derive(Debug, Default)]
struct TopLevelDeclarationBinder {
    declarations: Option<Rc<RefCell<Scope>>>,
}

impl TopLevelDeclarationBinder {
    pub fn new() -> Self {
        Self::default()
    }

    fn register_declaration(&mut self, tree: &AST, path: &NodePath) {
        let declarations = self.declarations.as_ref().unwrap();

        declarations
            .borrow_mut()
            .register_declaration(tree, path.node(tree));
    }
}

impl<'a> Visitor<'a> for TopLevelDeclarationBinder {
    fn enter_program(&mut self, _tree: &'a AST, _path: &mut NodePath, program: &Program) {
        self.declarations = Some(Rc::clone(program.declarations_scope()));
    }

    fn enter_struct_definition(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        _definition: &StructDefinition,
    ) {
        self.register_declaration(tree, path);
    }

    fn enter_function_definition(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        _definition: &FunctionDefinition,
    ) {
        self.register_declaration(tree, path);
    }
}

/// Constructs scope chain
#[derive(Debug, Default)]
struct ScopeChainBinder {
    scope: Weak<RefCell<Scope>>,
}

impl ScopeChainBinder {
    pub fn new() -> Self {
        Self::default()
    }

    fn _enter_scope(&mut self, _path: &mut NodePath, scope: &Rc<RefCell<Scope>>) {
        scope.borrow_mut().parent = Weak::clone(&self.scope);
        self.scope = Rc::downgrade(scope);
    }

    fn _exit_scope(&mut self, _path: &mut NodePath, _scope: &Rc<RefCell<Scope>>) {
        if let Some(scope) = self.scope.upgrade() {
            self.scope = Weak::clone(&scope.borrow().parent);
        }
    }
}

impl<'a> Visitor<'a> for ScopeChainBinder {
    fn enter_program(&mut self, _tree: &'a AST, _path: &mut NodePath, program: &Program) {
        program.main_scope().borrow_mut().parent = Rc::downgrade(program.declarations_scope());
        self.scope = Rc::downgrade(program.main_scope());
    }

    fn enter_block(&mut self, _tree: &'a AST, path: &mut NodePath, block: &Block) {
        self._enter_scope(path, block.scope());
    }

    fn exit_block(&mut self, _tree: &'a AST, path: &mut NodePath, block: &Block) {
        self._exit_scope(path, block.scope());
    }

    fn enter_case_arm(&mut self, _tree: &'a AST, path: &mut NodePath, arm: &CaseArm) {
        self._enter_scope(path, arm.scope());
    }

    fn exit_case_arm(&mut self, _tree: &'a AST, path: &mut NodePath, arm: &CaseArm) {
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
        tree: &'a AST,
        path: &mut NodePath,
        _param: &FunctionParameter,
    ) {
        let parent_path = path.expect_parent();
        let parent_path = parent_path.borrow();
        let fun = parent_path.node(tree).function_definition().unwrap();

        let mut scope = fun.body(tree).scope().borrow_mut();
        scope.register_declaration(tree, path.node(tree));
    }

    fn enter_variable_declaration(
        &mut self,
        tree: &'a AST,
        path: &mut NodePath,
        declaration: &VariableDeclaration,
    ) {
        if let Some(pattern) = declaration.pattern(tree) {
            let scope = path.scope();
            let mut scope = scope.borrow_mut();

            scope.register_pattern(tree, pattern);
        }
    }

    fn enter_case_arm(&mut self, tree: &'a AST, _path: &mut NodePath, arm: &CaseArm) {
        if let Some(pattern) = arm.pattern(tree) {
            let mut scope = arm.scope().borrow_mut();
            scope.register_pattern(tree, pattern);
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
        _tree: &'a AST,
        _path: &mut NodePath,
        expr: &Expression,
        _literal: i32,
    ) {
        let ty = expr.r#type();
        ty.replace(Type::Int32);
    }

    fn enter_string_literal(
        &mut self,
        _tree: &'a AST,
        _path: &mut NodePath,
        expr: &Expression,
        _literal: Option<&str>,
    ) {
        let ty = expr.r#type();
        ty.replace(Type::String);
    }
}

pub fn bind(tree: &mut AST) {
    let mut binder = TopLevelDeclarationBinder::new();
    traverse(&mut binder, tree);

    let mut binder = ScopeChainBinder::new();
    traverse(&mut binder, tree);

    let mut binder = VariableBinder::new();
    traverse(&mut binder, tree);

    let mut binder = TypeBinder::new();
    traverse(&mut binder, tree);
}

#[cfg(test)]
mod tests {
    use crate::syntax::Parser;

    #[test]
    fn top_level_declarations() {
        let tree = Parser::parse_string("fun foo()\nend");

        let program = tree.program();
        let scope = program.declarations_scope().borrow();
        let binding = scope.get_binding("foo");

        assert!(binding.is_some());

        let binding = binding.unwrap();
        assert_eq!(binding.borrow().id(), "foo");
    }
}
