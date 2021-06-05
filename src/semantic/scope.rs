use crate::arena::{BumpaloArena, BumpaloBox};
use crate::semantic::{Binding, TypeKind};
use crate::syntax::{
    self, Block, CaseArm, FunctionDefinition, NodeKind, NodePath, PatternKind, Program,
    StructDefinition, VariableDeclaration, Visitor,
};
use std::cell::Ref;
use std::{
    cell::{Cell, RefCell},
    collections::HashMap,
};

#[derive(Debug)]
pub struct Scope<'a> {
    bindings: BumpaloBox<'a, RefCell<HashMap<&'a str, &'a Binding<'a>>>>,
    parent: BumpaloBox<'a, Cell<Option<&'a Scope<'a>>>>,
}

impl<'a> Scope<'a> {
    pub fn prelude(arena: &'a BumpaloArena) -> Self {
        let scope = Self::new(arena);

        // print
        scope.insert(Binding::builtin_function(
            arena,
            "println_str",
            &[("arg0", TypeKind::String)],
            TypeKind::Int32,
        ));
        scope.insert(Binding::builtin_function(
            arena,
            "println_i32",
            &[("arg0", TypeKind::Int32)],
            TypeKind::Int32,
        ));
        scope.insert(Binding::builtin_function(
            arena,
            "debug_i32",
            &[("message", TypeKind::String), ("value", TypeKind::Int32)],
            TypeKind::Int32,
        ));

        scope
    }

    pub fn new(arena: &'a BumpaloArena) -> Self {
        Self {
            bindings: BumpaloBox::new_in(RefCell::new(HashMap::new()), arena),
            parent: BumpaloBox::new_in(Cell::new(None), arena),
        }
    }

    pub fn parent(&self) -> Option<&'a Scope<'a>> {
        self.parent.get()
    }

    fn insert(&self, binding: &'a Binding<'a>) {
        self.bindings.borrow_mut().insert(binding.id(), binding);
    }

    pub fn register_declaration(&self, arena: &'a BumpaloArena, declaration: NodeKind<'a>) {
        if let Some(fun) = declaration.function_definition() {
            if let Some(binding) = Binding::alloc_function_in(arena, fun) {
                self.insert(binding);
                fun.assign_binding(binding);
            }
        } else if let Some(param) = declaration.function_parameter() {
            let binding = Binding::alloc_function_parameter_in(arena, param);

            self.insert(binding);
            param.assign_binding(binding);
        } else if let Some(struct_node) = declaration.struct_definition() {
            if let Some(binding) = Binding::alloc_struct_in(arena, struct_node) {
                self.insert(binding);
                struct_node.assign_binding(binding);
            }
        } else if let Some(pattern) = declaration.pattern() {
            self.register_pattern(arena, pattern.kind());
        }
    }

    pub fn register_pattern(&self, arena: &'a BumpaloArena, pattern: &PatternKind<'a>) {
        match pattern {
            PatternKind::IntegerPattern(_) => {}
            PatternKind::StringPattern(_) => {}
            PatternKind::VariablePattern(variable_pattern) => {
                let binding = Binding::alloc_variable_pattern_in(arena, &variable_pattern);

                self.insert(binding);
                variable_pattern.assign_binding(binding);
            }
            PatternKind::ArrayPattern(pat) => {
                for pat in pat.elements() {
                    self.register_pattern(arena, pat.kind());
                }
            }
            PatternKind::RestPattern(pat) => {
                if let Some(variable_pattern) = pat.variable_pattern() {
                    self.register_pattern(arena, &PatternKind::VariablePattern(variable_pattern));
                }
            }
            PatternKind::StructPattern(pat) => {
                for field in pat.fields() {
                    self.register_pattern(arena, &PatternKind::ValueFieldPattern(field));
                }
            }
            PatternKind::ValueFieldPattern(field) => {
                if let Some(value) = field.value() {
                    self.register_pattern(arena, value.kind());
                } else {
                    // omitted
                    let pattern = field.omitted_value().unwrap();
                    self.register_pattern(arena, pattern.kind());
                }
            }
        }
    }

    pub fn get_binding(&self, name: &str) -> Option<&'a Binding<'a>> {
        if let Some(binding) = self.bindings.borrow().get(name) {
            return Some(binding);
        }

        if let Some(parent) = self.parent.get() {
            return parent.get_binding(name);
        }

        None
    }

    pub fn borrow_bindings(&self) -> Ref<'_, HashMap<&'a str, &'a Binding<'a>>> {
        self.bindings.borrow()
    }
}

/// A Visitor collects only top-level declarations in order to resolve forward references.
#[derive(Debug)]
pub(super) struct TopLevelDeclarationBinder<'a> {
    arena: &'a BumpaloArena,
    declarations: Option<&'a Scope<'a>>,
}

impl<'a> TopLevelDeclarationBinder<'a> {
    pub fn new(arena: &'a BumpaloArena) -> Self {
        Self {
            arena,
            declarations: None,
        }
    }

    fn register_declaration(&mut self, node: NodeKind<'a>) {
        if let Some(ref declarations) = self.declarations {
            declarations.register_declaration(self.arena, node);
        }
    }
}

impl<'a> Visitor<'a> for TopLevelDeclarationBinder<'a> {
    fn enter_program(&mut self, _path: &'a NodePath<'a>, program: &'a Program<'a>) {
        self.declarations = Some(program.declarations_scope());
    }

    fn enter_struct_definition(
        &mut self,
        path: &'a NodePath<'a>,
        _definition: &'a StructDefinition<'a>,
    ) {
        self.register_declaration(path.node());
    }

    fn enter_function_definition(
        &mut self,
        path: &'a NodePath<'a>,
        _definition: &'a FunctionDefinition<'a>,
    ) {
        self.register_declaration(path.node());
    }
}

/// Constructs scope chain visitor
#[derive(Debug)]
pub(super) struct ScopeChainBinder<'a> {
    arena: &'a BumpaloArena,
    scope: Option<&'a Scope<'a>>,
}

impl<'a> ScopeChainBinder<'a> {
    pub fn new(arena: &'a BumpaloArena) -> Self {
        Self { arena, scope: None }
    }

    fn _enter_scope(&mut self, _path: &'a NodePath<'a>, scope: &'a Scope<'a>) {
        scope.parent.replace(self.scope);
        self.scope = Some(scope);
    }

    fn _exit_scope(&mut self, _path: &'a NodePath<'a>, _scope: &'a Scope<'a>) {
        if let Some(scope) = self.scope {
            self.scope = scope.parent()
        }
    }
}

impl<'a> Visitor<'a> for ScopeChainBinder<'a> {
    fn enter_program(&mut self, _path: &'a NodePath<'a>, program: &'a Program<'a>) {
        program
            .main_scope()
            .parent
            .replace(Some(program.declarations_scope()));
        self.scope = Some(program.main_scope());
    }

    fn enter_block(&mut self, path: &'a NodePath<'a>, block: &'a Block<'a>) {
        self._enter_scope(path, block.scope());
    }

    fn exit_block(&mut self, path: &'a NodePath<'a>, block: &'a Block<'a>) {
        self._exit_scope(path, block.scope());
    }

    fn enter_case_arm(&mut self, path: &'a NodePath<'a>, arm: &'a CaseArm<'a>) {
        self._enter_scope(path, arm.scope());
    }

    fn exit_case_arm(&mut self, path: &'a NodePath<'a>, arm: &'a CaseArm<'a>) {
        self._exit_scope(path, &arm.scope());
    }
}

/// Register variables
#[derive(Debug)]
pub(super) struct VariableBinder<'a> {
    arena: &'a BumpaloArena,
}

impl<'a> VariableBinder<'a> {
    pub fn new(arena: &'a BumpaloArena) -> Self {
        Self { arena }
    }
}

impl<'a> Visitor<'a> for VariableBinder<'a> {
    fn enter_function_parameter(
        &mut self,
        path: &'a NodePath<'a>,
        fun: &'a FunctionDefinition<'a>,
        _param: &'a syntax::FunctionParameter<'a>,
    ) {
        let node = path.node();
        fun.body().scope().register_declaration(self.arena, node);
    }

    fn enter_variable_declaration(
        &mut self,
        path: &'a NodePath<'a>,
        declaration: &'a VariableDeclaration<'a>,
    ) {
        if let Some(pattern) = declaration.pattern() {
            let scope = path.scope();

            scope.register_declaration(self.arena, NodeKind::Pattern(pattern));
        }
    }

    fn enter_case_arm(&mut self, _path: &'a NodePath<'a>, arm: &'a CaseArm<'a>) {
        if let Some(pattern) = arm.pattern() {
            arm.scope()
                .register_declaration(self.arena, NodeKind::Pattern(pattern));
        }
    }
}
