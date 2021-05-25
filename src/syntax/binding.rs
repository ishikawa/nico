//! This module contains implementations of `Visitor` that assigns meta information that can be
//! determined solely from the structure of the abstract syntax tree.
use super::{
    traverse, Block, CaseArm, FunctionDefinition, FunctionParameter, NodeKind, NodePath, Pattern,
    Program, StructDefinition, VariableDeclaration, Visitor,
};
use crate::arena::{BumpaloArena, BumpaloBox, BumpaloString};
use crate::{sem::Type, semantic::DefinitionKind};
use crate::{semantic::Builtin, util::wrap};
use std::{
    cell::{Cell, RefCell},
    collections::HashMap,
    fmt,
    rc::Rc,
};

#[derive(Debug, Clone)]
pub struct Binding<'a> {
    id: BumpaloString<'a>,
    kind: &'a DefinitionKind<'a>,
}

impl<'a> Binding<'a> {
    pub fn new<S: AsRef<str>>(arena: &'a BumpaloArena, name: S, kind: DefinitionKind<'a>) -> Self {
        Self {
            id: BumpaloString::from_str_in(name.as_ref(), arena),
            kind: arena.alloc(kind),
        }
    }

    pub fn builtin_function<S: AsRef<str>>(
        arena: &'a BumpaloArena,
        name: S,
        function_type: Type,
    ) -> Self {
        Self::defined_function(arena, name, &wrap(function_type))
    }

    pub fn defined_function<S: AsRef<str>>(
        arena: &'a BumpaloArena,
        name: S,
        function_type: &Rc<RefCell<Type>>,
    ) -> Self {
        Self::new(
            arena,
            name.as_ref(),
            DefinitionKind::Builtin(Rc::new(Builtin::new(
                name.as_ref().to_string(),
                function_type,
            ))),
        )
    }

    pub fn id(&self) -> &str {
        self.id.as_str()
    }

    pub fn kind(&self) -> &'a DefinitionKind<'a> {
        self.kind
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

#[derive(Debug)]
pub struct Scope<'a> {
    bindings: BumpaloBox<'a, RefCell<HashMap<&'a str, &'a Binding<'a>>>>,
    parent: BumpaloBox<'a, Cell<Option<&'a Scope<'a>>>>,
}

impl<'a> Scope<'a> {
    pub fn prelude(arena: &'a BumpaloArena) -> Self {
        let scope = Self::new(arena);

        // print
        scope.insert(
            arena,
            Binding::builtin_function(
                arena,
                "println_str",
                Type::Function {
                    params: vec![wrap(Type::String)],
                    return_type: wrap(Type::Int32),
                },
            ),
        );
        scope.insert(
            arena,
            Binding::builtin_function(
                arena,
                "println_i32",
                Type::Function {
                    params: vec![wrap(Type::Int32)],
                    return_type: wrap(Type::Int32),
                },
            ),
        );
        scope.insert(
            arena,
            Binding::builtin_function(
                arena,
                "debug_i32",
                Type::Function {
                    params: vec![wrap(Type::String), wrap(Type::Int32)],
                    return_type: wrap(Type::Int32),
                },
            ),
        );

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

    fn insert(&self, arena: &'a BumpaloArena, binding: Binding<'a>) {
        let b = arena.alloc(binding);
        self.bindings.borrow_mut().insert(b.id(), b);
    }

    pub fn register_declaration(&self, arena: &'a BumpaloArena, declaration: &NodeKind<'a>) {
        if let Some(fun) = declaration.function_definition() {
            if let Some(name) = fun.name() {
                self.insert(
                    arena,
                    Binding::new(
                        arena,
                        name.as_str(),
                        DefinitionKind::FunctionDefinition(&fun),
                    ),
                );
            }
        } else if let Some(param) = declaration.function_parameter() {
            self.insert(
                arena,
                Binding::new(
                    arena,
                    param.name().as_str(),
                    DefinitionKind::FunctionParameter(&param),
                ),
            );
        } else if let Some(def) = declaration.struct_definition() {
            if let Some(name) = def.name() {
                self.insert(
                    arena,
                    Binding::new(arena, name.as_str(), DefinitionKind::StructDefinition(&def)),
                );
            }
        } else if let Some(pattern) = declaration.pattern() {
            self.register_pattern(arena, pattern);
        }
    }

    pub fn register_pattern(&self, arena: &'a BumpaloArena, pattern: &'a Pattern<'a>) {
        match pattern.kind() {
            super::PatternKind::IntegerPattern(_) => {}
            super::PatternKind::StringPattern(_) => {}
            super::PatternKind::VariablePattern(id) => {
                self.insert(
                    arena,
                    Binding::new(arena, id.as_str(), DefinitionKind::Pattern(pattern)),
                );
            }
            super::PatternKind::ArrayPattern(pat) => {
                for pat in pat.elements() {
                    self.register_pattern(arena, pat);
                }
            }
            super::PatternKind::RestPattern(pat) => {
                if let Some(id) = pat.id() {
                    self.insert(
                        arena,
                        Binding::new(arena, id.as_str(), DefinitionKind::Pattern(pattern)),
                    );
                }
            }
            super::PatternKind::StructPattern(pat) => {
                for field in pat.fields() {
                    if let Some(value) = field.value() {
                        self.register_pattern(arena, value);
                    } else {
                        // omitted
                        let pattern = field.omitted_value().unwrap();

                        self.insert(
                            arena,
                            Binding::new(
                                arena,
                                field.name().as_str(),
                                DefinitionKind::Pattern(pattern),
                            ),
                        );
                    }
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
}

/// A Visitor collects only top-level declarations in order to resolve forward references.
#[derive(Debug)]
struct TopLevelDeclarationBinder<'a> {
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

    fn register_declaration(&mut self, node: &NodeKind<'a>) {
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

/// Constructs scope chain
#[derive(Debug)]
struct ScopeChainBinder<'a> {
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
struct VariableBinder<'a> {
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
        _param: &'a FunctionParameter<'a>,
    ) {
        let node = path.node();

        let parent_path = path.expect_parent();
        let fun = parent_path.node().function_definition().unwrap();

        fun.body().scope().register_declaration(self.arena, node);
    }

    fn enter_variable_declaration(
        &mut self,
        path: &'a NodePath<'a>,
        declaration: &'a VariableDeclaration<'a>,
    ) {
        if let Some(pattern) = declaration.pattern() {
            let scope = path.scope();

            scope.register_declaration(self.arena, &NodeKind::Pattern(pattern));
        }
    }

    fn enter_case_arm(&mut self, _path: &'a NodePath<'a>, arm: &'a CaseArm<'a>) {
        if let Some(pattern) = arm.pattern() {
            arm.scope()
                .register_declaration(self.arena, &NodeKind::Pattern(pattern));
        }
    }
}

pub fn bind<'a>(arena: &'a BumpaloArena, node: &'a Program<'a>) {
    let mut binder = TopLevelDeclarationBinder::new(arena);
    traverse(arena, &mut binder, node);

    let mut binder = ScopeChainBinder::new(arena);
    traverse(arena, &mut binder, node);

    let mut binder = VariableBinder::new(arena);
    traverse(arena, &mut binder, node);
}

#[cfg(test)]
mod tests {
    use crate::arena::BumpaloArena;
    use crate::syntax::Parser;

    #[test]
    fn top_level_declarations() {
        let arena = BumpaloArena::new();
        let program = Parser::parse_string(&arena, "fun foo()\nend");

        let scope = program.declarations_scope();
        let binding = scope.get_binding("foo");

        assert!(binding.is_some());

        let binding = binding.unwrap();
        assert_eq!(binding.id(), "foo");
    }
}
