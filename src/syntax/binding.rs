//! This module contains implementations of `Visitor` that assigns meta information that can be
//! determined solely from the structure of the abstract syntax tree.
use super::{
    traverse, ArrayExpression, BinaryExpression, Block, CallExpression, CaseArm, CaseExpression,
    FunctionDefinition, FunctionParameter, GroupedExpression, IfExpression, MemberExpression,
    NodeKind, NodePath, PatternKind, Program, StructDefinition, StructLiteral, SubscriptExpression,
    UnaryExpression, ValueField, VariableDeclaration, VariableExpression, VariablePattern, Visitor,
};
use crate::arena::{BumpaloArena, BumpaloBox};
use crate::semantic::{self, Binding, TypeKind, TypeVariable};
use crate::syntax;
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
}

/// A visitor assigns an initial type (type variable or primitive type) to a node.
#[derive(Debug)]
struct InitialTypeBinder<'a> {
    arena: &'a BumpaloArena,
    seq: i32,
}

impl<'a> InitialTypeBinder<'a> {
    pub fn new(arena: &'a BumpaloArena) -> Self {
        Self { arena, seq: 0 }
    }

    pub fn new_type_var(&mut self) -> &'a TypeVariable<'a> {
        let var = TypeVariable::new(self.seq);

        self.seq += 1;
        self.arena.alloc(var)
    }

    fn build_struct_type(
        &mut self,
        definition: &'a StructDefinition<'a>,
    ) -> Option<&'a semantic::StructType<'a>> {
        let name = definition.name()?;
        let mut field_types = vec![];

        for f in definition.fields() {
            let name = f.name()?.as_str();
            let ty = f.type_annotation()?.r#type();

            let field = &*self
                .arena
                .alloc(semantic::StructField::new(self.arena, name, ty));

            field_types.push(field);
        }

        let ty = semantic::StructType::new(self.arena, name.as_str(), &field_types);
        Some(&*self.arena.alloc(ty))
    }

    fn build_function_type(
        &mut self,
        definition: &'a FunctionDefinition<'a>,
    ) -> Option<&'a semantic::FunctionType<'a>> {
        let name = definition.name()?;
        let params: Vec<_> = definition
            .parameters()
            .map(|p| {
                &*self.arena.alloc(semantic::FunctionParameter::new(
                    self.arena,
                    p.name().as_str(),
                    p.r#type(),
                ))
            })
            .collect();

        let ty = semantic::FunctionType::new(
            self.arena,
            name.as_str(),
            &params,
            TypeKind::TypeVariable(self.new_type_var()),
        );

        Some(&*self.arena.alloc(ty))
    }
}

impl<'a> Visitor<'a> for InitialTypeBinder<'a> {
    fn exit_struct_definition(
        &mut self,
        _path: &'a NodePath<'a>,
        definition: &'a StructDefinition<'a>,
    ) {
        if let Some(ty) = self.build_struct_type(definition) {
            definition.assign_type(TypeKind::StructType(ty))
        }
    }

    fn exit_function_definition(
        &mut self,
        _path: &'a NodePath<'a>,
        definition: &'a FunctionDefinition<'a>,
    ) {
        if let Some(ty) = self.build_function_type(definition) {
            definition.assign_type(TypeKind::FunctionType(ty))
        }
    }

    fn exit_function_parameter(
        &mut self,
        _path: &'a NodePath<'a>,
        _fun: &'a FunctionDefinition<'a>,
        param: &'a FunctionParameter<'a>,
    ) {
        param.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_struct_literal(&mut self, _path: &'a NodePath<'a>, expr: &'a StructLiteral<'a>) {
        expr.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_value_field(
        &mut self,
        _path: &'a NodePath<'a>,
        _struct_literal: &'a StructLiteral<'a>,
        field: &'a ValueField<'a>,
    ) {
        field.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_binary_expression(&mut self, _path: &'a NodePath<'a>, expr: &'a BinaryExpression<'a>) {
        expr.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_unary_expression(&mut self, _path: &'a NodePath<'a>, expr: &'a UnaryExpression<'a>) {
        expr.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_array_expression(&mut self, _path: &'a NodePath<'a>, expr: &'a ArrayExpression<'a>) {
        expr.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_call_expression(&mut self, _path: &'a NodePath<'a>, expr: &'a CallExpression<'a>) {
        expr.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_subscript_expression(
        &mut self,
        _path: &'a NodePath<'a>,
        expr: &'a SubscriptExpression<'a>,
    ) {
        expr.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_member_expression(&mut self, _path: &'a NodePath<'a>, expr: &'a MemberExpression<'a>) {
        expr.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_case_expression(&mut self, _path: &'a NodePath<'a>, expr: &'a CaseExpression<'a>) {
        expr.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_if_expression(&mut self, _path: &'a NodePath<'a>, expr: &'a IfExpression<'a>) {
        expr.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_variable_expression(
        &mut self,
        _path: &'a NodePath<'a>,
        expr: &'a VariableExpression<'a>,
    ) {
        expr.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_grouped_expression(
        &mut self,
        _path: &'a NodePath<'a>,
        expr: &'a GroupedExpression<'a>,
    ) {
        expr.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_variable_pattern(&mut self, _path: &'a NodePath<'a>, pattern: &'a VariablePattern<'a>) {
        pattern.assign_type(TypeKind::TypeVariable(self.new_type_var()))
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

#[derive(Debug)]
struct TypeInferencer<'a> {
    arena: &'a BumpaloArena,
}

impl<'a> TypeInferencer<'a> {
    pub fn new(arena: &'a BumpaloArena) -> Self {
        Self { arena }
    }
}

impl<'a> Visitor<'a> for TypeInferencer<'a> {
    fn exit_struct_literal(&mut self, path: &'a NodePath<'a>, literal: &'a StructLiteral<'a>) {
        let binding = match path.scope().get_binding(literal.name().as_str()) {
            Some(binding) => binding,
            None => return,
        };

        let struct_def = match binding.struct_definition() {
            Some(struct_def) => struct_def,
            None => return,
        };

        literal
            .r#type()
            .unify(self.arena, struct_def.r#type())
            .unwrap_or_else(|err| panic!("Type error: {}", err));
    }

    fn exit_variable_declaration(
        &mut self,
        _path: &'a NodePath<'a>,
        declaration: &'a VariableDeclaration<'a>,
    ) {
        let pattern = match declaration.pattern() {
            Some(pattern) => pattern,
            None => return,
        };

        let init = match declaration.init() {
            Some(init) => init,
            None => return,
        };

        if let PatternKind::VariablePattern(var_pattern) = pattern.kind() {
            var_pattern
                .r#type()
                .unify(self.arena, init.r#type())
                .unwrap_or_else(|err| panic!("Type error: {}", err));
        } else {
            todo!("warn: except for variable pattern, we can't infer type.");
        }
    }

    fn exit_variable_expression(
        &mut self,
        path: &'a NodePath<'a>,
        expr: &'a VariableExpression<'a>,
    ) {
        if let Some(binding) = path.scope().get_binding(expr.name()) {
            expr.r#type()
                .unify(self.arena, binding.r#type())
                .unwrap_or_else(|err| panic!("Type error: {}", err));
        }
    }

    fn exit_grouped_expression(
        &mut self,
        _path: &'a NodePath<'a>,
        grouped_expr: &'a GroupedExpression<'a>,
    ) {
        if let Some(expr) = grouped_expr.expression() {
            grouped_expr
                .r#type()
                .unify(self.arena, expr.r#type())
                .unwrap_or_else(|err| panic!("Type error: {}", err));
        }
    }
}

pub fn bind<'a>(arena: &'a BumpaloArena, node: &'a Program<'a>) {
    let mut binder = InitialTypeBinder::new(arena);
    traverse(arena, &mut binder, node);

    let mut binder = TopLevelDeclarationBinder::new(arena);
    traverse(arena, &mut binder, node);

    let mut binder = ScopeChainBinder::new(arena);
    traverse(arena, &mut binder, node);

    let mut binder = VariableBinder::new(arena);
    traverse(arena, &mut binder, node);

    let mut binder = TypeInferencer::new(arena);
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
