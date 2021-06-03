use crate::arena::BumpaloArena;
use crate::semantic::{self, TypeKind, TypeVariable};
use crate::syntax::{
    ArrayExpression, BinaryExpression, CallExpression, CaseExpression, FunctionDefinition,
    FunctionParameter, GroupedExpression, IfExpression, MemberExpression, NodePath, PatternKind,
    StructDefinition, StructLiteral, SubscriptExpression, UnaryExpression, ValueField,
    VariableDeclaration, VariableExpression, VariablePattern, Visitor,
};

/// A visitor assigns an initial type (type variable or primitive type) to a node.
#[derive(Debug)]
pub(super) struct InitialTypeBinder<'a> {
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

#[derive(Debug)]
pub(super) struct TypeInferencer<'a> {
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
