use super::description;
use crate::arena::BumpaloArena;
use crate::syntax::{
    self, EffectiveRange, FunctionDefinition, FunctionParameter, MemberExpression, Node, NodePath,
    Position, Program, StructDefinition, StructLiteral, TypeAnnotation, TypeField, TypedNode,
    ValueField, VariableExpression, VariablePattern,
};
use crate::unwrap_or_return;

#[derive(Debug)]
pub struct Hover<'a> {
    arena: &'a BumpaloArena,
    position: Position,
    result: Option<(String, EffectiveRange)>,
}

impl<'a> Hover<'a> {
    pub fn new(arena: &'a BumpaloArena, position: Position) -> Self {
        Self {
            arena,
            position,
            result: None,
        }
    }

    pub fn describe(&mut self, program: &'a Program<'a>) -> Option<(&str, EffectiveRange)> {
        syntax::traverse(self.arena, self, program);
        self.result.as_ref().map(|(s, r)| (s.as_str(), *r))
    }

    fn can_hover(&self, range: EffectiveRange, path: &'a NodePath<'a>) -> Option<&'a NodePath<'a>> {
        if range.contains(self.position) {
            Some(path)
        } else {
            None
        }
    }
}

impl<'a> syntax::Visitor<'a> for Hover<'a> {
    fn enter_function_definition(
        &mut self,
        path: &'a NodePath<'a>,
        definition: &'a FunctionDefinition<'a>,
    ) {
        let range = unwrap_or_return!(definition.name()).range();
        unwrap_or_return!(self.can_hover(range, path)).stop();

        let function_type = unwrap_or_return!(definition.function_type());
        self.result
            .replace((description::code_fence(function_type.to_string()), range));
    }

    fn enter_function_parameter(
        &mut self,
        path: &'a NodePath<'a>,
        _function: &'a FunctionDefinition<'a>,
        param: &'a FunctionParameter<'a>,
    ) {
        let range = param.name().range();
        unwrap_or_return!(self.can_hover(range, path)).stop();

        self.result.replace((
            description::code_fence(description::format_function_parameter(param)),
            range,
        ));
    }

    fn enter_struct_definition(
        &mut self,
        path: &'a NodePath<'a>,
        definition: &'a StructDefinition<'a>,
    ) {
        let range = unwrap_or_return!(definition.name()).range();
        unwrap_or_return!(self.can_hover(range, path)).stop();

        let struct_type = unwrap_or_return!(definition.struct_type());
        self.result.replace((
            description::code_fence(description::format_struct_type_phrase(struct_type)),
            range,
        ));
    }

    fn enter_struct_literal(&mut self, path: &'a NodePath<'a>, expr: &'a StructLiteral<'a>) {
        let range = expr.name().range();
        unwrap_or_return!(self.can_hover(range, path)).stop();

        let struct_type = unwrap_or_return!(expr.r#type().struct_type());
        self.result.replace((
            description::code_fence(description::format_struct_type_phrase(struct_type)),
            range,
        ));
    }

    fn enter_type_field(
        &mut self,
        path: &'a NodePath<'a>,
        struct_def: &'a StructDefinition<'a>,
        field: &'a TypeField<'a>,
    ) {
        let field_name = unwrap_or_return!(field.name());
        let range = field_name.range();
        unwrap_or_return!(self.can_hover(range, path)).stop();

        let struct_type = unwrap_or_return!(struct_def.struct_type());

        self.result.replace((
            description::format_struct_field(struct_type, field_name.as_str()),
            range,
        ));
    }

    fn enter_type_annotation(
        &mut self,
        path: &'a NodePath<'a>,
        annotation: &'a TypeAnnotation<'a>,
    ) {
        let range = annotation.range();
        unwrap_or_return!(self.can_hover(range, path)).stop();

        self.result
            .replace((description::describe_type(annotation.r#type()), range));
    }

    fn enter_value_field(
        &mut self,
        path: &'a NodePath<'a>,
        struct_literal: &'a StructLiteral<'a>,
        field: &'a ValueField<'a>,
    ) {
        let range = field.name().range();
        unwrap_or_return!(self.can_hover(range, path)).stop();

        let struct_type = unwrap_or_return!(struct_literal.struct_type());

        self.result.replace((
            description::format_struct_field(struct_type, field.name().as_str()),
            range,
        ));
    }

    fn enter_member_expression(
        &mut self,
        path: &'a NodePath<'a>,
        member_expr: &'a MemberExpression<'a>,
    ) {
        let field = unwrap_or_return!(member_expr.field());
        let range = field.range();
        unwrap_or_return!(self.can_hover(range, path)).stop();

        let object_type = member_expr.object().r#type();
        let struct_type = unwrap_or_return!(object_type.struct_type());

        self.result.replace((
            description::format_struct_field(struct_type, field.as_str()),
            range,
        ));
    }

    fn enter_variable_expression(
        &mut self,
        path: &'a NodePath<'a>,
        expr: &'a VariableExpression<'a>,
    ) {
        let range = expr.range();
        unwrap_or_return!(self.can_hover(range, path)).stop();

        let binding = unwrap_or_return!(path.scope().get_binding(expr.name()));

        if let Some(pattern) = binding.variable_pattern() {
            self.result.replace((
                description::code_fence(description::format_local_variable(pattern)),
                range,
            ));
        } else if let Some(function_type) = binding.defined_function_type() {
            self.result
                .replace((description::code_fence(function_type.to_string()), range));
        } else if let Some(param) = binding.function_parameter() {
            self.result.replace((
                description::code_fence(description::format_function_parameter(param)),
                range,
            ));
        }
    }

    fn enter_variable_pattern(&mut self, path: &'a NodePath<'a>, pattern: &'a VariablePattern<'a>) {
        let range = pattern.range();
        unwrap_or_return!(self.can_hover(range, path)).stop();

        self.result.replace((
            description::code_fence(description::format_local_variable(pattern)),
            range,
        ));
    }
}
