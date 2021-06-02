use std::fmt::Display;

use crate::arena::BumpaloArena;
use crate::semantic::StructType;
use crate::semantic::TypeKind;
use crate::syntax::MemberExpression;
use crate::syntax::StructLiteral;
use crate::syntax::TypeField;
use crate::syntax::{
    self, EffectiveRange, Node, NodePath, Position, Program, TypeAnnotation, ValueField,
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

    fn describe_optional<T: Display>(&self, name: Option<T>) -> String {
        name.map_or("{{unknown}}".to_string(), |x| x.to_string())
    }

    fn describe_type(&self, ty: TypeKind<'a>) -> String {
        let description = match ty {
            TypeKind::Int32 => "The 32-bit signed integer type.",
            TypeKind::Boolean => "The boolean type.",
            _ => "",
        };

        format!("```nico\n{}\n```\n---\n{}", ty, description)
    }

    fn describe_struct_field(&self, struct_type: &'a StructType<'a>, field_name: &str) -> String {
        let ty = struct_type.get_field_type(field_name);

        format!(
            "```nico\n{}.{}: {}\n```",
            struct_type.name(),
            field_name,
            self.describe_optional(ty),
        )
    }

    fn can_hover(&self, range: EffectiveRange, path: &'a NodePath<'a>) -> Option<&'a NodePath<'a>> {
        if range.contains(self.position) {
            return Some(path);
        } else {
            return None;
        }
    }
}

impl<'a> syntax::Visitor<'a> for Hover<'a> {
    fn enter_type_field(&mut self, path: &'a NodePath<'a>, field: &'a TypeField<'a>) {
        let field_name = unwrap_or_return!(field.name());
        let range = field_name.range();
        unwrap_or_return!(self.can_hover(range, path)).stop();

        let parent = path.expect_parent();
        let struct_def = unwrap_or_return!(parent.node().struct_definition());
        let struct_type = unwrap_or_return!(struct_def.struct_type());

        self.result.replace((
            self.describe_struct_field(struct_type, field_name.as_str()),
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
            .replace((self.describe_type(annotation.r#type()), range));
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
            self.describe_struct_field(struct_type, field.name().as_str()),
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

        let object_type = unwrap_or_return!(member_expr.object().r#type());
        let struct_type = unwrap_or_return!(object_type.struct_type());

        self.result.replace((
            self.describe_struct_field(struct_type, field.as_str()),
            range,
        ));
    }
}
