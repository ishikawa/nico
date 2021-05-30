use std::fmt::Display;

use crate::arena::BumpaloArena;
use crate::semantic::StructType;
use crate::semantic::TypeKind;
use crate::syntax::{
    self, EffectiveRange, Node, NodePath, Position, Program, TypeAnnotation, ValueField,
};

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

    fn describe_value_field(
        &self,
        struct_type: &'a StructType<'a>,
        field: &'a ValueField<'a>,
    ) -> String {
        let ty = struct_type.get_field_type(field.name().as_str());

        format!(
            "```nico\n{}.{}: {}\n```",
            struct_type.name(),
            field.name(),
            self.describe_optional(ty),
        )
    }
}

impl<'a> syntax::Visitor<'a> for Hover<'a> {
    fn enter_type_annotation(
        &mut self,
        path: &'a NodePath<'a>,
        annotation: &'a TypeAnnotation<'a>,
    ) {
        if !annotation.range().contains(self.position) {
            return;
        }

        self.result
            .replace((self.describe_type(annotation.r#type()), annotation.range()));
        path.stop();
    }

    fn enter_value_field(&mut self, path: &'a NodePath<'a>, field: &'a ValueField<'a>) {
        if !field.name().range().contains(self.position) {
            return;
        }

        let parent = path.expect_parent();
        let scope = parent.scope();
        let parent = parent.node();

        let literal = parent.struct_literal().unwrap();

        // TODO: Use type info
        if let Some(binding) = scope.get_binding(literal.name().as_str()) {
            let value = binding.semantic_value();

            if let Some(struct_type) = value.r#type().struct_type() {
                self.result.replace((
                    self.describe_value_field(struct_type, field),
                    field.name().range(),
                ));
            }
        }

        path.stop();
    }
}
