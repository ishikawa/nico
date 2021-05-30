use crate::arena::BumpaloArena;
use crate::{
    sem,
    syntax::{
        self, EffectiveRange, Node, NodePath, Position, Program, StructDefinition, TypeAnnotation,
        ValueField,
    },
};
use std::{cell::RefCell, fmt, rc::Rc};

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

    fn describe_optional<T: fmt::Display>(&self, name: Option<T>) -> String {
        name.map_or("{{unknown}}".to_string(), |x| x.to_string())
    }

    fn describe_type(&self, r#type: &Rc<RefCell<sem::Type>>) -> String {
        let description = match *r#type.borrow() {
            sem::Type::Int32 => "The 32-bit signed integer type.",
            sem::Type::Boolean => "The boolean type.",
            _ => "",
        };

        format!("```nico\n{}\n```\n---\n{}", r#type.borrow(), description)
    }

    fn describe_value_field(
        &self,
        definition: &'a StructDefinition<'a>,
        field: &'a ValueField<'a>,
    ) -> String {
        let ty = definition.get_field_type(field.name().as_str());

        format!(
            "```nico\n{}.{}: {}\n```",
            self.describe_optional(definition.name()),
            field.name(),
            self.describe_optional(ty.map(|x| x.borrow().to_string())),
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
            .replace((self.describe_type(&annotation.r#type()), annotation.range()));
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
            if let DefinitionKind::StructDefinition(ref definition) = binding.value() {
                self.result.replace((
                    self.describe_value_field(definition, field),
                    field.name().range(),
                ));
            }
        }

        path.stop();
    }
}
