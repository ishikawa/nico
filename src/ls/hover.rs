use crate::{
    sem,
    syntax::{
        self, DefinitionKind, EffectiveRange, Node, NodePath, Position, Program, StructDefinition,
        TypeAnnotation, ValueField,
    },
};
use std::{cell::RefCell, fmt, rc::Rc};

#[derive(Debug)]
pub struct Hover {
    position: Position,
    result: Option<(String, EffectiveRange)>,
}

impl Hover {
    pub fn new(position: Position) -> Self {
        Self {
            position,
            result: None,
        }
    }

    pub fn describe(&mut self, program: &Rc<Program>) -> Option<(&str, EffectiveRange)> {
        syntax::traverse(self, program);
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
        definition: &Rc<StructDefinition>,
        field: &Rc<ValueField>,
    ) -> String {
        let ty = definition.get_type(field.name().as_str());

        format!(
            "```nico\n{}.{}: {}\n```",
            self.describe_optional(definition.name()),
            field.name(),
            self.describe_optional(ty.map(|x| x.borrow().to_string())),
        )
    }
}

impl syntax::Visitor for Hover {
    fn enter_type_annotation(&mut self, path: &mut NodePath, annotation: &Rc<TypeAnnotation>) {
        if !annotation.range().contains(self.position) {
            return;
        }

        self.result
            .replace((self.describe_type(&annotation.r#type), annotation.range()));
        path.stop();
    }

    fn enter_value_field(&mut self, path: &mut NodePath, field: &Rc<ValueField>) {
        if !field.name().range().contains(self.position) {
            return;
        }

        let parent = path.expect_parent();
        let parent = parent.borrow();
        let scope = parent.scope();
        let parent = parent.node();

        let literal = parent.expression().unwrap().struct_literal().unwrap();

        // TODO: Use type info
        if let Some(binding) = scope.borrow().get_binding(literal.name().as_str()) {
            let binding = binding.borrow();

            if let DefinitionKind::StructDefinition(ref definition) = binding.kind() {
                self.result.replace((
                    self.describe_value_field(definition, field),
                    field.name().range(),
                ));
            }
        }

        path.stop();
    }
}
