use crate::{
    sem,
    semantic::Struct,
    syntax::{
        self, EffectiveRange, Node, NodePath, Position, StructDefinition, TypeAnnotation,
        ValueField, AST,
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

    pub fn describe(&mut self, tree: &mut AST) -> Option<(&str, EffectiveRange)> {
        syntax::traverse(self, tree);
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

    fn describe_value_field(&self, tree: &AST, definition: &Struct, field: &ValueField) -> String {
        let ty = definition.get_field_type(tree, field.name(tree).as_str());

        format!(
            "```nico\n{}.{}: {}\n```",
            definition.name(),
            field.name(tree),
            self.describe_optional(ty.map(|x| x.borrow().to_string())),
        )
    }
}

impl<'a> syntax::Visitor<'a> for Hover {
    fn enter_type_annotation(&mut self, path: &mut NodePath, annotation: &mut TypeAnnotation) {
        if !annotation.range(path.tree()).contains(self.position) {
            return;
        }

        self.result.replace((
            self.describe_type(&annotation.r#type),
            annotation.range(path.tree()),
        ));
        path.stop();
    }

    fn enter_value_field(&mut self, path: &mut NodePath, field: &mut ValueField) {
        if !field
            .name(path.tree())
            .range(path.tree())
            .contains(self.position)
        {
            return;
        }

        let parent = path.expect_parent();
        let parent = parent.borrow();
        let scope = parent.scope();
        let parent = parent.node();

        let literal = parent.expression().unwrap().struct_literal().unwrap();

        // TODO: Use type info
        if let Some(binding) = scope
            .borrow()
            .get_binding(literal.name(path.tree()).as_str())
        {
            let binding = binding.borrow();
            let value = binding.value().borrow();

            if let Some(struct_value) = value.kind().r#struct() {
                self.result.replace((
                    self.describe_value_field(path.tree(), struct_value, field),
                    field.name(path.tree()).range(path.tree()),
                ));
            }
        }

        path.stop();
    }
}
