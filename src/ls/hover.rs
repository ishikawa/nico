use crate::syntax::{self, EffectiveRange, Node, NodePath, Position, Program, TypeAnnotation};
use std::rc::Rc;

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
}

impl syntax::Visitor for Hover {
    fn enter_type_annotation(&mut self, _path: &mut NodePath, annotation: &Rc<TypeAnnotation>) {
        if !annotation.range().contains(self.position) {
            return;
        }

        let description = format!(
            "```nico\n{}\n```\n---\nThe 32-bit signed integer type.",
            annotation.r#type.borrow()
        );

        self.result.replace((description, annotation.range()));
    }
}
