use crate::{
    sem,
    syntax::{self, EffectiveRange, Node, NodePath, Position, Program, TypeAnnotation},
};
use std::{cell::RefCell, rc::Rc};

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

    fn describe_type(&self, r#type: &Rc<RefCell<sem::Type>>) -> String {
        let description = match *r#type.borrow() {
            sem::Type::Int32 => "The 32-bit signed integer type.",
            sem::Type::Boolean => "The boolean type.",
            _ => "",
        };

        format!("```nico\n{}\n```\n---\n{}", r#type.borrow(), description)
    }
}

impl syntax::Visitor for Hover {
    fn enter_type_annotation(&mut self, _path: &mut NodePath, annotation: &Rc<TypeAnnotation>) {
        if !annotation.range().contains(self.position) {
            return;
        }

        self.result
            .replace((self.describe_type(&annotation.r#type), annotation.range()));
    }
}
