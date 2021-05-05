use crate::syntax::{self, EffectiveRange, Position, Program};
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

impl syntax::Visitor for Hover {}
