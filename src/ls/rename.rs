//! Rename operation
use crate::syntax::{self, Identifier, Node, NodeKind, NodePath, Position};
use std::rc::Rc;

#[derive(Debug)]
pub struct PrepareRename {
    position: Position,
    found: Option<Rc<Identifier>>,
}

impl PrepareRename {
    pub fn find_identifier_at(node: &NodeKind, position: Position) -> Option<Rc<Identifier>> {
        let mut preparer = PrepareRename::new(position);

        syntax::traverse(&mut preparer, &node, None);

        preparer.found
    }

    pub fn new(position: Position) -> Self {
        Self {
            position,
            found: None,
        }
    }
}

impl syntax::Visitor for PrepareRename {
    fn enter_identifier(&mut self, path: &mut NodePath, id: &Rc<Identifier>) {
        if id.range().contains(self.position) {
            self.found = Some(Rc::clone(id));
            path.stop();
        }
    }
}
