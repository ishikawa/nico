//! Rename operation
use crate::syntax::{self, Identifier, Node, NodePath, Position, Program};
use std::rc::Rc;

#[derive(Debug)]
pub struct PrepareRename {
    position: Position,
    found: Option<Rc<Identifier>>,
}

impl PrepareRename {
    pub fn find_identifier_at(node: &Rc<Program>, position: Position) -> Option<Rc<Identifier>> {
        let mut preparer = PrepareRename::new(position);

        syntax::traverse(&mut preparer, node);

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

            let parent = path
                .parent()
                .unwrap_or_else(|| panic!("parent must exist."));

            eprintln!("found = {}, parent = {}", id, parent.borrow().node());
            path.stop();
        }
    }
}
