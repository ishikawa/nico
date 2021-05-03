//! Rename operation
use crate::syntax::{self, DefinitionKind, Identifier, Node, NodePath, Position, Program};
use std::rc::Rc;

#[derive(Debug)]
pub struct PrepareRename {
    position: Position,
    operation: Option<RenameOperation>,
}

#[derive(Debug)]
struct RenameOperation {
    id: Rc<Identifier>,
    kind: RenameOperationKind,
}

impl RenameOperation {
    fn new(id: &Rc<Identifier>, kind: RenameOperationKind) -> Self {
        Self {
            id: Rc::clone(id),
            kind,
        }
    }
}

#[derive(Debug, Clone)]
enum RenameOperationKind {
    Definition(DefinitionKind),
    Unknown,
}

impl PrepareRename {
    pub fn new(position: Position) -> Self {
        Self {
            position,
            operation: None,
        }
    }

    pub fn prepare(&mut self, program: &Rc<Program>) -> Option<&Identifier> {
        self.operation = None;
        syntax::traverse(self, program);
        self.operation.as_ref().map(|op| op.id.as_ref())
    }
}

impl syntax::Visitor for PrepareRename {
    fn enter_identifier(&mut self, path: &mut NodePath, id: &Rc<Identifier>) {
        // Prepare
        if self.operation.is_none() && id.range().contains(self.position) {
            let parent = path
                .parent()
                .unwrap_or_else(|| panic!("parent must exist."));

            let parent = parent.borrow();
            let scope = parent.scope();

            if parent.node().is_variable_expression() {
                if let Some(binding) = scope.borrow().get_binding(id.as_str()) {
                    let binding = binding.borrow();

                    self.operation = Some(RenameOperation::new(
                        id,
                        RenameOperationKind::Definition(binding.kind().clone()),
                    ));
                }
            } else {
                // dummy
                self.operation = Some(RenameOperation::new(id, RenameOperationKind::Unknown));
            }

            path.stop();
            return;
        }
    }
}
