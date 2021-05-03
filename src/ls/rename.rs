//! Rename operation
use crate::syntax::{
    self, DefinitionKind, EffectiveRange, FunctionDefinition, Identifier, Node, NodePath, Position,
    Program, StructDefinition,
};
use std::rc::Rc;

#[derive(Debug)]
pub struct Rename {
    position: Position,
    operation: Option<RenameOperation>,
}

impl Rename {
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

    pub fn rename(&mut self, program: &Rc<Program>) -> Option<Vec<EffectiveRange>> {
        if let Some(RenameOperation { kind, .. }) = self.operation.as_ref() {
            match kind {
                RenameOperationKind::Definition(definition) => {
                    let mut visitor = RenameDefinition::new(definition);
                    syntax::traverse(&mut visitor, program);

                    return Some(visitor.ranges);
                }
                RenameOperationKind::Unknown => {}
            }
        }

        return None;
    }
}

impl syntax::Visitor for Rename {
    fn enter_identifier(&mut self, path: &mut NodePath, id: &Rc<Identifier>) {
        // Prepare
        if self.operation.is_none() && id.range().contains(self.position) {
            let parent = path
                .parent()
                .unwrap_or_else(|| panic!("parent must exist."));

            let parent = parent.borrow();
            let scope = parent.scope();
            let parent = parent.node();

            if parent.is_variable_expression() {
                if let Some(binding) = scope.borrow().get_binding(id.as_str()) {
                    let binding = binding.borrow();

                    self.operation = Some(RenameOperation::new(
                        id,
                        RenameOperationKind::Definition(binding.kind().clone()),
                    ));
                }
            } else if let Some(function) = parent.function_definition() {
                self.operation = Some(RenameOperation::new(
                    id,
                    RenameOperationKind::Definition(DefinitionKind::FunctionDefinition(Rc::clone(
                        function,
                    ))),
                ));
            } else {
                // dummy
                self.operation = Some(RenameOperation::new(id, RenameOperationKind::Unknown));
            }

            path.stop();
        }
    }
}

// --- Operations

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

#[derive(Debug)]
struct RenameDefinition<'a> {
    definition: &'a DefinitionKind,
    ranges: Vec<EffectiveRange>,
}

impl<'a> RenameDefinition<'a> {
    fn new(definition: &'a DefinitionKind) -> Self {
        Self {
            definition,
            ranges: vec![],
        }
    }
}

impl<'a> syntax::Visitor for RenameDefinition<'a> {
    fn enter_struct_definition(&mut self, _path: &mut NodePath, struct_def: &Rc<StructDefinition>) {
        if let DefinitionKind::StructDefinition(definition) = self.definition {
            if std::ptr::eq(definition.as_ref(), struct_def.as_ref()) {
                eprintln!("Found: {}", struct_def);
                if let Some(ref name) = struct_def.name {
                    self.ranges.push(name.range());
                }
            }
        }
    }

    fn enter_function_definition(
        &mut self,
        _path: &mut NodePath,
        function: &Rc<FunctionDefinition>,
    ) {
        if let DefinitionKind::FunctionDefinition(definition) = self.definition {
            if std::ptr::eq(definition.as_ref(), function.as_ref()) {
                eprintln!("Found: {}", function);
                if let Some(ref name) = function.name {
                    self.ranges.push(name.range());
                }
            }
        }
    }

    fn enter_variable(&mut self, path: &mut NodePath, id: &Rc<Identifier>) {
        let scope = path.scope();
        let scope = scope.borrow();

        let binding = match scope.get_binding(id.as_str()) {
            None => return,
            Some(binding) => binding,
        };
        let binding = binding.borrow();

        if binding.kind().ptr_eq(self.definition) {
            eprintln!("Found: {}", path.node());
            self.ranges.push(id.range());
        }
    }
}
