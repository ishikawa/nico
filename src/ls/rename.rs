//! Rename operation
use crate::{
    semantic::SemanticValue,
    syntax::{
        self, EffectiveRange, Expression, FunctionDefinition, FunctionParameter, Identifier, Node,
        NodeId, NodePath, Pattern, Position, StructDefinition, StructLiteral, AST,
    },
};
use std::{cell::RefCell, rc::Rc};

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

    pub fn prepare<'a>(&mut self, tree: &mut AST) -> Option<&Identifier> {
        self.operation = None;
        syntax::traverse(self, tree);
        self.operation.as_ref().map(|op| op.id.as_ref())
    }

    pub fn rename(&mut self, tree: &mut AST) -> Option<Vec<EffectiveRange>> {
        if let Some(RenameOperation { kind, .. }) = self.operation.as_ref() {
            match kind {
                RenameOperationKind::Definition(value) => {
                    let mut visitor = RenameDefinition::new(Rc::clone(value));
                    syntax::traverse(&mut visitor, tree);

                    return Some(visitor.ranges);
                }
                RenameOperationKind::Unknown => {}
            }
        }

        None
    }
}

impl<'a> syntax::Visitor<'a> for Rename {
    fn enter_identifier(&mut self, path: &mut NodePath, id: &mut Identifier) {
        // Prepare
        if self.operation.is_none() && id.range(path.tree()).contains(self.position) {
            let parent = path.expect_parent();
            let parent = parent.borrow();
            let scope = parent.scope();
            let parent = parent.node();

            // Renaming variable
            if parent.is_variable_expression(path.tree()) {
                if let Some(binding) = scope.borrow().get_binding(id.as_str()) {
                    let binding = binding.borrow();

                    self.operation = Some(RenameOperation::new(
                        id,
                        RenameOperationKind::Definition(Rc::clone(binding.value())),
                    ));
                }
            }
            // Renaming struct name
            else if parent.is_struct_literal() {
                // TODO: Use type info
                if let Some(binding) = scope.borrow().get_binding(id.as_str()) {
                    let binding = binding.borrow();

                    if binding.value().borrow().kind().is_struct() {
                        self.operation = Some(RenameOperation::new(
                            id,
                            RenameOperationKind::Definition(Rc::clone(binding.value())),
                        ));
                    }
                }
            } else if let Some(struct_def) = parent.struct_definition() {
                if let Some(value) = struct_def.semantic_value() {
                    self.operation = Some(RenameOperation::new(
                        id,
                        RenameOperationKind::Definition(Rc::clone(value)),
                    ));
                }
            }
            // Renaming function name
            else if let Some(function) = parent.function_definition() {
                if let Some(value) = function.semantic_value() {
                    self.operation = Some(RenameOperation::new(
                        id,
                        RenameOperationKind::Definition(Rc::clone(value)),
                    ));
                }
            }
            // Renaming function parameter
            else if let Some(param) = parent.function_parameter() {
                if let Some(value) = param.semantic_value() {
                    self.operation = Some(RenameOperation::new(
                        id,
                        RenameOperationKind::Definition(Rc::clone(value)),
                    ));
                }
            }
            // Renaming pattern
            else if let Some(pattern) = parent.pattern() {
                self.operation = Some(RenameOperation::new(
                    id,
                    RenameOperationKind::Definition(DefinitionKind::Pattern(Rc::clone(pattern))),
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
    fn new(id: &mut Identifier, kind: RenameOperationKind) -> Self {
        Self {
            id: Rc::clone(id),
            kind,
        }
    }
}

#[derive(Debug, Clone)]
enum RenameOperationKind {
    Definition(Rc<RefCell<SemanticValue>>),
    Unknown,
}

#[derive(Debug)]
struct RenameDefinition {
    value: Rc<RefCell<SemanticValue>>,
    ranges: Vec<EffectiveRange>,
}

impl RenameDefinition {
    fn new(value: Rc<RefCell<SemanticValue>>) -> Self {
        Self {
            value,
            ranges: vec![],
        }
    }

    fn matches_node(&self, node: NodeId) -> bool {
        let value = self.value.borrow();

        if let Some(node_id) = value.node_id() {
            node == node_id
        } else {
            false
        }
    }
}

impl<'a> syntax::Visitor<'a> for RenameDefinition {
    // definition

    fn enter_struct_definition(&mut self, path: &mut NodePath, struct_def: &mut StructDefinition) {
        if self.matches_node(path.node_id()) {
            let tree = path.tree();

            if let Some(ref name) = struct_def.name(tree) {
                self.ranges.push(name.range(tree));
            }
        }
    }

    fn enter_function_definition(
        &mut self,
        path: &mut NodePath,
        function: &mut FunctionDefinition,
    ) {
        if self.matches_node(path.node_id()) {
            let tree = path.tree();

            if let Some(ref name) = function.name(tree) {
                self.ranges.push(name.range(tree));
            }
        }
    }

    fn enter_function_parameter(&mut self, path: &mut NodePath, param: &mut FunctionParameter) {
        if self.matches_node(param.name_id()) {
            let tree = path.tree();
            self.ranges.push(param.name(tree).range(tree));
        }
    }

    fn enter_pattern(&mut self, _path: &mut NodePath, pattern: &mut Pattern) {
        if let DefinitionKind::Pattern(definition) = self.definition {
            if std::ptr::eq(definition.as_ref(), pattern.as_ref()) {
                self.ranges.push(pattern.range());
            }
        }
    }

    // reference

    fn enter_struct_literal(
        &mut self,
        path: &mut NodePath,
        _expr: &mut Expression,
        literal: &StructLiteral,
    ) {
        let tree = path.tree();
        let scope = path.scope();
        let scope = scope.borrow();

        let binding = match scope.get_binding(literal.name(tree).as_str()) {
            None => return,
            Some(binding) => binding,
        };
        let binding = binding.borrow();

        if binding.value().borrow().node_id() == self.value.borrow().node_id() {
            self.ranges.push(literal.name(tree).range(tree));
        }
    }

    fn enter_variable(&mut self, path: &mut NodePath, _expr: &mut Expression, id: &Identifier) {
        let tree = path.tree();
        let scope = path.scope();
        let scope = scope.borrow();

        let binding = match scope.get_binding(id.as_str()) {
            None => return,
            Some(binding) => binding,
        };
        let binding = binding.borrow();

        if binding.value().borrow().node_id() == self.value.borrow().node_id() {
            self.ranges.push(id.range(tree));
        }
    }
}
