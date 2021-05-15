//! Rename operation
use crate::{
    semantic,
    syntax::{
        self, Ast, EffectiveRange, Expression, Identifier, Node, NodeId, NodePath, Pattern,
        PatternKind, Position, StructDefinition, StructLiteral,
    },
};
use std::{cell::RefCell, rc::Rc};

#[derive(Debug)]
pub struct Rename {
    position: Position,
    operation: Option<RenameStructNameOperation>,
}

impl Rename {
    pub fn new(position: Position) -> Self {
        Self {
            position,
            operation: None,
        }
    }

    pub fn prepare<'a>(&mut self, tree: &'a Ast) -> Option<&'a Identifier> {
        self.operation = None;
        syntax::traverse(self, tree);

        self.operation
            .as_ref()
            .and_then(move |op| tree.get(op.id))
            .and_then(|node_kind| node_kind.identifier())
    }

    pub fn rename(&mut self, tree: &Ast) -> Option<Vec<EffectiveRange>> {
        let operation = self.operation.as_mut()?;
        syntax::traverse(operation, tree);

        return Some(operation.ranges().iter().copied().collect());
    }
}

impl syntax::Visitor for Rename {
    fn enter_identifier(&mut self, tree: &Ast, path: &mut NodePath, id: &Identifier) {
        let node_id = path.node_id();

        // Prepare
        if self.operation.is_none() && id.range(tree).contains(self.position) {
            let parent = path.expect_parent();
            let parent = parent.borrow();
            let scope = parent.scope();
            let parent = parent.node(tree);

            // Renaming struct name
            if parent.is_struct_literal() {
                // TODO: Use type info
                if let Some(binding) = scope.borrow().get_binding(id.as_str()) {
                    let binding = binding.borrow();

                    if let Some(value) = binding.value().r#struct() {
                        self.operation =
                            Some(RenameStructNameOperation::new(node_id, Rc::clone(value)));
                    }
                }
            } else if let Some(struct_def) = parent.struct_definition() {
                if let Some(value) = struct_def.semantic_value() {
                    self.operation =
                        Some(RenameStructNameOperation::new(node_id, Rc::clone(value)));
                }
            }

            path.stop();
        }
    }
}

// --- Operations
trait RenameVisitor<'a>: syntax::Visitor + std::fmt::Debug {
    fn ranges(&self) -> &[EffectiveRange];
}

#[derive(Debug)]
struct RenameStructNameOperation {
    id: NodeId, // Identifier
    value: Rc<RefCell<semantic::Struct>>,
    ranges: Vec<EffectiveRange>,
}

impl RenameStructNameOperation {
    fn new(
        id: NodeId, // Identifier
        value: Rc<RefCell<semantic::Struct>>,
    ) -> Self {
        Self {
            id,
            value,
            ranges: vec![],
        }
    }
}

impl<'a> RenameVisitor<'a> for RenameStructNameOperation {
    fn ranges(&self) -> &[EffectiveRange] {
        &self.ranges
    }
}

impl syntax::Visitor for RenameStructNameOperation {
    fn enter_struct_definition(
        &mut self,
        tree: &Ast,
        _path: &mut NodePath,
        struct_def: &StructDefinition,
    ) {
        if let Some(value) = struct_def.semantic_value() {
            if std::ptr::eq(value.as_ref(), self.value.as_ref()) {
                if let Some(name) = struct_def.name(tree) {
                    self.ranges.push(name.range(tree));
                }
            }
        }
    }

    fn enter_struct_literal(
        &mut self,
        tree: &Ast,
        _path: &mut NodePath,
        _expr: &Expression,
        literal: &StructLiteral,
    ) {
        if let Some(value) = literal.semantic_value() {
            if std::ptr::eq(value.as_ref(), self.value.as_ref()) {
                let name = literal.name(tree);
                self.ranges.push(name.range(tree));
            }
        }
    }

    fn enter_pattern(&mut self, tree: &Ast, _path: &mut NodePath, pattern: &Pattern) {
        if let PatternKind::StructPattern(pat) = pattern.kind() {
            if let Some(value) = pat.semantic_value() {
                if std::ptr::eq(value.as_ref(), self.value.as_ref()) {
                    let name = pat.name(tree);
                    self.ranges.push(name.range(tree));
                }
            }
        }
    }
}

/*
#[derive(Debug)]
struct RenameOperation {
    id: NodeId, // Identifier
    kind: SemanticValueKind,
    ranges: Vec<EffectiveRange>,
}

impl RenameOperation {
    fn new(id: NodeId, kind: SemanticValueKind) -> Self {
        Self {
            id,
            kind,
            ranges: vec![],
        }
    }

    fn add_node(&mut self, tree: &AST, node_id: NodeId) {
        if let Some(node) = tree.get(node_id) {
            self.ranges.push(node.range(tree));
        }
    }

    fn matches_node(&self, node: NodeId) -> bool {
        if let Some(node_id) = self.kind.node_id() {
            node == node_id
        } else {
            false
        }
    }
}

impl syntax::Visitor for RenameOperation {
    // definition

    fn enter_struct_definition(&mut self, tree: &'a AST, path: &mut NodePath, struct_def: &mut StructDefinition) {
        if self.matches_node(path.node_id()) {


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


            if let Some(ref name) = function.name(tree) {
                self.ranges.push(name.range(tree));
            }
        }
    }

    fn enter_function_parameter(&mut self, tree: &'a AST, path: &mut NodePath, param: &mut FunctionParameter) {
        if self.matches_node(param.name_id()) {

            self.ranges.push(param.name(tree).range(tree));
        }
    }

    fn enter_pattern(&mut self, tree: &'a AST, _path: &mut NodePath, pattern: &mut Pattern) {
        if let Some(value) = pattern.variable_semantic_value() {
            if std::ptr::eq(definition.as_ref(), pattern.as_ref()) {
                self.ranges.push(pattern.range());
            }
        }

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

    fn enter_variable(&mut self, tree: &'a AST, path: &mut NodePath, _expr: &mut Expression, id: &Identifier) {

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
 */
