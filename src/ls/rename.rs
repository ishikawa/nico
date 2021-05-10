//! Rename operation
use crate::syntax::{
    self, DefinitionKind, EffectiveRange, Expression, FunctionDefinition, FunctionParameter,
    Identifier, Node, NodePath, Pattern, Position, StructDefinition, StructLiteral, AST,
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

    pub fn prepare<'a>(&mut self, tree: &mut AST) -> Option<&Identifier> {
        self.operation = None;
        syntax::traverse(self, tree);
        self.operation.as_ref().map(|op| op.id.as_ref())
    }

    pub fn rename(&mut self, tree: &mut AST) -> Option<Vec<EffectiveRange>> {
        if let Some(RenameOperation { kind, .. }) = self.operation.as_ref() {
            match kind {
                RenameOperationKind::Definition(definition) => {
                    let mut visitor = RenameDefinition::new(definition);
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
                        RenameOperationKind::Definition(binding.kind().clone()),
                    ));
                }
            }
            // Renaming struct name
            else if parent.is_struct_literal() {
                // TODO: Use type info
                if let Some(binding) = scope.borrow().get_binding(id.as_str()) {
                    let binding = binding.borrow();

                    if let DefinitionKind::StructDefinition(_) = binding.kind() {
                        self.operation = Some(RenameOperation::new(
                            id,
                            RenameOperationKind::Definition(binding.kind().clone()),
                        ));
                    }
                }
            } else if let Some(struct_def) = parent.struct_definition() {
                self.operation = Some(RenameOperation::new(
                    id,
                    RenameOperationKind::Definition(DefinitionKind::StructDefinition(Rc::clone(
                        struct_def,
                    ))),
                ));
            }
            // Renaming function name
            else if let Some(function) = parent.function_definition() {
                self.operation = Some(RenameOperation::new(
                    id,
                    RenameOperationKind::Definition(DefinitionKind::FunctionDefinition(Rc::clone(
                        function,
                    ))),
                ));
            }
            // Renaming function parameter
            else if let Some(param) = parent.function_parameter() {
                self.operation = Some(RenameOperation::new(
                    id,
                    RenameOperationKind::Definition(DefinitionKind::FunctionParameter(Rc::clone(
                        param,
                    ))),
                ));
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

impl<'a> syntax::Visitor<'a> for RenameDefinition<'a> {
    fn enter_struct_definition(&mut self, _path: &mut NodePath, struct_def: &mut StructDefinition) {
        if let DefinitionKind::StructDefinition(definition) = self.definition {
            if std::ptr::eq(definition.as_ref(), struct_def.as_ref()) {
                if let Some(ref name) = struct_def.name {
                    self.ranges.push(name.range());
                }
            }
        }
    }

    fn enter_struct_literal(
        &mut self,
        path: &mut NodePath,
        _expr: &mut Expression,
        value: &StructLiteral,
    ) {
        let scope = path.scope();
        let scope = scope.borrow();

        let binding = match scope.get_binding(value.name().as_str()) {
            None => return,
            Some(binding) => binding,
        };
        let binding = binding.borrow();

        if binding.kind().ptr_eq(self.definition) {
            self.ranges.push(value.name().range());
        }
    }

    fn enter_function_definition(
        &mut self,
        _path: &mut NodePath,
        function: &mut FunctionDefinition,
    ) {
        if let DefinitionKind::FunctionDefinition(definition) = self.definition {
            if std::ptr::eq(definition.as_ref(), function.as_ref()) {
                if let Some(ref name) = function.name {
                    self.ranges.push(name.range());
                }
            }
        }
    }

    fn enter_function_parameter(&mut self, _path: &mut NodePath, param: &mut FunctionParameter) {
        if let DefinitionKind::FunctionParameter(definition) = self.definition {
            if std::ptr::eq(definition.as_ref(), param.as_ref()) {
                self.ranges.push(param.name().range());
            }
        }
    }

    fn enter_variable(&mut self, path: &mut NodePath, _expr: &mut Expression, id: &mut Identifier) {
        let scope = path.scope();
        let scope = scope.borrow();

        let binding = match scope.get_binding(id.as_str()) {
            None => return,
            Some(binding) => binding,
        };
        let binding = binding.borrow();

        if binding.kind().ptr_eq(self.definition) {
            self.ranges.push(id.range());
        }
    }

    fn enter_pattern(&mut self, _path: &mut NodePath, pattern: &mut Pattern) {
        if let DefinitionKind::Pattern(definition) = self.definition {
            if std::ptr::eq(definition.as_ref(), pattern.as_ref()) {
                self.ranges.push(pattern.range());
            }
        }
    }
}
