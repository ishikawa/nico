//! Rename operation
use crate::arena::BumpaloArena;
use crate::syntax::VariableExpression;
use crate::syntax::VariablePattern;
use crate::{
    semantic::DefinitionKind,
    syntax::{
        self, EffectiveRange, FunctionDefinition, FunctionParameter, Identifier, Node, NodePath,
        Position, Program, StructDefinition, StructLiteral,
    },
};

#[derive(Debug)]
pub struct Rename<'a> {
    arena: &'a BumpaloArena,
    position: Position,
    operation: Option<RenameOperation<'a>>,
}

impl<'a> Rename<'a> {
    pub fn new(arena: &'a BumpaloArena, position: Position) -> Self {
        Self {
            arena,
            position,
            operation: None,
        }
    }

    pub fn prepare(&mut self, program: &'a Program<'a>) -> Option<&'a Identifier<'a>> {
        self.operation = None;
        syntax::traverse(self.arena, self, program);
        self.operation.as_ref().map(|op| op.id)
    }

    pub fn rename(&mut self, program: &'a Program<'a>) -> Option<Vec<EffectiveRange>> {
        if let Some(RenameOperation { kind, .. }) = self.operation.as_ref() {
            match kind {
                RenameOperationKind::Definition(definition) => {
                    let mut visitor = RenameDefinition::new(definition.clone());
                    syntax::traverse(self.arena, &mut visitor, program);

                    return Some(visitor.ranges);
                }
                RenameOperationKind::Unknown => {}
            }
        }

        None
    }
}

impl<'a> syntax::Visitor<'a> for Rename<'a> {
    fn enter_identifier(&mut self, path: &'a NodePath<'a>, id: &'a Identifier<'a>) {
        // Prepare
        if self.operation.is_none() && id.range().contains(self.position) {
            let parent = path.expect_parent();
            let scope = parent.scope();
            let parent = parent.node();

            // Renaming variable
            if parent.is_variable_expression() {
                if let Some(binding) = scope.get_binding(id.as_str()) {
                    self.operation = Some(RenameOperation::new(
                        id,
                        RenameOperationKind::Definition(binding.kind().clone()),
                    ));
                }
            }
            // Renaming struct name
            else if parent.is_struct_literal() {
                // TODO: Use type info
                if let Some(binding) = scope.get_binding(id.as_str()) {
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
                    RenameOperationKind::Definition(DefinitionKind::StructDefinition(struct_def)),
                ));
            }
            // Renaming function name
            else if let Some(function) = parent.function_definition() {
                self.operation = Some(RenameOperation::new(
                    id,
                    RenameOperationKind::Definition(DefinitionKind::FunctionDefinition(function)),
                ));
            }
            // Renaming function parameter
            else if let Some(param) = parent.function_parameter() {
                self.operation = Some(RenameOperation::new(
                    id,
                    RenameOperationKind::Definition(DefinitionKind::FunctionParameter(param)),
                ));
            }
            // Renaming pattern
            else if let Some(pattern) = parent.variable_pattern() {
                self.operation = Some(RenameOperation::new(
                    id,
                    RenameOperationKind::Definition(DefinitionKind::VariablePattern(pattern)),
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
struct RenameOperation<'a> {
    id: &'a Identifier<'a>,
    kind: RenameOperationKind<'a>,
}

impl<'a> RenameOperation<'a> {
    fn new(id: &'a Identifier<'a>, kind: RenameOperationKind<'a>) -> Self {
        Self { id, kind }
    }
}

#[derive(Debug, Clone)]
enum RenameOperationKind<'a> {
    Definition(DefinitionKind<'a>),
    Unknown,
}

#[derive(Debug)]
struct RenameDefinition<'a> {
    definition: DefinitionKind<'a>,
    ranges: Vec<EffectiveRange>,
}

impl<'a> RenameDefinition<'a> {
    fn new(definition: DefinitionKind<'a>) -> Self {
        Self {
            definition,
            ranges: vec![],
        }
    }

    fn definition(&self) -> &DefinitionKind<'a> {
        &self.definition
    }
}

impl<'a> syntax::Visitor<'a> for RenameDefinition<'a> {
    fn enter_struct_definition(
        &mut self,
        _path: &'a NodePath<'a>,
        struct_def: &'a StructDefinition<'a>,
    ) {
        if let DefinitionKind::StructDefinition(definition) = self.definition {
            if std::ptr::eq(definition, struct_def) {
                if let Some(name) = struct_def.name() {
                    self.ranges.push(name.range());
                }
            }
        }
    }

    fn enter_struct_literal(&mut self, path: &'a NodePath<'a>, value: &'a StructLiteral<'a>) {
        let scope = path.scope();

        let binding = match scope.get_binding(value.name().as_str()) {
            None => return,
            Some(binding) => binding,
        };

        if binding.kind().ptr_eq(self.definition()) {
            self.ranges.push(value.name().range());
        }
    }

    fn enter_function_definition(
        &mut self,
        _path: &'a NodePath<'a>,
        function: &'a FunctionDefinition<'a>,
    ) {
        if let DefinitionKind::FunctionDefinition(definition) = self.definition {
            if std::ptr::eq(definition, function) {
                if let Some(name) = function.name() {
                    self.ranges.push(name.range());
                }
            }
        }
    }

    fn enter_function_parameter(
        &mut self,
        _path: &'a NodePath<'a>,
        param: &'a FunctionParameter<'a>,
    ) {
        if let DefinitionKind::FunctionParameter(definition) = self.definition {
            if std::ptr::eq(definition, param) {
                self.ranges.push(param.name().range());
            }
        }
    }

    fn enter_variable_expression(
        &mut self,
        path: &'a NodePath<'a>,
        expr: &'a VariableExpression<'a>,
    ) {
        let scope = path.scope();
        let binding = match scope.get_binding(expr.name()) {
            None => return,
            Some(binding) => binding,
        };

        if binding.kind().ptr_eq(self.definition()) {
            self.ranges.push(expr.range());
        }
    }

    fn enter_variable_pattern(
        &mut self,
        _path: &'a NodePath<'a>,
        pattern: &'a VariablePattern<'a>,
    ) {
        if let DefinitionKind::VariablePattern(definition) = self.definition {
            if std::ptr::eq(definition, pattern) {
                self.ranges.push(pattern.range());
            }
        }
    }
}
