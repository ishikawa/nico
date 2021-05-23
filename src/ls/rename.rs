//! Rename operation
use crate::{
    semantic::DefinitionKind,
    syntax::{
        self, EffectiveRange, Expression, FunctionDefinition, FunctionParameter, Identifier, Node,
        NodePath, Pattern, Position, Program, StructDefinition, StructLiteral,
    },
};

#[derive(Debug)]
pub struct Rename<'a> {
    position: Position,
    operation: Option<RenameOperation<'a>>,
}

impl<'a> Rename<'a> {
    pub fn new(position: Position) -> Self {
        Self {
            position,
            operation: None,
        }
    }

    pub fn prepare(&mut self, program: &'a Program<'a>) -> Option<&'a Identifier<'a>> {
        self.operation = None;
        syntax::traverse(self, program);
        self.operation.as_ref().map(|op| op.id)
    }

    pub fn rename(&mut self, program: &'a Program<'a>) -> Option<Vec<EffectiveRange>> {
        if let Some(RenameOperation { kind, .. }) = self.operation.as_ref() {
            match kind {
                RenameOperationKind::Definition(definition) => {
                    let mut visitor = RenameDefinition::new(definition.clone());
                    syntax::traverse(&mut visitor, program);

                    return Some(visitor.ranges);
                }
                RenameOperationKind::Unknown => {}
            }
        }

        None
    }
}

impl<'a> syntax::Visitor<'a> for Rename<'a> {
    fn enter_identifier(&mut self, path: &mut NodePath<'a>, id: &'a Identifier<'a>) {
        // Prepare
        if self.operation.is_none() && id.range().contains(self.position) {
            let parent = path.expect_parent();
            let parent = parent.borrow();
            let scope = parent.scope();
            let parent = parent.node();

            // Renaming variable
            if parent.is_variable_expression() {
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
            else if let Some(pattern) = parent.pattern() {
                self.operation = Some(RenameOperation::new(
                    id,
                    RenameOperationKind::Definition(DefinitionKind::Pattern(pattern)),
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
        _path: &mut NodePath<'a>,
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

    fn enter_struct_literal(
        &mut self,
        path: &mut NodePath<'a>,
        _expr: &'a Expression<'a>,
        value: &'a StructLiteral<'a>,
    ) {
        let scope = path.scope();
        let scope = scope.borrow();

        let binding = match scope.get_binding(value.name().as_str()) {
            None => return,
            Some(binding) => binding,
        };
        let binding = binding.borrow();

        if binding.kind().ptr_eq(self.definition()) {
            self.ranges.push(value.name().range());
        }
    }

    fn enter_function_definition(
        &mut self,
        _path: &mut NodePath<'a>,
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
        _path: &mut NodePath<'a>,
        param: &'a FunctionParameter<'a>,
    ) {
        if let DefinitionKind::FunctionParameter(definition) = self.definition {
            if std::ptr::eq(definition, param) {
                self.ranges.push(param.name().range());
            }
        }
    }

    fn enter_variable(
        &mut self,
        path: &mut NodePath<'a>,
        _expr: &'a Expression<'a>,
        id: &'a Identifier<'a>,
    ) {
        let scope = path.scope();
        let scope = scope.borrow();

        let binding = match scope.get_binding(id.as_str()) {
            None => return,
            Some(binding) => binding,
        };
        let binding = binding.borrow();

        if binding.kind().ptr_eq(self.definition()) {
            self.ranges.push(id.range());
        }
    }

    fn enter_pattern(&mut self, _path: &mut NodePath<'a>, pattern: &'a Pattern<'a>) {
        if let DefinitionKind::Pattern(definition) = self.definition {
            if std::ptr::eq(definition, pattern) {
                self.ranges.push(pattern.range());
            }
        }
    }
}
