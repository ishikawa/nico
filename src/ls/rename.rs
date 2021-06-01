//! Rename operation
use crate::arena::BumpaloArena;
use crate::semantic::StructType;
use crate::syntax::{
    self, Binding, EffectiveRange, FunctionDefinition, FunctionParameter, Identifier, Node,
    NodePath, Position, Program, StructDefinition, StructLiteral, VariableExpression,
    VariablePattern,
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
        self.operation.as_ref().map(|op| op.id())
    }

    pub fn rename(&mut self, program: &'a Program<'a>) -> Option<Vec<EffectiveRange>> {
        if let Some(operation) = self.operation.as_ref() {
            match operation.kind() {
                RenameOperationKind::Binding(semantic_value) => {
                    let mut visitor = RenameBinding::new(semantic_value);

                    syntax::traverse(self.arena, &mut visitor, program);
                    return Some(visitor.ranges);
                }
                RenameOperationKind::StructField(_, _) => todo!(),
            }
        }

        None
    }

    fn rename_operation_for_identifier(
        &self,
        path: &'a NodePath<'a>,
        id: &'a Identifier<'a>,
    ) -> Option<RenameOperation<'a>> {
        let parent = path.expect_parent();
        let scope = parent.scope();
        let parent = parent.node();

        // Renaming variable
        if parent.is_variable_expression() {
            let binding = scope.get_binding(id.as_str())?;
            return Some(RenameOperation::rename_binding(id, binding));
        }
        // Renaming struct name
        else if parent.is_struct_literal() {
            let binding = scope.get_binding(id.as_str())?;

            if binding.is_struct() {
                return Some(RenameOperation::rename_binding(id, binding));
            }
        } else if let Some(struct_def) = parent.struct_definition() {
            let binding = struct_def.binding()?;
            return Some(RenameOperation::rename_binding(id, binding));
        }
        // Renaming struct member
        else if let Some(member_expr) = parent.member_expression() {
            // In the case of MemberExpression, rename is possible only if
            // the target object type is struct.
            let object_type = member_expr.object().r#type()?;
            let struct_type = object_type.struct_type()?;

            return Some(RenameOperation::rename_struct_field(struct_type, id));
        } else if parent.is_type_field() || parent.is_value_field() {
            todo!();
        }
        // Renaming function name
        else if let Some(function) = parent.function_definition() {
            let binding = function.binding()?;
            return Some(RenameOperation::rename_binding(id, binding));
        }
        // Renaming function parameter
        else if let Some(param) = parent.function_parameter() {
            let binding = param.binding()?;
            return Some(RenameOperation::rename_binding(id, binding));
        }
        // Renaming pattern
        else if let Some(pattern) = parent.variable_pattern() {
            let binding = pattern.binding()?;
            return Some(RenameOperation::rename_binding(id, binding));
        }

        None
    }
}

impl<'a> syntax::Visitor<'a> for Rename<'a> {
    fn enter_identifier(&mut self, path: &'a NodePath<'a>, id: &'a Identifier<'a>) {
        // Prepare
        if self.operation.is_none() && id.range().contains(self.position) {
            self.operation = self.rename_operation_for_identifier(path, id);
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

    fn rename_binding(id: &'a Identifier<'a>, binding: &'a Binding<'a>) -> Self {
        Self::new(id, RenameOperationKind::Binding(binding))
    }

    fn rename_struct_field(struct_type: &'a StructType<'a>, id: &'a Identifier<'a>) -> Self {
        Self::new(id, RenameOperationKind::StructField(struct_type, id))
    }

    fn id(&self) -> &'a Identifier<'a> {
        self.id
    }

    fn kind(&self) -> RenameOperationKind<'a> {
        self.kind
    }
}

#[derive(Debug, Clone, Copy)]
enum RenameOperationKind<'a> {
    Binding(&'a Binding<'a>),
    StructField(&'a StructType<'a>, &'a Identifier<'a>),
}

#[derive(Debug)]
struct RenameBinding<'a> {
    binding: &'a Binding<'a>,
    ranges: Vec<EffectiveRange>,
}

impl<'a> RenameBinding<'a> {
    fn new(binding: &'a Binding<'a>) -> Self {
        Self {
            binding,
            ranges: vec![],
        }
    }

    fn binding(&self) -> &'a Binding<'a> {
        &self.binding
    }
}

impl<'a> syntax::Visitor<'a> for RenameBinding<'a> {
    fn enter_struct_definition(
        &mut self,
        _path: &'a NodePath<'a>,
        struct_def: &'a StructDefinition<'a>,
    ) {
        if let Some(binding) = struct_def.binding() {
            if std::ptr::eq(self.binding(), binding) {
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

        if std::ptr::eq(self.binding(), binding) {
            self.ranges.push(value.name().range());
        }
    }

    fn enter_function_definition(
        &mut self,
        _path: &'a NodePath<'a>,
        function: &'a FunctionDefinition<'a>,
    ) {
        if let Some(binding) = function.binding() {
            if std::ptr::eq(self.binding(), binding) {
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
        if let Some(binding) = param.binding() {
            if std::ptr::eq(self.binding(), binding) {
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

        if std::ptr::eq(self.binding(), binding) {
            self.ranges.push(expr.range());
        }
    }

    fn enter_variable_pattern(
        &mut self,
        _path: &'a NodePath<'a>,
        pattern: &'a VariablePattern<'a>,
    ) {
        if let Some(binding) = pattern.binding() {
            if std::ptr::eq(self.binding(), binding) {
                self.ranges.push(pattern.range());
            }
        }
    }
}
