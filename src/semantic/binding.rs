use crate::arena::{BumpaloArena, BumpaloString};
use crate::semantic::{self, TypeKind};
use crate::syntax::{
    FunctionDefinition, FunctionParameter, StructDefinition, TypedNode, VariablePattern,
};
use std::fmt;

use super::{FunctionType, StructType};

#[derive(Debug, Clone)]
pub struct Binding<'a> {
    id: BumpaloString<'a>,
    r#type: TypeKind<'a>,
    kind: Option<BindingNodeKind<'a>>,
}

#[derive(Debug, Clone, Copy)]
enum BindingNodeKind<'a> {
    StructDefinition(&'a StructDefinition<'a>),
    FunctionDefinition(&'a FunctionDefinition<'a>),
    FunctionParameter(&'a FunctionParameter<'a>),
    VariablePattern(&'a VariablePattern<'a>),
}

impl<'a> Binding<'a> {
    pub fn alloc_function_in(
        arena: &'a BumpaloArena,
        function: &'a FunctionDefinition<'a>,
    ) -> Option<&'a Binding<'a>> {
        let name = function.name()?;

        let binding = Binding::alloc_in(
            arena,
            name.as_str(),
            function.r#type(),
            Some(BindingNodeKind::FunctionDefinition(function)),
        );

        Some(binding)
    }

    pub fn alloc_function_parameter_in(
        arena: &'a BumpaloArena,
        param: &'a FunctionParameter<'a>,
    ) -> &'a Binding<'a> {
        let binding = Binding::alloc_in(
            arena,
            param.name().as_str(),
            param.r#type(),
            Some(BindingNodeKind::FunctionParameter(param)),
        );

        binding
    }

    pub fn alloc_struct_in(
        arena: &'a BumpaloArena,
        struct_def: &'a StructDefinition<'a>,
    ) -> Option<&'a Binding<'a>> {
        let name = struct_def.name()?;

        let binding = Binding::alloc_in(
            arena,
            name.as_str(),
            struct_def.r#type(),
            Some(BindingNodeKind::StructDefinition(struct_def)),
        );

        Some(binding)
    }

    pub fn alloc_variable_pattern_in(
        arena: &'a BumpaloArena,
        pattern: &'a VariablePattern<'a>,
    ) -> &'a Binding<'a> {
        let binding = Binding::alloc_in(
            arena,
            pattern.name(),
            pattern.r#type(),
            Some(BindingNodeKind::VariablePattern(pattern)),
        );

        binding
    }

    fn new(id: BumpaloString<'a>, r#type: TypeKind<'a>, kind: Option<BindingNodeKind<'a>>) -> Self {
        Self { id, r#type, kind }
    }

    fn alloc_in<S: AsRef<str>>(
        arena: &'a BumpaloArena,
        name: S,
        r#type: TypeKind<'a>,
        kind: Option<BindingNodeKind<'a>>,
    ) -> &'a Binding<'a> {
        let binding = Self::new(
            BumpaloString::from_str_in(name.as_ref(), arena),
            r#type,
            kind,
        );

        arena.alloc(binding)
    }

    pub fn builtin_function<S: AsRef<str>>(
        arena: &'a BumpaloArena,
        name: S,
        parameters: &[(S, TypeKind<'a>)],
        return_type: TypeKind<'a>,
    ) -> &'a Binding<'a> {
        let params: Vec<_> = parameters
            .iter()
            .map(|(name, ty)| {
                &*arena.alloc(semantic::FunctionParameter::new(arena, name.as_ref(), *ty))
            })
            .collect();
        let fun_type = arena.alloc(semantic::FunctionType::new(
            arena,
            name.as_ref(),
            &params,
            return_type,
        ));

        Self::alloc_in(arena, name.as_ref(), TypeKind::FunctionType(fun_type), None)
    }

    pub fn id(&self) -> &str {
        self.id.as_str()
    }

    pub fn r#type(&self) -> TypeKind<'a> {
        self.r#type
    }

    pub fn struct_definition(&self) -> Option<&'a StructDefinition<'a>> {
        if let Some(BindingNodeKind::StructDefinition(node)) = self.kind {
            Some(node)
        } else {
            None
        }
    }

    pub fn function_definition(&self) -> Option<&'a FunctionDefinition<'a>> {
        if let Some(BindingNodeKind::FunctionDefinition(node)) = self.kind {
            Some(node)
        } else {
            None
        }
    }

    pub fn function_parameter(&self) -> Option<&'a FunctionParameter<'a>> {
        if let Some(BindingNodeKind::FunctionParameter(node)) = self.kind {
            Some(node)
        } else {
            None
        }
    }

    pub fn variable_pattern(&self) -> Option<&'a VariablePattern<'a>> {
        if let Some(BindingNodeKind::VariablePattern(node)) = self.kind {
            Some(node)
        } else {
            None
        }
    }

    /// Returns the function type if the binding points to a defined function.
    pub fn defined_function_type(&self) -> Option<&'a FunctionType<'a>> {
        if self.is_builtin() || self.function_definition().is_some() {
            self.r#type().function_type()
        } else {
            None
        }
    }

    /// Returns the struct type if the binding points to a defined struct.
    pub fn defined_struct_type(&self) -> Option<&'a StructType<'a>> {
        if self.is_builtin() || self.struct_definition().is_some() {
            self.r#type().struct_type()
        } else {
            None
        }
    }

    pub fn is_defined_function(&self) -> bool {
        self.defined_function_type().is_some()
    }

    pub fn is_defined_struct(&self) -> bool {
        self.defined_struct_type().is_some()
    }

    pub fn is_function_parameter(&self) -> bool {
        self.function_parameter().is_some()
    }

    pub fn is_function(&self) -> bool {
        self.function_definition().is_some() || self.r#type().is_function_type()
    }

    pub fn is_struct(&self) -> bool {
        self.struct_definition().is_some() || self.r#type().is_struct_type()
    }

    pub fn is_local_variable(&self) -> bool {
        self.variable_pattern().is_some()
    }

    pub fn is_builtin(&self) -> bool {
        self.kind.is_none()
    }
}

impl fmt::Display for Binding<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_function_parameter() {
            write!(f, "function parameter `{}`", self.id())
        } else if self.is_function() {
            write!(f, "function `{}`", self.id())
        } else if self.is_struct() {
            write!(f, "struct `{}`", self.id())
        } else if self.is_local_variable() {
            write!(f, "local variable `{}`", self.id())
        } else {
            write!(f, "`{}`", self.id())
        }
    }
}
