use crate::arena::BumpaloArena;
use crate::arena::{BumpaloString, BumpaloVec};
use crate::semantic::errors::TypeMismatchError;
use crate::semantic::SemanticError;
use crate::syntax::{
    self, ArrayExpression, BinaryExpression, BinaryOperator, CallExpression, CaseExpression,
    FunctionDefinition, GroupedExpression, IfExpression, MemberExpression, Node, NodeKind,
    NodePath, PatternKind, StructDefinition, StructLiteral, SubscriptExpression, TypeAnnotation,
    TypeAnnotationKind, TypedNode, UnaryExpression, UnaryOperator, ValueField, VariableDeclaration,
    VariableExpression, VariablePattern, Visitor,
};
use crate::unwrap_or_return;
use log::debug;
use std::cell::Cell;
use std::fmt;

use super::errors::TypeError;
use super::Scope;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TypeKind<'a> {
    Integer,
    Boolean,
    String,
    Void,
    StructType(&'a StructType<'a>),
    FunctionType(&'a FunctionType<'a>),
    ArrayType(&'a ArrayType<'a>),
    TypeVariable(&'a TypeVariable<'a>),
}

impl<'a> TypeKind<'a> {
    pub fn struct_type(&self) -> Option<&'a StructType<'a>> {
        match self {
            TypeKind::StructType(ty) => Some(ty),
            TypeKind::TypeVariable(var) => var.instance().and_then(|x| x.struct_type()),
            _ => None,
        }
    }

    pub fn function_type(&self) -> Option<&'a FunctionType<'a>> {
        match self {
            TypeKind::FunctionType(ty) => Some(ty),
            TypeKind::TypeVariable(var) => var.instance().and_then(|x| x.function_type()),
            _ => None,
        }
    }

    pub fn array_type(&self) -> Option<&'a ArrayType<'a>> {
        match self {
            TypeKind::ArrayType(ty) => Some(ty),
            TypeKind::TypeVariable(var) => var.instance().and_then(|x| x.array_type()),
            _ => None,
        }
    }

    pub fn is_function_type(&self) -> bool {
        self.function_type().is_some()
    }

    pub fn is_struct_type(&self) -> bool {
        self.struct_type().is_some()
    }

    pub fn is_array_type(&self) -> bool {
        self.array_type().is_some()
    }

    pub fn unify(
        &self,
        arena: &'a BumpaloArena,
        expected_type: TypeKind<'a>,
    ) -> Result<TypeKind<'a>, TypeError<'a>> {
        debug!("[unify] {} - {}", self, expected_type);

        let ty1 = self.terminal_type();
        let ty2 = expected_type.terminal_type();
        debug!("[unify] prune: {} - {}", ty1, ty2);

        // Already unified or primitive type.
        if ty1 == ty2 {
            return Ok(ty2);
        }

        match ty1 {
            TypeKind::TypeVariable(var) => {
                return var.unify(arena, ty2);
            }
            TypeKind::ArrayType(array_type1) => {
                if let Some(array_type2) = ty2.array_type() {
                    return array_type1.unify(arena, array_type2);
                }
            }
            TypeKind::StructType(struct_type1) => {
                if let Some(struct_type2) = ty2.struct_type() {
                    return struct_type1.unify(arena, struct_type2);
                }
            }
            TypeKind::FunctionType(fun_type1) => {
                if let Some(fun_type2) = ty2.function_type() {
                    return fun_type1.unify(arena, fun_type2);
                }
            }
            _ => {}
        }

        // trying opposite side.
        if let TypeKind::TypeVariable(var2) = ty2 {
            return match var2.unify(arena, ty1) {
                // reverse operand if error occurred.
                Err(TypeError::TypeMismatchError(mismatch)) => {
                    let mismatch =
                        TypeMismatchError::new(mismatch.actual_type(), mismatch.expected_type());
                    Err(TypeError::TypeMismatchError(mismatch))
                }
                u => u,
            };
        }

        let mismatch = TypeMismatchError::new(ty2, ty1);
        Err(TypeError::TypeMismatchError(mismatch))
    }

    pub fn terminal_type(self) -> Self {
        if let TypeKind::TypeVariable(ty) = self {
            ty.terminal_type()
        } else {
            self
        }
    }

    pub fn type_specifier(&self) -> String {
        match self {
            TypeKind::StructType(ty) => ty.type_specifier(),
            TypeKind::FunctionType(ty) => ty.type_specifier(),
            TypeKind::ArrayType(ty) => ty.type_specifier(),
            TypeKind::TypeVariable(ty) => ty.type_specifier(),
            _ => self.to_string(),
        }
    }
}

impl fmt::Display for TypeKind<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeKind::Integer => write!(f, "Int"),
            TypeKind::Boolean => write!(f, "Bool"),
            TypeKind::String => write!(f, "Str"),
            TypeKind::Void => write!(f, "Void"),
            TypeKind::StructType(ty) => ty.fmt(f),
            TypeKind::FunctionType(ty) => ty.fmt(f),
            TypeKind::ArrayType(ty) => ty.fmt(f),
            TypeKind::TypeVariable(ty) => ty.fmt(f),
        }
    }
}

#[derive(Debug, Clone)]
struct TypeFieldList<'a> {
    fields: BumpaloVec<'a, &'a TypeField<'a>>,
    // stable sorted by name.
    sorted_fields: BumpaloVec<'a, &'a TypeField<'a>>,
}

impl<'a> TypeFieldList<'a> {
    pub fn new(arena: &'a BumpaloArena, field_types: &[&'a TypeField<'a>]) -> Self {
        let mut fields = BumpaloVec::with_capacity_in(field_types.len(), arena);
        let mut sorted_fields: BumpaloVec<'a, &'a TypeField<'a>> =
            BumpaloVec::with_capacity_in(field_types.len(), arena);

        fields.extend(field_types);
        sorted_fields.extend(field_types);
        sorted_fields.sort_by(|a, b| a.name().partial_cmp(b.name()).unwrap());

        Self {
            fields,
            sorted_fields,
        }
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = &'a TypeField<'a>> + '_ {
        self.fields.iter().copied()
    }

    pub fn sorted_iter(&self) -> impl ExactSizeIterator<Item = &'a TypeField<'a>> + '_ {
        self.sorted_fields.iter().copied()
    }

    pub fn get_field(&self, name: &str) -> Option<&'a TypeField<'a>> {
        self.sorted_fields
            .binary_search_by(|f| f.name().partial_cmp(name).unwrap())
            .ok()
            .map(|i| self.sorted_fields[i])
    }

    pub fn get_field_type(&self, name: &str) -> Option<TypeKind<'a>> {
        self.get_field(name).map(|f| f.r#type())
    }
}

impl PartialEq for TypeFieldList<'_> {
    fn eq(&self, other: &Self) -> bool {
        if self.fields.len() != other.fields.len() {
            return false;
        }

        self.fields
            .iter()
            .all(|f1| other.get_field(f1.name()).filter(|f2| f1 == f2).is_some())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructType<'a> {
    name: BumpaloString<'a>,
    fields: TypeFieldList<'a>,
}

impl<'a> StructType<'a> {
    pub fn new(arena: &'a BumpaloArena, name: &str, field_types: &[&'a TypeField<'a>]) -> Self {
        Self {
            name: BumpaloString::from_str_in(name, arena),
            fields: TypeFieldList::new(arena, field_types),
        }
    }

    pub fn name(&self) -> &str {
        self.name.as_str()
    }

    pub fn fields(&self) -> impl ExactSizeIterator<Item = &'a TypeField<'a>> + '_ {
        self.fields.iter()
    }

    pub fn sorted_fields(&self) -> impl ExactSizeIterator<Item = &'a TypeField<'a>> + '_ {
        self.fields.sorted_iter()
    }

    pub fn get_field_type(&self, name: &str) -> Option<TypeKind<'a>> {
        self.fields.get_field_type(name)
    }

    /// Is a type `self` assignable to `other`?
    pub fn unify(
        &'a self,
        arena: &'a BumpaloArena,
        expected_type: &'a StructType<'a>,
    ) -> Result<TypeKind<'a>, TypeError<'a>> {
        debug!("[unify:struct] {} -> {}", self, expected_type);

        // Struct follows nominal subtyping.
        if self.name() != expected_type.name() {
            let mismatch = TypeMismatchError::new(
                TypeKind::StructType(expected_type),
                TypeKind::StructType(self),
            );
            return Err(TypeError::TypeMismatchError(mismatch));
        }

        for (i, (x, y)) in self
            .sorted_fields()
            .zip(expected_type.sorted_fields())
            .enumerate()
        {
            if let Err(err) = x.unify(arena, y) {
                match err {
                    TypeError::TypeMismatchError(mismatch) => {
                        let mut fields: Vec<_> = self.fields().collect();

                        fields[i] =
                            arena.alloc(TypeField::new(arena, y.name(), mismatch.expected_type()));

                        let expected =
                            arena.alloc(StructType::new(arena, expected_type.name(), &fields));
                        let mismatch = TypeMismatchError::new(
                            TypeKind::StructType(expected),
                            TypeKind::StructType(self),
                        );

                        return Err(TypeError::TypeMismatchError(mismatch));
                    }
                }
            }
        }

        Ok(TypeKind::StructType(self))
    }

    pub fn type_specifier(&self) -> String {
        self.name().to_string()
    }
}

impl fmt::Display for StructType<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "struct {} ", self.name())?;

        let mut it = self.fields().peekable();

        write!(f, "{{")?;
        while let Some(param) = it.next() {
            write!(f, "{}", param)?;
            if it.peek().is_some() {
                write!(f, ", ")?;
            }
        }
        write!(f, "}}")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeField<'a> {
    name: BumpaloString<'a>,
    r#type: TypeKind<'a>,
}

impl<'a> TypeField<'a> {
    pub fn new(arena: &'a BumpaloArena, name: &str, r#type: TypeKind<'a>) -> Self {
        Self {
            name: BumpaloString::from_str_in(name, arena),
            r#type,
        }
    }

    pub fn name(&self) -> &str {
        self.name.as_str()
    }

    pub fn r#type(&self) -> TypeKind<'a> {
        self.r#type
    }

    pub fn unify(
        &'a self,
        arena: &'a BumpaloArena,
        other: &'a TypeField<'a>,
    ) -> Result<TypeKind<'a>, TypeError<'a>> {
        if self.name() != other.name() {
            let mismatch = TypeMismatchError::new(other.r#type(), self.r#type());
            return Err(TypeError::TypeMismatchError(mismatch));
        }

        if let Err(err) = self.r#type().unify(arena, other.r#type()) {
            match err {
                TypeError::TypeMismatchError(mismatch) => {
                    let mismatch = TypeMismatchError::new(mismatch.expected_type(), self.r#type());
                    return Err(TypeError::TypeMismatchError(mismatch));
                }
            }
        }

        Ok(other.r#type())
    }
}

impl fmt::Display for TypeField<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.name(), self.r#type())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionType<'a> {
    name: BumpaloString<'a>,
    parameters: BumpaloVec<'a, &'a FunctionParameter<'a>>,
    return_type: TypeKind<'a>,
}

impl<'a> FunctionType<'a> {
    pub fn new(
        arena: &'a BumpaloArena,
        name: &str,
        parameters: &[&'a FunctionParameter<'a>],
        return_type: TypeKind<'a>,
    ) -> Self {
        let mut params = BumpaloVec::with_capacity_in(parameters.len(), arena);

        params.extend(parameters);

        Self {
            name: BumpaloString::from_str_in(name, arena),
            parameters: params,
            return_type,
        }
    }

    pub fn name(&self) -> &str {
        self.name.as_str()
    }

    pub fn parameters(&self) -> impl ExactSizeIterator<Item = &'a FunctionParameter<'a>> + '_ {
        self.parameters.iter().copied()
    }

    pub fn return_type(&self) -> TypeKind<'a> {
        self.return_type
    }

    pub fn unify(
        &'a self,
        arena: &'a BumpaloArena,
        other: &'a FunctionType<'a>,
    ) -> Result<TypeKind<'a>, TypeError<'a>> {
        if self.name() != other.name() {
            let mismatch =
                TypeMismatchError::new(TypeKind::FunctionType(other), TypeKind::FunctionType(self));
            return Err(TypeError::TypeMismatchError(mismatch));
        }

        for (i, (x, y)) in self.parameters().zip(other.parameters()).enumerate() {
            if let Err(err) = x.unify(arena, y) {
                match err {
                    TypeError::TypeMismatchError(mismatch) => {
                        let mut params: Vec<_> = self.parameters().collect();

                        params[i] = arena.alloc(FunctionParameter::new(
                            arena,
                            y.name(),
                            mismatch.expected_type(),
                        ));

                        let expected = arena.alloc(FunctionType::new(
                            arena,
                            other.name(),
                            &params,
                            other.return_type(),
                        ));
                        let mismatch = TypeMismatchError::new(
                            TypeKind::FunctionType(expected),
                            TypeKind::FunctionType(other),
                        );

                        return Err(TypeError::TypeMismatchError(mismatch));
                    }
                }
            }
        }

        if let Err(err) = self.return_type().unify(arena, other.return_type()) {
            match err {
                TypeError::TypeMismatchError(mismatch) => {
                    let params: Vec<_> = other.parameters().collect();

                    let expected = arena.alloc(FunctionType::new(
                        arena,
                        other.name(),
                        &params,
                        mismatch.expected_type(),
                    ));
                    let mismatch = TypeMismatchError::new(
                        TypeKind::FunctionType(expected),
                        TypeKind::FunctionType(other),
                    );

                    return Err(TypeError::TypeMismatchError(mismatch));
                }
            }
        }

        Ok(TypeKind::FunctionType(self))
    }

    pub fn type_specifier(&self) -> String {
        let mut buffer = String::new();
        let mut it = self.parameters().peekable();

        buffer.push('(');
        while let Some(param) = it.next() {
            buffer.push_str(&param.to_string());
            if it.peek().is_some() {
                buffer.push_str(", ");
            }
        }

        match self.return_type().terminal_type() {
            TypeKind::Void => {}
            ty => {
                buffer.push_str(") -> ");
                buffer.push_str(&ty.type_specifier());
            }
        };

        buffer
    }
}

impl fmt::Display for FunctionType<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "fun {}", self.name())?;

        let mut it = self.parameters().peekable();

        write!(f, "(")?;
        while let Some(param) = it.next() {
            write!(f, "{}", param)?;
            if it.peek().is_some() {
                write!(f, ", ")?;
            }
        }

        match self.return_type().terminal_type() {
            TypeKind::Void => {
                write!(f, ")")
            }
            ty => {
                write!(f, ") -> {}", ty)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionParameter<'a> {
    name: BumpaloString<'a>,
    r#type: TypeKind<'a>,
}

impl<'a> FunctionParameter<'a> {
    pub fn new(arena: &'a BumpaloArena, name: &str, r#type: TypeKind<'a>) -> Self {
        Self {
            name: BumpaloString::from_str_in(name, arena),
            r#type,
        }
    }

    pub fn name(&self) -> &str {
        self.name.as_str()
    }

    pub fn r#type(&self) -> TypeKind<'a> {
        self.r#type
    }

    pub fn unify(
        &'a self,
        arena: &'a BumpaloArena,
        other: &'a FunctionParameter<'a>,
    ) -> Result<TypeKind<'a>, TypeError<'a>> {
        if self.name() != other.name() {
            let mismatch = TypeMismatchError::new(other.r#type(), self.r#type());
            return Err(TypeError::TypeMismatchError(mismatch));
        }

        if let Err(err) = self.r#type().unify(arena, other.r#type()) {
            match err {
                TypeError::TypeMismatchError(mismatch) => {
                    let mismatch = TypeMismatchError::new(mismatch.expected_type(), self.r#type());
                    return Err(TypeError::TypeMismatchError(mismatch));
                }
            }
        }

        Ok(other.r#type())
    }
}

impl fmt::Display for FunctionParameter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.name(), self.r#type().type_specifier())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ArrayType<'a> {
    element_type: TypeKind<'a>,
}

impl<'a> ArrayType<'a> {
    pub fn new(element_type: TypeKind<'a>) -> Self {
        Self { element_type }
    }

    pub fn element_type(&self) -> TypeKind<'a> {
        self.element_type
    }

    pub fn unify(
        &'a self,
        arena: &'a BumpaloArena,
        other: &'a ArrayType<'a>,
    ) -> Result<TypeKind<'a>, TypeError<'a>> {
        match self.element_type().unify(arena, other.element_type()) {
            Ok(_) => return Ok(TypeKind::ArrayType(other)),
            Err(err) => match err {
                TypeError::TypeMismatchError(mismatch) => {
                    let expected = arena.alloc(ArrayType::new(mismatch.expected_type()));
                    let mismatch = TypeMismatchError::new(
                        TypeKind::ArrayType(expected),
                        TypeKind::ArrayType(self),
                    );

                    return Err(TypeError::TypeMismatchError(mismatch));
                }
            },
        }
    }

    pub fn type_specifier(&self) -> String {
        self.to_string()
    }
}

impl fmt::Display for ArrayType<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}[]", self.element_type().type_specifier())
    }
}

/// There are three states of a type variable
///
/// 1. The initial state is where the type is not instantiated. It can be adapted to any number of constraints.
/// 2. A reference to another type variable. In this case, constraints are moved to the another reference.
/// 3. Finally, the type has been instantiated.
///
/// The states transition in the above order and do not go backwards.

#[derive(Debug, Clone, Copy)]
pub enum TypeVariableInner<'a> {
    Uninstantiated,
    Reference(&'a TypeVariable<'a>),
    Instantiated(TypeKind<'a>),
}

pub struct TypeVariable<'a> {
    label: i32,
    inner: Cell<TypeVariableInner<'a>>,
}

impl<'a> TypeVariable<'a> {
    fn new(label: i32, inner: Cell<TypeVariableInner<'a>>) -> Self {
        Self { label, inner }
    }

    pub fn uninstantiated(label: i32) -> Self {
        Self::new(label, Cell::new(TypeVariableInner::Uninstantiated))
    }

    pub fn instance(&self) -> Option<TypeKind<'a>> {
        match self.inner.get() {
            TypeVariableInner::Uninstantiated => None,
            TypeVariableInner::Reference(var) => var.instance(),
            TypeVariableInner::Instantiated(ty) => Some(ty),
        }
    }

    /// Returns the type variable or concrete type at the deepest position in type chain.
    pub fn terminal_type(&'a self) -> TypeKind<'a> {
        match self.inner.get() {
            TypeVariableInner::Uninstantiated => TypeKind::TypeVariable(self),
            TypeVariableInner::Reference(var) => var.terminal_type(),
            TypeVariableInner::Instantiated(ty) => ty,
        }
    }

    /// Prune unnecessary indirections.
    fn prune(&self) {
        if let TypeVariableInner::Reference(var) = self.inner.get() {
            let terminal_type = var.terminal_type();

            let inner = if let TypeKind::TypeVariable(v) = terminal_type {
                TypeVariableInner::Reference(v)
            } else {
                TypeVariableInner::Instantiated(terminal_type)
            };

            self.inner.replace(inner);
        }
    }

    pub fn unify(
        &'a self,
        arena: &'a BumpaloArena,
        other: TypeKind<'a>,
    ) -> Result<TypeKind<'a>, TypeError<'a>> {
        match self.inner.get() {
            TypeVariableInner::Uninstantiated => {
                // TODO: confirm interfaces?
                let inner = if let TypeKind::TypeVariable(var) = other {
                    debug!("[unify] reference: ?{} -> {}", self.label, var);
                    TypeVariableInner::Reference(var)
                } else {
                    debug!("[unify] instantiation: ?{} -> {}", self.label, other);
                    TypeVariableInner::Instantiated(other)
                };

                self.inner.replace(inner);
                Ok(TypeKind::TypeVariable(self))
            }
            TypeVariableInner::Reference(var) => var.unify(arena, other),
            TypeVariableInner::Instantiated(ty) => {
                unreachable!(
                    "A type variable ?{} is already instantiated with {}",
                    self.label, ty
                );
            }
        }
    }

    pub fn type_specifier(&self) -> String {
        // Prints the instance type if a type variable is already pruned.
        if let TypeVariableInner::Instantiated(ty) = self.inner.get() {
            ty.type_specifier()
        } else {
            self.to_string()
        }
    }
}

impl fmt::Display for TypeVariable<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Prints the instance type if a type variable is already pruned.
        if let TypeVariableInner::Instantiated(ty) = self.inner.get() {
            ty.fmt(f)
        } else {
            write!(f, "?{}", self.label)
        }
    }
}

impl fmt::Debug for TypeVariable<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        write!(f, "?{}", self.label)?;
        match self.inner.get() {
            TypeVariableInner::Uninstantiated => {
                // TODO: interfaces
            }
            TypeVariableInner::Reference(var) => {
                write!(f, " -> {:?}", var)?;
            }
            TypeVariableInner::Instantiated(ty) => {
                write!(f, " -> {}", ty)?;
            }
        };
        write!(f, ")")
    }
}

impl<'a> PartialEq for TypeVariable<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.label == other.label
    }
}

// --- Type inference visitors ---

/// A visitor assigns an initial type (type variable or primitive type) to a node
/// without unification.
#[derive(Debug)]
pub(super) struct InitialTypeBinder<'a> {
    arena: &'a BumpaloArena,
    seq: i32,
}

impl<'a> InitialTypeBinder<'a> {
    pub fn new(arena: &'a BumpaloArena) -> Self {
        Self { arena, seq: 0 }
    }

    fn new_type_var(&mut self) -> &'a TypeVariable<'a> {
        let var = TypeVariable::uninstantiated(self.seq);

        self.seq += 1;
        self.arena.alloc(var)
    }

    fn new_array_type(&mut self) -> &'a ArrayType<'a> {
        let element_type = self.new_type_var();
        let array_type = ArrayType::new(TypeKind::TypeVariable(element_type));

        self.arena.alloc(array_type)
    }

    fn build_struct_type(
        &mut self,
        definition: &'a StructDefinition<'a>,
    ) -> Option<&'a StructType<'a>> {
        let name = definition.name()?;
        let mut field_types = vec![];

        for f in definition.fields() {
            let name = f.name()?.as_str();
            let ty = f.type_annotation()?.r#type();

            let field = &*self.arena.alloc(TypeField::new(self.arena, name, ty));

            field_types.push(field);
        }

        let ty = StructType::new(self.arena, name.as_str(), &field_types);
        Some(&*self.arena.alloc(ty))
    }

    fn build_function_type(
        &mut self,
        definition: &'a FunctionDefinition<'a>,
    ) -> Option<&'a FunctionType<'a>> {
        let name = definition.name()?;
        let params: Vec<_> = definition
            .parameters()
            .map(|p| {
                &*self.arena.alloc(FunctionParameter::new(
                    self.arena,
                    p.name().as_str(),
                    p.r#type(),
                ))
            })
            .collect();

        let return_type = if let Some(return_type_annotation) = definition.return_type_annotation()
        {
            return_type_annotation.r#type()
        } else {
            TypeKind::TypeVariable(self.new_type_var())
        };

        let ty = FunctionType::new(self.arena, name.as_str(), &params, return_type);
        Some(&*self.arena.alloc(ty))
    }

    fn build_struct_literal_type(
        &mut self,
        literal: &'a StructLiteral<'a>,
    ) -> Option<&'a StructType<'a>> {
        let name = literal.name();
        let mut field_types = vec![];

        for f in literal.fields() {
            let name = f.name().as_str();

            let field = &*self
                .arena
                .alloc(TypeField::new(self.arena, name, f.r#type()));

            field_types.push(field);
        }

        let ty = StructType::new(self.arena, name.as_str(), &field_types);
        Some(&*self.arena.alloc(ty))
    }
}

impl<'a> Visitor<'a> for InitialTypeBinder<'a> {
    fn exit_struct_definition(
        &mut self,
        _path: &'a NodePath<'a>,
        definition: &'a StructDefinition<'a>,
    ) {
        if let Some(ty) = self.build_struct_type(definition) {
            definition.assign_type(TypeKind::StructType(ty))
        } else {
            definition.assign_type(TypeKind::TypeVariable(self.new_type_var()))
        }
    }

    fn exit_function_definition(
        &mut self,
        _path: &'a NodePath<'a>,
        definition: &'a FunctionDefinition<'a>,
    ) {
        if let Some(ty) = self.build_function_type(definition) {
            definition.assign_type(TypeKind::FunctionType(ty))
        } else {
            definition.assign_type(TypeKind::TypeVariable(self.new_type_var()))
        }
    }

    fn exit_type_annotation(
        &mut self,
        _path: &'a NodePath<'a>,
        annotation: &'a TypeAnnotation<'a>,
    ) {
        // placeholder
        annotation.assign_type(TypeKind::TypeVariable(self.new_type_var()));
    }

    fn exit_function_parameter(
        &mut self,
        _path: &'a NodePath<'a>,
        _fun: &'a FunctionDefinition<'a>,
        param: &'a syntax::FunctionParameter<'a>,
    ) {
        if let Some(annotation) = param.type_annotation() {
            param.assign_type(annotation.r#type())
        } else {
            param.assign_type(TypeKind::TypeVariable(self.new_type_var()))
        }
    }

    fn exit_struct_literal(&mut self, _path: &'a NodePath<'a>, literal: &'a StructLiteral<'a>) {
        if let Some(ty) = self.build_struct_literal_type(literal) {
            literal.assign_type(TypeKind::StructType(ty))
        } else {
            literal.assign_type(TypeKind::TypeVariable(self.new_type_var()))
        }
    }

    fn exit_value_field(
        &mut self,
        _path: &'a NodePath<'a>,
        _struct_literal: &'a StructLiteral<'a>,
        field: &'a ValueField<'a>,
    ) {
        if let Some(expr) = field.value() {
            field.assign_type(expr.r#type());
        } else {
            field.assign_type(TypeKind::TypeVariable(self.new_type_var()));
        }
    }

    fn exit_binary_expression(&mut self, _path: &'a NodePath<'a>, expr: &'a BinaryExpression<'a>) {
        expr.assign_type(TypeKind::TypeVariable(self.new_type_var()));
    }

    fn exit_unary_expression(&mut self, _path: &'a NodePath<'a>, expr: &'a UnaryExpression<'a>) {
        expr.assign_type(TypeKind::TypeVariable(self.new_type_var()));
    }

    fn exit_array_expression(&mut self, _path: &'a NodePath<'a>, expr: &'a ArrayExpression<'a>) {
        expr.assign_type(TypeKind::ArrayType(self.new_array_type()));
    }

    fn exit_block(&mut self, _path: &'a NodePath<'a>, block: &'a syntax::Block<'a>) {
        // The type of a block is actually the return type of the last expression that
        // occurs in the body.
        if let Some(expr) = block.last_expression() {
            block.assign_type(expr.r#type());
        } else {
            // Otherwise, the type of a block is `void`
            block.assign_type(TypeKind::Void);
        }
    }

    fn exit_call_expression(&mut self, _path: &'a NodePath<'a>, expr: &'a CallExpression<'a>) {
        expr.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_subscript_expression(
        &mut self,
        _path: &'a NodePath<'a>,
        expr: &'a SubscriptExpression<'a>,
    ) {
        expr.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_member_expression(&mut self, _path: &'a NodePath<'a>, expr: &'a MemberExpression<'a>) {
        expr.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_case_expression(&mut self, _path: &'a NodePath<'a>, expr: &'a CaseExpression<'a>) {
        expr.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_if_expression(&mut self, _path: &'a NodePath<'a>, expr: &'a IfExpression<'a>) {
        expr.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_variable_expression(
        &mut self,
        _path: &'a NodePath<'a>,
        expr: &'a VariableExpression<'a>,
    ) {
        expr.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_grouped_expression(
        &mut self,
        _path: &'a NodePath<'a>,
        expr: &'a GroupedExpression<'a>,
    ) {
        expr.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_variable_pattern(&mut self, _path: &'a NodePath<'a>, pattern: &'a VariablePattern<'a>) {
        pattern.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_array_pattern(
        &mut self,
        _path: &'a NodePath<'a>,
        pattern: &'a syntax::ArrayPattern<'a>,
    ) {
        pattern.assign_type(TypeKind::ArrayType(self.new_array_type()));
    }

    fn exit_rest_pattern(&mut self, _path: &'a NodePath<'a>, pattern: &'a syntax::RestPattern<'a>) {
        pattern.assign_type(TypeKind::ArrayType(self.new_array_type()));
    }

    fn exit_struct_pattern(
        &mut self,
        _path: &'a NodePath<'a>,
        pattern: &'a syntax::StructPattern<'a>,
    ) {
        pattern.assign_type(TypeKind::TypeVariable(self.new_type_var()));
    }
}

#[derive(Debug)]
pub(super) struct TypeQualifierResolver<'a> {
    arena: &'a BumpaloArena,
}

impl<'a> TypeQualifierResolver<'a> {
    pub fn new(arena: &'a BumpaloArena) -> Self {
        Self { arena }
    }

    fn resolve_type_qualifier(
        &self,
        scope: &Scope<'a>,
        annotation_kind: &TypeAnnotationKind<'a>,
    ) -> Result<TypeKind<'a>, String> {
        let ty = match annotation_kind {
            syntax::TypeAnnotationKind::Int => TypeKind::Integer,
            syntax::TypeAnnotationKind::Bool => TypeKind::Boolean,
            syntax::TypeAnnotationKind::Identifier(type_name) => {
                let binding = match scope.get_binding(type_name.as_str()) {
                    None => {
                        return Err(type_name.to_string());
                    }
                    Some(binding) => binding,
                };

                if !binding.is_defined_struct() {
                    return Err(type_name.to_string());
                }

                binding.r#type()
            }
            syntax::TypeAnnotationKind::ArrayType(element_kind) => {
                let element_type = self.resolve_type_qualifier(scope, element_kind)?;
                let array_type = ArrayType::new(element_type);

                TypeKind::ArrayType(self.arena.alloc(array_type))
            }
        };

        Ok(ty)
    }
}

impl<'a> Visitor<'a> for TypeQualifierResolver<'a> {
    fn exit_type_annotation(&mut self, path: &'a NodePath<'a>, annotation: &'a TypeAnnotation<'a>) {
        match self.resolve_type_qualifier(path.scope(), annotation.kind()) {
            Ok(ty) => {
                // We have to unify the previously assigned type variable and the concrete type.
                annotation
                    .r#type()
                    .unify(self.arena, ty)
                    .unwrap_or_else(|err| panic!("Type error: {}", err));
            }
            Err(name) => {
                annotation
                    .errors()
                    .push_semantic_error(SemanticError::UndefinedType(name));
            }
        };
    }
}

#[derive(Debug)]
struct BinaryOperatorType<'a> {
    lhs: TypeKind<'a>,
    rhs: TypeKind<'a>,
    result_type: TypeKind<'a>,
}

impl<'a> From<BinaryOperator> for BinaryOperatorType<'a> {
    fn from(op: BinaryOperator) -> Self {
        match op {
            BinaryOperator::Add
            | BinaryOperator::Sub
            | BinaryOperator::Mul
            | BinaryOperator::Div
            | BinaryOperator::Rem => Self {
                lhs: TypeKind::Integer,
                rhs: TypeKind::Integer,
                result_type: TypeKind::Integer,
            },
            BinaryOperator::Lt
            | BinaryOperator::Gt
            | BinaryOperator::Le
            | BinaryOperator::Ge
            | BinaryOperator::Eq
            | BinaryOperator::Ne => Self {
                lhs: TypeKind::Integer,
                rhs: TypeKind::Integer,
                result_type: TypeKind::Boolean,
            },
            BinaryOperator::And | BinaryOperator::Or => Self {
                lhs: TypeKind::Boolean,
                rhs: TypeKind::Boolean,
                result_type: TypeKind::Boolean,
            },
        }
    }
}

#[derive(Debug)]
struct UnaryOperatorType<'a> {
    operand: TypeKind<'a>,
    result_type: TypeKind<'a>,
}

impl<'a> From<UnaryOperator> for UnaryOperatorType<'a> {
    fn from(op: UnaryOperator) -> Self {
        match op {
            UnaryOperator::Plus | UnaryOperator::Minus => Self {
                operand: TypeKind::Integer,
                result_type: TypeKind::Integer,
            },
            UnaryOperator::Not => Self {
                operand: TypeKind::Boolean,
                result_type: TypeKind::Boolean,
            },
        }
    }
}

#[derive(Debug)]
pub(super) struct TypeInferencer<'a> {
    arena: &'a BumpaloArena,
}

impl<'a> TypeInferencer<'a> {
    pub fn new(arena: &'a BumpaloArena) -> Self {
        Self { arena }
    }
}

impl<'a> Visitor<'a> for TypeInferencer<'a> {
    fn exit_function_definition(
        &mut self,
        _path: &'a NodePath<'a>,
        function: &'a FunctionDefinition<'a>,
    ) {
        let function_type = unwrap_or_return!(function.function_type());
        let return_type = function_type.return_type();
        let body_type = function.body().r#type();

        // If an explicit type is specified for the return type,
        // the type of function body must be compatible.
        debug!(
            "[inference] return_type: {}, body: {} in function {}",
            return_type, body_type, function
        );

        let err = if let TypeKind::TypeVariable(_) = return_type {
            body_type.unify(self.arena, return_type)
        } else {
            return_type.unify(self.arena, body_type)
        };

        if let Err(err) = err {
            if let Some(expr) = function.body().last_expression() {
                expr.errors()
                    .push_semantic_error(SemanticError::TypeError(err));
            } else {
                function
                    .body()
                    .errors()
                    .push_semantic_error(SemanticError::TypeError(err));
            }
        }
    }

    fn exit_struct_literal(&mut self, path: &'a NodePath<'a>, literal: &'a StructLiteral<'a>) {
        let binding = unwrap_or_return!(path.scope().get_binding(literal.name().as_str()));
        let struct_type = unwrap_or_return!(binding.r#type().struct_type());

        debug!("[inference] struct literal: {}", literal);

        if let Err(err) = literal
            .r#type()
            .unify(self.arena, TypeKind::StructType(struct_type))
        {
            literal
                .errors()
                .push_semantic_error(SemanticError::TypeError(err));
        }
    }

    fn exit_member_expression(
        &mut self,
        _path: &'a NodePath<'a>,
        member_expr: &'a MemberExpression<'a>,
    ) {
        let field = unwrap_or_return!(member_expr.field());
        let object = member_expr.object();
        let object_type = object.r#type();

        if let Some(struct_type) = object_type.struct_type() {
            if let Some(field_type) = struct_type.get_field_type(field.as_str()) {
                if let Err(err) = member_expr.r#type().unify(self.arena, field_type) {
                    member_expr
                        .errors()
                        .push_semantic_error(SemanticError::TypeError(err));
                }

                return;
            }
        }

        object
            .errors()
            .push_semantic_error(SemanticError::FieldDoesNotExist {
                r#type: object_type,
                field: field.to_string(),
            });
    }

    fn exit_array_expression(&mut self, _path: &'a NodePath<'a>, expr: &'a ArrayExpression<'a>) {
        let array_type = expr
            .r#type()
            .array_type()
            .expect("The type of an array expression must be array type.");

        for element in expr.elements() {
            if let Err(err) = element
                .r#type()
                .unify(self.arena, array_type.element_type())
            {
                element
                    .errors()
                    .push_semantic_error(SemanticError::TypeError(err));
            }
        }
    }

    fn exit_binary_expression(&mut self, _path: &'a NodePath<'a>, expr: &'a BinaryExpression<'a>) {
        let lhs = expr.lhs();
        let rhs = unwrap_or_return!(expr.rhs());
        let operator = expr.operator();
        let op_type = BinaryOperatorType::from(operator);

        debug!("[inference] binary_expression ({}) lhs: {}", operator, lhs);
        if let Err(err) = lhs.r#type().unify(self.arena, op_type.lhs) {
            lhs.errors()
                .push_semantic_error(SemanticError::TypeError(err));
        }

        debug!("[inference] binary_expression ({}) rhs: {}", operator, rhs);
        if let Err(err) = rhs.r#type().unify(self.arena, op_type.rhs) {
            rhs.errors()
                .push_semantic_error(SemanticError::TypeError(err));
        }

        debug!("[inference] binary_expression ({}) - {}", operator, expr);
        if let Err(err) = expr.r#type().unify(self.arena, op_type.result_type) {
            expr.errors()
                .push_semantic_error(SemanticError::TypeError(err));
        }
    }

    fn exit_unary_expression(&mut self, _path: &'a NodePath<'a>, expr: &'a UnaryExpression<'a>) {
        let operand = unwrap_or_return!(expr.operand());
        let operator = expr.operator();
        let op_type = UnaryOperatorType::from(operator);

        debug!(
            "[inference] unary_expression ({}) operand: {}",
            operator, operand
        );
        if let Err(err) = operand.r#type().unify(self.arena, op_type.operand) {
            operand
                .errors()
                .push_semantic_error(SemanticError::TypeError(err));
        }

        debug!("[inference] unary_expression ({}) - {}", operator, expr);
        if let Err(err) = expr.r#type().unify(self.arena, op_type.result_type) {
            expr.errors()
                .push_semantic_error(SemanticError::TypeError(err));
        }
    }

    fn exit_grouped_expression(
        &mut self,
        _path: &'a NodePath<'a>,
        grouped_expr: &'a GroupedExpression<'a>,
    ) {
        if let Some(expr) = grouped_expr.expression() {
            debug!("[inference] grouped_expression: {}, {}", grouped_expr, expr);
            grouped_expr
                .r#type()
                .unify(self.arena, expr.r#type())
                .unwrap_or_else(|err| panic!("Unexpected type error: {}", err));
        }
    }

    fn exit_if_expression(&mut self, _path: &'a NodePath<'a>, if_expr: &'a IfExpression<'a>) {
        // The type of `then_body` and `else_body` must be same.
        // If `else_body` is omitted, the type of `if` is `void`.
        let then_body = if_expr.then_body();

        let ty = if let Some(else_body) = if_expr.else_body() {
            debug!(
                "[inference] if_expression (body): {}, {}",
                then_body, else_body
            );
            then_body
                .r#type()
                .unify(self.arena, else_body.r#type())
                .unwrap_or_else(|err| panic!("Type error: {}", err));

            then_body.r#type()
        } else {
            TypeKind::Void
        };

        debug!("[inference] if_expression: {}", if_expr);
        if_expr
            .r#type()
            .unify(self.arena, ty)
            .unwrap_or_else(|err| panic!("Type error: {}", err));
    }

    fn exit_case_expression(&mut self, _path: &'a NodePath<'a>, case_expr: &'a CaseExpression<'a>) {
        // -- All arm pattern types must be same as the type of head expression.
        if let Some(head_expr) = case_expr.head() {
            for (i, arm) in case_expr.arms().enumerate() {
                debug!("[inference] head {} <- arm #{} ", head_expr, i);

                if let Some(pattern) = arm.pattern() {
                    if let Err(err) = pattern.r#type().unify(self.arena, head_expr.r#type()) {
                        arm.errors()
                            .push_semantic_error(SemanticError::TypeError(err));
                    }
                }
            }
        }

        // -- Infer the return type of a case expression

        // - All arms must have same type.
        let accumulated = case_expr.arms().enumerate().reduce(|(i, a), (j, b)| {
            debug!("[inference] case_expression: arm #{} - #{}", i, j);
            if let Err(err) = b.r#type().unify(self.arena, a.r#type()) {
                b.errors()
                    .push_semantic_error(SemanticError::TypeError(err));
            }

            (j, b)
        });

        // - An empty case expression's type is `void`.
        if let Some((i, arm)) = accumulated {
            debug!("[inference] case_expression <- arm #{} ", i);
            if let Err(err) = case_expr.r#type().unify(self.arena, arm.r#type()) {
                case_expr
                    .errors()
                    .push_semantic_error(SemanticError::TypeError(err));
            }
        } else {
            debug!("[inference] case_expression <- void");
            case_expr.assign_type(TypeKind::Void);
        }
    }

    fn exit_call_expression(&mut self, _path: &'a NodePath<'a>, call_expr: &'a CallExpression<'a>) {
        let callee_type = call_expr.callee().r#type();

        let function_type = if let Some(function_type) = callee_type.function_type() {
            function_type
        } else {
            call_expr
                .errors()
                .push_semantic_error(SemanticError::CalleeIsNotCallable { callee_type });
            return;
        };

        // return type
        debug!(
            "[inference] call_expression: {}, {}",
            call_expr,
            call_expr.callee()
        );
        call_expr
            .r#type()
            .unify(self.arena, function_type.return_type())
            .unwrap_or_else(|err| panic!("Type error: {}", err));

        // arguments
        let parameters = function_type.parameters();
        let arguments = call_expr.arguments();

        if parameters.len() != arguments.len() {
            call_expr
                .errors()
                .push_semantic_error(SemanticError::ArgumentCountMismatch {
                    expected: parameters.len(),
                    found: arguments.len(),
                });
        }

        parameters
            .zip(arguments)
            .enumerate()
            .for_each(|(i, (param, arg))| {
                debug!(
                    "[inference] call_expression (arg #{}): {}, {}",
                    i, param, arg
                );
                if let Err(err) = arg.r#type().unify(self.arena, param.r#type()) {
                    arg.errors()
                        .push_semantic_error(SemanticError::TypeError(err));
                }
            })
    }

    fn exit_subscript_expression(
        &mut self,
        _path: &'a NodePath<'a>,
        subscript_expr: &'a SubscriptExpression<'a>,
    ) {
        let callee_type = subscript_expr.callee().r#type();

        let array_type = if let Some(array_type) = callee_type.array_type() {
            array_type
        } else {
            subscript_expr
                .errors()
                .push_semantic_error(SemanticError::CalleeIsNotSubscriptable { callee_type });
            return;
        };

        // element type
        debug!(
            "[inference] subscript_expression: {}, {}",
            subscript_expr,
            subscript_expr.callee()
        );

        if let Err(err) = subscript_expr
            .r#type()
            .unify(self.arena, array_type.element_type())
        {
            subscript_expr
                .errors()
                .push_semantic_error(SemanticError::TypeError(err));
        }
    }

    // --- patterns: infer types top-down
    fn enter_array_pattern(
        &mut self,
        _path: &'a NodePath<'a>,
        pattern: &'a syntax::ArrayPattern<'a>,
    ) {
        let array_type = pattern
            .r#type()
            .array_type()
            .expect("The type of an array pattern must be an array type.");

        debug!("[inference] array pattern: {}", pattern);

        for (i, element) in pattern.elements().enumerate() {
            debug!("[inference] #{} of array pattern: {}", i, element);

            if element.rest_pattern().is_some() {
                if let Err(err) = element.r#type().unify(self.arena, pattern.r#type()) {
                    element
                        .errors()
                        .push_semantic_error(SemanticError::TypeError(err));
                }
            } else if let Err(err) = element
                .r#type()
                .unify(self.arena, array_type.element_type())
            {
                element
                    .errors()
                    .push_semantic_error(SemanticError::TypeError(err));
            }
        }
    }

    fn enter_struct_pattern(
        &mut self,
        path: &'a NodePath<'a>,
        pattern: &'a syntax::StructPattern<'a>,
    ) {
        let binding = unwrap_or_return!(path.scope().get_binding(pattern.name().as_str()));
        let struct_type = unwrap_or_return!(binding.r#type().struct_type());

        // Struct pattern type
        debug!("[inference] struct pattern: {}", pattern);

        if let Err(err) = pattern
            .r#type()
            .unify(self.arena, TypeKind::StructType(struct_type))
        {
            pattern
                .errors()
                .push_semantic_error(SemanticError::TypeError(err));
        }

        // Struct pattern fields type
        for field in pattern.fields() {
            if let Some(field_type) = struct_type.get_field_type(field.name().as_str()) {
                if let Err(err) = field.r#type().unify(self.arena, field_type) {
                    field
                        .errors()
                        .push_semantic_error(SemanticError::TypeError(err));
                }
            } else {
                field
                    .name()
                    .errors()
                    .push_semantic_error(SemanticError::FieldDoesNotExist {
                        r#type: TypeKind::StructType(struct_type),
                        field: field.name().to_string(),
                    });
            }
        }
    }

    fn enter_variable_declaration(
        &mut self,
        _path: &'a NodePath<'a>,
        declaration: &'a VariableDeclaration<'a>,
    ) {
        let pattern = unwrap_or_return!(declaration.pattern());
        let init = unwrap_or_return!(declaration.init());

        if let PatternKind::VariablePattern(var_pattern) = pattern.kind() {
            debug!(
                "[inference] variable_declaration: {}, {}",
                var_pattern, init
            );

            var_pattern
                .r#type()
                .unify(self.arena, init.r#type())
                .unwrap_or_else(|err| panic!("Type error: {}", err));
        } else {
            todo!("warn: except for variable pattern, we can't infer type.");
        }
    }

    fn enter_variable_expression(
        &mut self,
        path: &'a NodePath<'a>,
        expr: &'a VariableExpression<'a>,
    ) {
        let binding = unwrap_or_return!(path.scope().get_binding(expr.name()));

        debug!("[inference] variable_expression: {}, {}", expr, binding);
        expr.r#type()
            .unify(self.arena, binding.r#type())
            .unwrap_or_else(|err| panic!("Type error: {}", err));
    }
}

/// Indirect references by type variables are still necessary after type inference is complete.
/// However, unnecessary indirect references can be removed.
/// Furthermore, raise error if there are any type variables still left at the leaf node.
#[derive(Debug)]
pub(super) struct TypeVariablePruner<'a> {
    arena: &'a BumpaloArena,
}

impl<'a> TypeVariablePruner<'a> {
    pub fn new(arena: &'a BumpaloArena) -> Self {
        Self { arena }
    }

    fn prune(&self, ty: TypeKind<'a>) {
        match ty {
            TypeKind::Integer => {}
            TypeKind::Boolean => {}
            TypeKind::String => {}
            TypeKind::Void => {}
            TypeKind::StructType(ty) => {
                for f in ty.fields() {
                    self.prune(f.r#type());
                }
            }
            TypeKind::FunctionType(ty) => {
                self.prune(ty.return_type());
                for p in ty.parameters() {
                    self.prune(p.r#type());
                }
            }
            TypeKind::ArrayType(ty) => {
                self.prune(ty.element_type());
            }
            TypeKind::TypeVariable(var) => {
                var.prune();
            }
        };
    }

    fn does_type_contains_type_variable(&self, r#type: TypeKind<'a>) -> bool {
        match r#type.terminal_type() {
            TypeKind::Integer => false,
            TypeKind::Boolean => false,
            TypeKind::String => false,
            TypeKind::Void => false,
            TypeKind::StructType(ty) => ty
                .fields()
                .any(|f| self.does_type_contains_type_variable(f.r#type())),
            TypeKind::FunctionType(ty) => {
                ty.parameters()
                    .any(|p| self.does_type_contains_type_variable(p.r#type()))
                    || self.does_type_contains_type_variable(ty.return_type())
            }
            TypeKind::ArrayType(ty) => self.does_type_contains_type_variable(ty.element_type),
            TypeKind::TypeVariable(_) => true,
        }
    }

    fn type_should_be_instantiated(&self, node: NodeKind<'a>, r#type: TypeKind<'a>) {
        if self.does_type_contains_type_variable(r#type) {
            node.errors()
                .push_semantic_error(SemanticError::CannotInferType { node, r#type })
        }
    }
}

impl<'a> Visitor<'a> for TypeVariablePruner<'a> {
    fn exit_function_definition(
        &mut self,
        _path: &'a NodePath<'a>,
        definition: &'a FunctionDefinition<'a>,
    ) {
        self.prune(definition.r#type());
        self.type_should_be_instantiated(
            NodeKind::FunctionDefinition(definition),
            definition.r#type(),
        );
    }

    fn exit_function_parameter(
        &mut self,
        _path: &'a NodePath<'a>,
        _function: &'a FunctionDefinition<'a>,
        param: &'a syntax::FunctionParameter<'a>,
    ) {
        self.prune(param.r#type());
        self.type_should_be_instantiated(NodeKind::FunctionParameter(param), param.r#type());
    }

    fn exit_expression(&mut self, _path: &'a NodePath<'a>, expression: &'a syntax::Expression<'a>) {
        self.prune(expression.r#type());
        self.type_should_be_instantiated(NodeKind::Expression(expression), expression.r#type());
    }

    fn exit_pattern(&mut self, _path: &'a NodePath<'a>, pattern: &'a syntax::Pattern<'a>) {
        self.prune(pattern.r#type());
        self.type_should_be_instantiated(NodeKind::Pattern(pattern), pattern.r#type());
    }
}
