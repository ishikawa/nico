use crate::arena::BumpaloArena;
use crate::arena::{BumpaloString, BumpaloVec};
use crate::syntax::{
    self, ArrayExpression, BinaryExpression, CallExpression, CaseExpression, FunctionDefinition,
    GroupedExpression, IfExpression, MemberExpression, NodePath, PatternKind, StructDefinition,
    StructLiteral, SubscriptExpression, UnaryExpression, ValueField, VariableDeclaration,
    VariableExpression, VariablePattern, Visitor,
};
use crate::unwrap_or_return;
use log::debug;
use std::cell::Cell;
use std::fmt::Display;

pub trait Type {
    /// Returns a string which depicts type specification.
    /// e.g. i32, Rectangle, String[]
    fn type_specifier(&self) -> String;
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TypeError<'a> {
    TypeMismatchError(TypeMismatchError<'a>),
}

impl Display for TypeError<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self::TypeMismatchError(err) = self;
        err.fmt(f)
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct TypeMismatchError<'a> {
    expected_type: TypeKind<'a>,
    actual_type: TypeKind<'a>,
}

impl<'a> TypeMismatchError<'a> {
    pub fn new(expected_type: TypeKind<'a>, actual_type: TypeKind<'a>) -> Self {
        Self {
            expected_type,
            actual_type,
        }
    }

    pub fn expected_type(&self) -> TypeKind<'a> {
        self.expected_type
    }

    pub fn actual_type(&self) -> TypeKind<'a> {
        self.actual_type
    }
}

impl Display for TypeMismatchError<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "mismatched types")?;
        write!(f, "expected ")?;
        writeln!(f, "`{}`", self.expected_type())?;
        write!(f, "   found ")?;
        write!(f, "`{}`", self.actual_type())
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TypeKind<'a> {
    Int32,
    Boolean,
    String,
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

    pub fn type_variable(&self) -> Option<&'a TypeVariable<'a>> {
        if let TypeKind::TypeVariable(ty) = self {
            Some(ty)
        } else {
            None
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

    pub fn prune(self) -> Self {
        if let TypeKind::TypeVariable(ty) = self {
            if let Some(instance) = ty.instance() {
                instance.prune()
            } else {
                Self::TypeVariable(ty)
            }
        } else {
            self
        }
    }

    pub fn unify(
        &self,
        arena: &'a BumpaloArena,
        other: TypeKind<'a>,
    ) -> Result<TypeKind<'a>, TypeError<'a>> {
        debug!("[unify] {} - {}", self, other);

        let ty1 = self.prune();
        let ty2 = other.prune();
        debug!("[unify] prune: {} - {}", ty1, ty2);

        // Already unified.
        if ty1 == ty2 {
            return Ok(ty2);
        }

        match ty1 {
            TypeKind::TypeVariable(var) => {
                // `ty1` was pruned, so its instance must be `None`
                assert!(var.instance().is_none());
                if ty1 != ty2 {
                    var.replace_instance(ty2);
                }

                return Ok(ty2);
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
            _ => {
                if let TypeKind::TypeVariable(_) = ty2 {
                    // trying opposite side.
                    return ty2.unify(arena, ty1);
                }
            }
        }

        let mismatch = TypeMismatchError::new(ty2, ty1);
        Err(TypeError::TypeMismatchError(mismatch))
    }
}

impl Display for TypeKind<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeKind::Int32 => write!(f, "i32"),
            TypeKind::Boolean => write!(f, "bool"),
            TypeKind::String => write!(f, "str"),
            TypeKind::StructType(ty) => ty.fmt(f),
            TypeKind::FunctionType(ty) => ty.fmt(f),
            TypeKind::ArrayType(ty) => ty.fmt(f),
            TypeKind::TypeVariable(ty) => ty.fmt(f),
        }
    }
}

impl Type for TypeKind<'_> {
    fn type_specifier(&self) -> String {
        match self {
            TypeKind::StructType(ty) => ty.type_specifier(),
            TypeKind::FunctionType(ty) => ty.type_specifier(),
            TypeKind::ArrayType(ty) => ty.type_specifier(),
            TypeKind::TypeVariable(ty) => ty.type_specifier(),
            _ => self.to_string(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructType<'a> {
    name: BumpaloString<'a>,
    fields: BumpaloVec<'a, &'a StructField<'a>>,
}

impl<'a> StructType<'a> {
    pub fn new(arena: &'a BumpaloArena, name: &str, field_types: &[&'a StructField<'a>]) -> Self {
        let mut fields = BumpaloVec::with_capacity_in(field_types.len(), arena);

        fields.extend(field_types);

        Self {
            name: BumpaloString::from_str_in(name, arena),
            fields,
        }
    }

    pub fn name(&self) -> &str {
        self.name.as_str()
    }

    pub fn fields(&self) -> impl ExactSizeIterator<Item = &'a StructField<'a>> + '_ {
        self.fields.iter().copied()
    }

    pub fn get_field_type(&self, name: &str) -> Option<TypeKind<'a>> {
        self.fields
            .iter()
            .find(|f| f.name() == name)
            .map(|f| f.r#type())
    }

    pub fn unify(
        &'a self,
        arena: &'a BumpaloArena,
        other: &'a StructType<'a>,
    ) -> Result<TypeKind<'a>, TypeError<'a>> {
        if self.name() != other.name() {
            let mismatch =
                TypeMismatchError::new(TypeKind::StructType(other), TypeKind::StructType(self));
            return Err(TypeError::TypeMismatchError(mismatch));
        }

        for (i, (x, y)) in self.fields().zip(other.fields()).enumerate() {
            if let Err(err) = x.unify(arena, y) {
                match err {
                    TypeError::TypeMismatchError(mismatch) => {
                        let mut fields: Vec<_> = self.fields().collect();

                        fields[i] = arena.alloc(StructField::new(
                            arena,
                            y.name(),
                            mismatch.expected_type(),
                        ));

                        let expected = arena.alloc(StructType::new(arena, other.name(), &fields));
                        let mismatch = TypeMismatchError::new(
                            TypeKind::StructType(expected),
                            TypeKind::StructType(other),
                        );

                        return Err(TypeError::TypeMismatchError(mismatch));
                    }
                }
            }
        }

        Ok(TypeKind::StructType(self))
    }
}

impl Display for StructType<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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

impl Type for StructType<'_> {
    fn type_specifier(&self) -> String {
        self.name().to_string()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructField<'a> {
    name: BumpaloString<'a>,
    r#type: TypeKind<'a>,
}

impl<'a> StructField<'a> {
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
        other: &'a StructField<'a>,
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

impl Display for StructField<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
}

impl Display for FunctionType<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ", self.name())?;

        let mut it = self.parameters().peekable();

        write!(f, "(")?;
        while let Some(param) = it.next() {
            write!(f, "{}", param)?;
            if it.peek().is_some() {
                write!(f, ", ")?;
            }
        }
        write!(f, ") -> {}", self.return_type())
    }
}

impl Type for FunctionType<'_> {
    fn type_specifier(&self) -> String {
        let mut buffer = String::new();
        let mut it = self.parameters().peekable();

        buffer.push('(');
        while let Some(param) = it.next() {
            buffer.push_str(&param.to_string());
            if it.peek().is_some() {
                buffer.push_str(", ");
            }
        }
        buffer.push_str(") -> ");
        buffer.push_str(&self.return_type().type_specifier());

        buffer
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

impl Display for FunctionParameter<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
}

impl Display for ArrayType<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}[]", self.element_type().type_specifier())
    }
}

impl Type for ArrayType<'_> {
    fn type_specifier(&self) -> String {
        self.to_string()
    }
}

#[derive(Debug)]
pub struct TypeVariable<'a> {
    label: i32,
    inner: Cell<Option<TypeKind<'a>>>,
}

impl<'a> TypeVariable<'a> {
    pub fn new(label: i32) -> Self {
        Self {
            label,
            inner: Cell::default(),
        }
    }

    pub fn instance(&self) -> Option<TypeKind<'a>> {
        if let Some(inner) = self.inner.get() {
            match inner {
                TypeKind::TypeVariable(var) => var.instance(),
                ty => Some(ty),
            }
        } else {
            None
        }
    }

    pub fn prune(&self) -> &Self {
        let pruned = if let Some(TypeKind::TypeVariable(var)) = self.inner.get() {
            var.prune()
        } else {
            return self;
        };

        // Prune intermediate type variables.
        self.inner.replace(Some(TypeKind::TypeVariable(pruned)));
        pruned
    }

    pub fn replace_instance(&self, ty: TypeKind<'a>) {
        self.inner.replace(Some(ty));
    }
}

impl Display for TypeVariable<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "?{}", self.label)
    }
}

impl Type for TypeVariable<'_> {
    fn type_specifier(&self) -> String {
        self.to_string()
    }
}

impl<'a> PartialEq for TypeVariable<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.label == other.label
    }
}

// --- Type inference visitors ---

/// A visitor assigns an initial type (type variable or primitive type) to a node.
#[derive(Debug)]
pub(super) struct InitialTypeBinder<'a> {
    arena: &'a BumpaloArena,
    seq: i32,
}

impl<'a> InitialTypeBinder<'a> {
    pub fn new(arena: &'a BumpaloArena) -> Self {
        Self { arena, seq: 0 }
    }

    pub fn new_type_var(&mut self) -> &'a TypeVariable<'a> {
        let var = TypeVariable::new(self.seq);

        self.seq += 1;
        self.arena.alloc(var)
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

            let field = &*self.arena.alloc(StructField::new(self.arena, name, ty));

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

        let ty = FunctionType::new(
            self.arena,
            name.as_str(),
            &params,
            TypeKind::TypeVariable(self.new_type_var()),
        );

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
        }
    }

    fn exit_function_definition(
        &mut self,
        _path: &'a NodePath<'a>,
        definition: &'a FunctionDefinition<'a>,
    ) {
        if let Some(ty) = self.build_function_type(definition) {
            definition.assign_type(TypeKind::FunctionType(ty))
        }
    }

    fn exit_function_parameter(
        &mut self,
        _path: &'a NodePath<'a>,
        _fun: &'a FunctionDefinition<'a>,
        param: &'a syntax::FunctionParameter<'a>,
    ) {
        param.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_struct_literal(&mut self, _path: &'a NodePath<'a>, expr: &'a StructLiteral<'a>) {
        expr.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_value_field(
        &mut self,
        _path: &'a NodePath<'a>,
        _struct_literal: &'a StructLiteral<'a>,
        field: &'a ValueField<'a>,
    ) {
        field.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_binary_expression(&mut self, _path: &'a NodePath<'a>, expr: &'a BinaryExpression<'a>) {
        expr.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_unary_expression(&mut self, _path: &'a NodePath<'a>, expr: &'a UnaryExpression<'a>) {
        expr.assign_type(TypeKind::TypeVariable(self.new_type_var()))
    }

    fn exit_array_expression(&mut self, _path: &'a NodePath<'a>, expr: &'a ArrayExpression<'a>) {
        expr.assign_type(TypeKind::TypeVariable(self.new_type_var()))
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
    fn exit_struct_literal(&mut self, path: &'a NodePath<'a>, literal: &'a StructLiteral<'a>) {
        let binding = match path.scope().get_binding(literal.name().as_str()) {
            Some(binding) => binding,
            None => return,
        };

        let struct_def = match binding.struct_definition() {
            Some(struct_def) => struct_def,
            None => return,
        };

        literal
            .r#type()
            .unify(self.arena, struct_def.r#type())
            .unwrap_or_else(|err| panic!("Type error: {}", err));
    }

    fn exit_variable_declaration(
        &mut self,
        _path: &'a NodePath<'a>,
        declaration: &'a VariableDeclaration<'a>,
    ) {
        let pattern = unwrap_or_return!(declaration.pattern());
        let init = unwrap_or_return!(declaration.init());

        if let PatternKind::VariablePattern(var_pattern) = pattern.kind() {
            var_pattern
                .r#type()
                .unify(self.arena, init.r#type())
                .unwrap_or_else(|err| panic!("Type error: {}", err));
        } else {
            todo!("warn: except for variable pattern, we can't infer type.");
        }
    }

    fn exit_variable_expression(
        &mut self,
        path: &'a NodePath<'a>,
        expr: &'a VariableExpression<'a>,
    ) {
        if let Some(binding) = path.scope().get_binding(expr.name()) {
            debug!("[inference] variable_expression: {}, {}", expr, binding);
            expr.r#type()
                .unify(self.arena, binding.r#type())
                .unwrap_or_else(|err| panic!("Type error: {}", err));
        }
    }

    fn exit_binary_expression(&mut self, _path: &'a NodePath<'a>, expr: &'a BinaryExpression<'a>) {
        let lhs = expr.lhs();
        let rhs = unwrap_or_return!(expr.rhs());

        debug!("[inference] binary_expression: {}, {}", lhs, rhs);
        lhs.r#type()
            .unify(self.arena, rhs.r#type())
            .unwrap_or_else(|err| panic!("Type error: {}", err));
    }

    fn exit_grouped_expression(
        &mut self,
        _path: &'a NodePath<'a>,
        grouped_expr: &'a GroupedExpression<'a>,
    ) {
        if let Some(expr) = grouped_expr.expression() {
            grouped_expr
                .r#type()
                .unify(self.arena, expr.r#type())
                .unwrap_or_else(|err| panic!("Type error: {}", err));
        }
    }
}
