use crate::arena::{BumpaloArena, BumpaloString, BumpaloVec};
use std::cell::Cell;
use std::fmt::Display;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TypeError<'a> {
    TypeMismatchError(TypeMismatchError<'a>),
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
        if let &TypeKind::StructType(ty) = self {
            Some(ty)
        } else {
            None
        }
    }

    pub fn function_type(&self) -> Option<&'a FunctionType<'a>> {
        if let &TypeKind::FunctionType(ty) = self {
            Some(ty)
        } else {
            None
        }
    }

    pub fn array_type(&self) -> Option<&'a ArrayType<'a>> {
        if let &TypeKind::ArrayType(ty) = self {
            Some(ty)
        } else {
            None
        }
    }

    pub fn type_variable(&self) -> Option<&'a TypeVariable<'a>> {
        if let &TypeKind::TypeVariable(ty) = self {
            Some(ty)
        } else {
            None
        }
    }

    pub fn is_function_type(&self) -> bool {
        matches!(self, TypeKind::FunctionType(..))
    }

    pub fn is_struct_type(&self) -> bool {
        matches!(self, TypeKind::StructType(..))
    }

    pub fn prune(self) -> Self {
        if let TypeKind::TypeVariable(ty) = self {
            Self::TypeVariable(ty.prune())
        } else {
            self
        }
    }

    pub fn unify(
        &self,
        arena: &'a BumpaloArena,
        other: TypeKind<'a>,
    ) -> Result<TypeKind<'a>, TypeError<'a>> {
        let ty1 = self.prune();
        let ty2 = other.prune();

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
        write!(f, "{}: {}", self.name(), self.r#type())
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
        write!(f, "{}[]", self.element_type())
    }
}

#[derive(Debug)]
pub struct TypeVariable<'a> {
    label: i32,
    inner: Cell<Option<TypeKind<'a>>>,
}

impl<'a> TypeVariable<'a> {
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
        let pruned = if let Some(inner) = self.inner.get() {
            match inner {
                TypeKind::TypeVariable(var) => var.prune(),
                _ => return self,
            }
        } else {
            return self;
        };

        // Prune intermediate type variables.
        self.inner.replace(Some(TypeKind::TypeVariable(pruned)));
        return pruned;
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

impl<'a> PartialEq for TypeVariable<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.label == other.label
    }
}
