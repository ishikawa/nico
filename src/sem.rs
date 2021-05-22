pub mod binder;
pub mod inferencer;
pub mod validator;
use crate::asm;
use crate::parser;
use crate::util::wrap;
pub use binder::Binder;
pub use inferencer::TypeInferencer;
use std::collections::hash_map;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;
use std::{cell::RefCell, collections::HashSet};

pub use validator::TypeValidator;

pub trait SemanticAnalyzer {
    fn analyze(&mut self, module: &mut parser::Module);
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructType {
    name: String,
    fields: HashMap<String, Rc<RefCell<Type>>>,
}

impl StructType {
    pub fn new<S: Into<String>>(name: S, fields: HashMap<String, Rc<RefCell<Type>>>) -> Self {
        Self {
            name: name.into(),
            fields,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn fields(&self) -> &HashMap<String, Rc<RefCell<Type>>> {
        &self.fields
    }

    pub fn contains_type(&self, other: &Type) -> bool {
        self.fields
            .iter()
            .any(|(_name, ty)| ty.borrow().contains(other))
    }
}

impl fmt::Display for StructType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut it = self.fields.iter().peekable();

        write!(f, "{} ", self.name)?;
        write!(f, "{{ ")?;
        while let Some((name, ty)) = it.next() {
            write!(f, "{}: {}", name, ty.borrow())?;
            if it.peek().is_some() {
                write!(f, ", ")?;
            }
        }
        write!(f, " }}")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct IncompleteStructType {
    fields: HashMap<String, Rc<RefCell<Type>>>,
}

impl IncompleteStructType {
    pub fn new(fields: HashMap<String, Rc<RefCell<Type>>>) -> Self {
        Self { fields }
    }

    pub fn fields(&self) -> &HashMap<String, Rc<RefCell<Type>>> {
        &self.fields
    }

    pub fn contains_type(&self, other: &Type) -> bool {
        self.fields
            .iter()
            .any(|(_name, ty)| ty.borrow().contains(other))
    }
}

impl fmt::Display for IncompleteStructType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut it = self.fields.iter().peekable();

        write!(f, "{{ ")?;
        while let Some((name, ty)) = it.next() {
            write!(f, "{}: {}", name, ty.borrow())?;
            if it.peek().is_some() {
                write!(f, ", ")?;
            }
        }
        write!(f, " }}")
    }
}

#[derive(Debug)]
pub enum Type {
    /// Unspecified and not yet inferred type.
    Unknown,
    Int32,
    Boolean,
    String,
    /// Unit type. In many functional programming languages, this is
    /// written as `()`, but I am more familiar with `Void`.
    Void,
    Array(Rc<RefCell<Type>>),
    Struct(StructType),
    /// Access `x.field` and Pattern `{ field, ...}` generates this constraint.
    IncompleteStruct(IncompleteStructType),
    Function {
        params: Vec<Rc<RefCell<Type>>>,
        return_type: Rc<RefCell<Type>>,
    },
    TypeVariable {
        name: String,
        instance: Option<Rc<RefCell<Type>>>,
    },
}

/// A variable and function representation.
#[derive(Debug, PartialEq)]
pub struct Binding {
    // The variable name in the source code.
    // `None` if the variable is ignored (e.g `_`, `...`)
    pub name: Option<String>,
    // The reference to a runtime storage
    // `None` if the variable is ignored (e.g `_`, `...`)
    pub storage: Option<Rc<asm::Storage>>,
    // The type of a target being referenced.
    pub r#type: Rc<RefCell<Type>>,
}

impl Binding {
    // -- initializers
    pub fn builtin_function<S: Into<String>>(name: S, function_type: Type) -> Self {
        Self::defined_function(name, &wrap(function_type))
    }

    pub fn defined_function<S: Into<String>>(name: S, function_type: &Rc<RefCell<Type>>) -> Self {
        let name = name.into();

        Self {
            name: Some(name.clone()),
            r#type: Rc::clone(&function_type),
            storage: Some(Rc::new(asm::Storage::function(name, &function_type))),
        }
    }

    pub fn typed_name<S: Into<String>>(name: S, r#type: &Rc<RefCell<Type>>) -> Self {
        Self {
            name: Some(name.into()),
            r#type: Rc::clone(r#type),
            storage: None,
        }
    }

    pub fn ignored(r#type: &Rc<RefCell<Type>>) -> Self {
        Self {
            name: None,
            r#type: Rc::clone(r#type),
            storage: None,
        }
    }
}

#[derive(Debug, Default)]
pub struct Environment {
    pub parent: Option<Rc<RefCell<Environment>>>,
    bindings: HashMap<String, Rc<RefCell<Binding>>>,
}

impl Environment {
    pub fn prelude() -> Environment {
        let mut env = Environment::new();

        // Binary operators
        for op in &["+", "-", "%", "*", "/"] {
            env.insert(wrap(Binding::builtin_function(
                *op,
                Type::Function {
                    params: vec![wrap(Type::Int32), wrap(Type::Int32)],
                    return_type: wrap(Type::Int32),
                },
            )));
        }
        for op in &["<", ">", "<=", ">=", "==", "!="] {
            env.insert(wrap(Binding::builtin_function(
                *op,
                Type::Function {
                    params: vec![wrap(Type::Int32), wrap(Type::Int32)],
                    return_type: wrap(Type::Boolean),
                },
            )));
        }
        // Unary operators
        for op in &["@+", "@-"] {
            env.insert(wrap(Binding::builtin_function(
                *op,
                Type::Function {
                    params: vec![wrap(Type::Int32)],
                    return_type: wrap(Type::Int32),
                },
            )));
        }
        // print
        env.insert(wrap(Binding::builtin_function(
            "println_str",
            Type::Function {
                params: vec![wrap(Type::String)],
                return_type: wrap(Type::Int32),
            },
        )));
        env.insert(wrap(Binding::builtin_function(
            "println_i32",
            Type::Function {
                params: vec![wrap(Type::Int32)],
                return_type: wrap(Type::Int32),
            },
        )));
        env.insert(wrap(Binding::builtin_function(
            "debug_i32",
            Type::Function {
                params: vec![wrap(Type::String), wrap(Type::Int32)],
                return_type: wrap(Type::Int32),
            },
        )));

        env
    }

    pub fn new() -> Self {
        Environment::default()
    }

    pub fn with_parent(parent: Rc<RefCell<Environment>>) -> Environment {
        Environment {
            parent: Some(parent),
            bindings: HashMap::new(),
        }
    }

    /// Inserts a new binding into this environment.
    /// Does nothing if a binding is an ignored pattern.
    pub fn insert(&mut self, binding: Rc<RefCell<Binding>>) {
        if let Some(name) = &binding.borrow().name {
            self.bindings.insert(name.clone(), Rc::clone(&binding));
        }
    }

    pub fn get(&self, name: &str) -> Option<Rc<RefCell<Binding>>> {
        match self.bindings.get(name) {
            None => match self.parent {
                None => None,
                Some(ref parent) => parent.borrow().get(name).map(|x| Rc::clone(&x)),
            },
            Some(binding) => Some(Rc::clone(binding)),
        }
    }

    pub fn bindings(&self) -> hash_map::Values<'_, String, Rc<RefCell<Binding>>> {
        self.bindings.values()
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Unknown => write!(f, "{{unknown}}"),
            Type::Int32 => write!(f, "i32"),
            Type::Boolean => write!(f, "bool"),
            Type::String => write!(f, "str"),
            Type::Void => write!(f, "void"),
            Type::Array(element_type) => write!(f, "{}[]", element_type.borrow()),
            Type::Struct(struct_type) => write!(f, "{}", struct_type),
            Type::IncompleteStruct(struct_type) => write!(f, "{}", struct_type),
            Type::Function {
                params,
                return_type,
            } => {
                let mut it = params.iter().peekable();

                write!(f, "(")?;
                while let Some(param) = it.next() {
                    write!(f, "{}", param.borrow())?;
                    if it.peek().is_some() {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ") -> {}", return_type.borrow())
            }
            Type::TypeVariable {
                name,
                instance: None,
            } => write!(f, "{}", name),
            Type::TypeVariable {
                name,
                instance: Some(instance),
            } => write!(f, "{}<{}>", name, instance.borrow()),
        }
    }
}

impl Type {
    pub fn new_type_var(name: &str) -> Self {
        Type::TypeVariable {
            name: name.to_string(),
            instance: None,
        }
    }

    pub fn struct_type(&self) -> Option<&StructType> {
        match self {
            Type::Struct(struct_type) => Some(struct_type),
            _ => None,
        }
    }

    pub fn struct_fields(&self) -> Option<&HashMap<String, Rc<RefCell<Type>>>> {
        match self {
            Type::Struct(struct_type) => Some(struct_type.fields()),
            Type::IncompleteStruct(struct_type) => Some(struct_type.fields()),
            _ => None,
        }
    }

    pub fn element_type(ty: &Self) -> Option<Rc<RefCell<Self>>> {
        match ty {
            Type::Array(ref element_type) => Some(Rc::clone(element_type)),
            _ => None,
        }
    }

    pub fn unwrap_element_type_or_else<F>(ty: &Rc<RefCell<Self>>, fun: F) -> Rc<RefCell<Self>>
    where
        F: FnOnce(&Self) -> Rc<RefCell<Self>>,
    {
        match *ty.borrow() {
            Type::Array(ref element_type) => Rc::clone(element_type),
            ref ty => fun(ty),
        }
    }

    /// Returns `true` if the type given by the 2nd argument appears in this type.
    pub fn contains(&self, other: &Self) -> bool {
        match self {
            Type::Unknown => false,
            Type::Int32 => matches!(other, Type::Int32),
            Type::Boolean => matches!(other, Type::Boolean),
            Type::String => matches!(other, Type::String),
            Type::Array(element_type) => element_type.borrow().contains(other),
            Type::Struct(struct_type) => struct_type.contains_type(other),
            Type::IncompleteStruct(struct_type) => struct_type.contains_type(other),
            Type::Void => matches!(other, Type::Void),
            Type::Function {
                params,
                return_type,
            } => {
                params.iter().any(|x| x.borrow().contains(other))
                    || return_type.borrow().contains(other)
            }
            Type::TypeVariable { instance: None, .. } => self == other,
            Type::TypeVariable {
                instance: Some(instance),
                ..
            } => (self == other) || (**instance).borrow().contains(other),
        }
    }
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match self {
            Type::Unknown => matches!(other, Type::Unknown),
            Type::Int32 => matches!(other, Type::Int32),
            Type::Boolean => matches!(other, Type::Boolean),
            Type::String => matches!(other, Type::String),
            Type::Array(element_type1) => {
                if let Some(element_type2) = Type::element_type(other) {
                    *element_type1 == element_type2
                } else {
                    false
                }
            }
            Type::Struct(struct_type1) => {
                if let Type::Struct(struct_type2) = other {
                    struct_type1 == struct_type2
                } else {
                    false
                }
            }
            Type::IncompleteStruct(struct_type1) => {
                if let Type::IncompleteStruct(struct_type2) = other {
                    struct_type1 == struct_type2
                } else {
                    false
                }
            }
            Type::Void => matches!(other, Type::Void),
            Type::Function {
                params: params1,
                return_type: return_type1,
            } => match other {
                Type::Function {
                    params: params2,
                    return_type: return_type2,
                } => params1 == params2 && return_type1 == return_type2,
                _ => false,
            },
            // TypeVariable equality depends on name only.
            Type::TypeVariable { name: name1, .. } => match other {
                Type::TypeVariable { name: name2, .. } => name1 == name2,
                _ => false,
            },
        }
    }
}

// Pattern Matching Exhaustivity
//
// References
// ----------
// A Generic Algorithm for Checking Exhaustivity of Pattern Matching
// https://infoscience.epfl.ch/record/225497
#[derive(Debug, PartialEq, Clone)]
enum Space {
    // empty space.
    Empty,
    // all possible values of the type T. It's an infinite set of values.
    Everything(Rc<RefCell<Type>>),
    // concrete value.
    Something(Rc<RefCell<Type>>, Value),
    // union space.
    Union(Box<Space>, Box<Space>),
    // array
    Array(Vec<Space>),
    // rest
    Rest(Rc<RefCell<Type>>),
    // struct
    Struct(HashMap<String, Space>),
}

// Concrete value of a type.
#[derive(Debug, PartialEq, Clone)]
enum Value {
    Int(i32),
}

#[derive(Debug, PartialEq, Clone)]
enum Subtraction {
    Everything,
    Value(Value),
    ExactLength(usize),
    MinimumLength(usize),
    Struct(HashMap<String, Vec<Subtraction>>),
}

impl Space {
    // -- Projections

    pub fn from_type(r#type: &Rc<RefCell<Type>>) -> Space {
        match &*r#type.borrow() {
            Type::Struct(struct_type) => {
                let fields = struct_type
                    .fields
                    .iter()
                    .map(|(name, ty)| (name.clone(), Self::from_type(ty)))
                    .collect();

                Space::Struct(fields)
            }
            _ => Space::Everything(Rc::clone(r#type)),
        }
    }

    pub fn from_pattern(pattern: &parser::Pattern) -> Space {
        match pattern {
            parser::Pattern::Variable(_name, ref binding) => {
                Space::from_type(&binding.borrow().r#type)
            }
            parser::Pattern::Integer(i) => Self::Something(wrap(Type::Int32), Value::Int(*i)),
            parser::Pattern::Array(elements) => {
                let elements = elements.iter().map(|p| Self::from_pattern(p)).collect();
                Self::Array(elements)
            }
            parser::Pattern::Struct { fields, r#type, .. } => {
                let struct_type = r#type.as_ref().unwrap();
                let mut space_fields = HashMap::new();
                let mut type_fields = match &*struct_type.borrow() {
                    Type::Struct(struct_type) => struct_type.fields.clone(),
                    _ => unreachable!(),
                };

                // Missing fields in struct pattern means `field: _`.
                for field in fields {
                    space_fields.insert(field.name.clone(), Self::from_pattern(&field.pattern));
                    type_fields.remove(&field.name);
                }
                for (name, ty) in type_fields {
                    space_fields.insert(name.clone(), Self::from_type(&ty));
                }

                Space::Struct(space_fields)
            }
            parser::Pattern::Rest { ref binding, .. } => {
                Self::Rest(Rc::clone(&binding.borrow().r#type))
            }
        }
    }

    // -- Operations

    /// `self` - `other`
    fn _subtractions(space: &Space) -> Vec<Subtraction> {
        match space {
            Space::Everything(_) => vec![Subtraction::Everything],
            Space::Something(_, value) => vec![Subtraction::Value(value.clone())],
            Space::Union(a, b) => {
                let mut a = Self::_subtractions(a);
                let mut b = Self::_subtractions(b);

                a.append(&mut b);
                a
            }
            Space::Array(spaces) => {
                // A patten `[x, y, z]` consumes an array whose length is 3.
                if spaces.iter().all(|x| matches!(x, Space::Everything(_))) {
                    vec![Subtraction::ExactLength(spaces.len())]
                } else if spaces.iter().any(|x| matches!(x, Space::Rest(_))) {
                    vec![Subtraction::MinimumLength(spaces.len() - 1)]
                } else {
                    vec![]
                }
            }
            Space::Struct(fields) => {
                let subtraction_fields = fields
                    .iter()
                    .map(|(name, space)| (name.clone(), Self::_subtractions(space)))
                    .collect();

                vec![Subtraction::Struct(subtraction_fields)]
            }
            _ => vec![],
        }
    }

    /// `self` <: `other`: whether `self` is a subtype of `other`
    pub fn is_subspace_of(&self, other: &Space) -> bool {
        let subtractions = Self::_subtractions(other);
        self._is_subspace_of(&subtractions)
    }

    pub fn _is_subspace_of(&self, subtractions: &[Subtraction]) -> bool {
        match self {
            Space::Empty => true,
            Space::Union(a, b) => {
                a._is_subspace_of(subtractions) && b._is_subspace_of(subtractions)
            }
            Space::Something(_, value) => {
                // Everything
                if subtractions.iter().any(|x| match x {
                    Subtraction::Everything => true,
                    Subtraction::Value(v) => v == value,
                    _ => false,
                }) {
                    return true;
                }

                false
            }
            Space::Everything(ty) => {
                // Scan all the elements beforehand to gather the necessary information.
                let mut cover = HashSet::<usize>::new();
                let mut minimum_length = None;

                for subtraction in subtractions {
                    match subtraction {
                        Subtraction::Everything => {
                            return true;
                        }
                        Subtraction::MinimumLength(n) => {
                            minimum_length.replace(n);
                        }
                        Subtraction::ExactLength(n) => {
                            cover.insert(*n);
                        }
                        _ => {}
                    }
                }

                match *ty.borrow() {
                    Type::Array(..) => {
                        // Array exhaustivity

                        // -- If patterns have a rest pattern, returns `true` if other
                        // patterns cover possible array lengths < minimal length.
                        if let Some(n) = minimum_length {
                            if (0..*n).all(|i| cover.contains(&i)) {
                                return true;
                            }
                        }
                    }
                    Type::Struct { .. } => unreachable!("A space of struct must be Space::Struct"),
                    _ => {}
                };

                false
            }
            Space::Struct(space_fields) => {
                for subtraction in subtractions {
                    match subtraction {
                        Subtraction::Everything => {
                            return true;
                        }
                        Subtraction::Struct(subtraction_fields) => {
                            let exhausted = space_fields.iter().all(|(name, field_space)| {
                                let value = subtraction_fields.get(name).unwrap();
                                field_space._is_subspace_of(value)
                            });
                            if exhausted {
                                return true;
                            }
                        }
                        _ => {}
                    }
                }

                false
            }
            Space::Array(_) => todo!("Fixed length array type is not yet supported"),
            Space::Rest(_) => unreachable!(),
        }
    }

    pub fn union(&self, other: &Space) -> Space {
        Space::Union(Box::new(self.clone()), Box::new(other.clone()))
    }
}

#[cfg(test)]
mod type_tests {
    use super::*;

    #[test]
    fn eq_type_variable1() {
        let ty1 = Type::TypeVariable {
            name: "a".to_string(),
            instance: None,
        };
        let ty2 = Type::TypeVariable {
            name: "a".to_string(),
            instance: None,
        };

        assert_eq!(ty1, ty2);
    }

    #[test]
    fn eq_type_variable2() {
        // TypeVariable equality depends on name only.
        let ty1 = Type::TypeVariable {
            name: "a".to_string(),
            instance: None,
        };
        let ty2 = Type::TypeVariable {
            name: "a".to_string(),
            instance: Some(Rc::new(RefCell::new(Type::Int32))),
        };

        assert_eq!(ty1, ty2);
    }

    #[test]
    fn contains_monotype() {
        assert!(Type::Int32.contains(&Type::Int32));
        assert!(Type::Boolean.contains(&Type::Boolean));
        assert!(Type::String.contains(&Type::String));
        assert!(!Type::Int32.contains(&Type::Boolean));
    }
    #[test]
    fn contains_poly_type() {
        let ty1 = Type::Function {
            params: vec![Rc::new(RefCell::new(Type::Int32))],
            return_type: Rc::new(RefCell::new(Type::TypeVariable {
                name: "a".to_string(),
                instance: None,
            })),
        };

        assert!(ty1.contains(&Type::Int32));
        assert!(!ty1.contains(&Type::Boolean));
        assert!(ty1.contains(&Type::TypeVariable {
            name: "a".to_string(),
            instance: None,
        }));
    }

    #[test]
    fn contains_type_variable() {
        let ty1 = Type::Function {
            params: vec![Rc::new(RefCell::new(Type::Int32))],
            return_type: Rc::new(RefCell::new(Type::TypeVariable {
                name: "a".to_string(),
                instance: Some(Rc::new(RefCell::new(Type::Boolean))),
            })),
        };

        assert!(!ty1.contains(&Type::String));
        assert!(ty1.contains(&Type::Int32));
        assert!(ty1.contains(&Type::Boolean));
        assert!(ty1.contains(&Type::TypeVariable {
            name: "a".to_string(),
            instance: None,
        }));
    }
}

#[cfg(test)]
mod space_tests {
    use super::*;

    #[test]
    fn boolean_exhaustivity() {
        let true_space = Space::Something(wrap(Type::Boolean), Value::Int(1));
        let false_space = Space::Something(wrap(Type::Boolean), Value::Int(0));
        let boolean_space = true_space.union(&false_space);

        assert!(true_space.is_subspace_of(&true_space));
        assert!(true_space.is_subspace_of(&boolean_space));
        assert!(false_space.is_subspace_of(&false_space));
        assert!(false_space.is_subspace_of(&boolean_space));
        assert!(boolean_space.is_subspace_of(&boolean_space));

        assert!(!true_space.is_subspace_of(&false_space));
        assert!(!boolean_space.is_subspace_of(&true_space));
        assert!(!boolean_space.is_subspace_of(&false_space));
    }

    #[test]
    fn array_exhaustivity() {
        let array_type = wrap(Type::Array(wrap(Type::Int32)));
        let array_space = Space::Everything(Rc::clone(&array_type));

        assert!(array_space.is_subspace_of(&array_space));

        let empty_array_space = Space::Array(vec![]);
        let rest_array_space = Space::Array(vec![
            Space::Everything(wrap(Type::Int32)),
            Space::Rest(Rc::clone(&array_type)),
        ]);

        assert!(!array_space.is_subspace_of(&empty_array_space));
        assert!(!array_space.is_subspace_of(&rest_array_space));

        let union_space = empty_array_space.union(&rest_array_space);
        assert!(array_space.is_subspace_of(&union_space));
    }
}
