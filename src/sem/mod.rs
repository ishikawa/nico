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

#[derive(Debug)]
pub enum Type {
    Int32,
    Boolean,
    String,
    // Unit type. In many functional programming languages, this is
    // written as `()`, but I am more familiar with `Void`.
    Void,
    Array(Rc<RefCell<Type>>),
    Struct {
        name: Option<String>,
        fields: Vec<TypeField>,
    },
    Function {
        params: Vec<Rc<RefCell<Type>>>,
        return_type: Rc<RefCell<Type>>,
    },
    TypeVariable {
        name: String,
        instance: Option<Rc<RefCell<Type>>>,
    },
}

#[derive(Debug, PartialEq)]
pub struct TypeField {
    pub name: String,
    pub value: Rc<RefCell<Type>>,
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

    pub fn bindings(&self) -> hash_map::Values<String, Rc<RefCell<Binding>>> {
        self.bindings.values()
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Int32 => write!(f, "i32"),
            Type::Boolean => write!(f, "bool"),
            Type::String => write!(f, "str"),
            Type::Void => write!(f, "void"),
            Type::Array(element_type) => write!(f, "{}[]", element_type.borrow()),
            Type::Struct { name, fields } => {
                let mut it = fields.iter().peekable();

                if let Some(name) = name {
                    write!(f, "{} ", name)?;
                }

                write!(f, "{{")?;
                while let Some(field) = it.next() {
                    write!(f, "{}: {}", field.name, field.value.borrow())?;
                    if it.peek().is_some() {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "}}")
            }
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
            Type::Int32 => matches!(other, Type::Int32),
            Type::Boolean => matches!(other, Type::Boolean),
            Type::String => matches!(other, Type::String),
            Type::Array(element_type) => element_type.borrow().contains(other),
            Type::Struct { fields, .. } => fields.iter().any(|x| x.value.borrow().contains(other)),
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
            // Named struct
            Type::Struct {
                name: Some(name1), ..
            } => {
                if let Type::Struct {
                    name: Some(name2), ..
                } = other
                {
                    name1 == name2
                } else {
                    false
                }
            }
            // Anonymous struct
            Type::Struct {
                fields: fields1, ..
            } => {
                if let Type::Struct {
                    fields: fields2, ..
                } = other
                {
                    fields1 == fields2
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
    MinimalLength(usize),
}

impl Space {
    // -- Projections

    pub fn from_type(r#type: &Rc<RefCell<Type>>) -> Space {
        Space::Everything(Rc::clone(r#type))
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
            parser::Pattern::Rest { ref binding, .. } => {
                Self::Rest(Rc::clone(&binding.borrow().r#type))
            }
        }
    }

    // -- Operations

    /// `self` - `other`
    fn _subtract(other: &Space) -> Vec<Subtraction> {
        match other {
            Space::Everything(_) => vec![Subtraction::Everything],
            Space::Something(_, value) => vec![Subtraction::Value(value.clone())],
            Space::Union(a, b) => {
                let mut a = Self::_subtract(a);
                let mut b = Self::_subtract(b);

                a.append(&mut b);
                a
            }
            Space::Array(spaces) => {
                // A patten `[x, y, z]` consumes an array whose length is 3.
                if spaces.iter().all(|x| matches!(x, Space::Everything(_))) {
                    vec![Subtraction::ExactLength(spaces.len())]
                } else if spaces.iter().any(|x| matches!(x, Space::Rest(_))) {
                    vec![Subtraction::MinimalLength(spaces.len() - 1)]
                } else {
                    vec![]
                }
            }
            _ => vec![],
        }
    }

    /// `self` <: `other`: whether `self` is a subtype of `other`
    pub fn is_subspace_of(&self, other: &Space) -> bool {
        match self {
            Space::Empty => true,
            Space::Union(a, b) => a.is_subspace_of(other) && b.is_subspace_of(other),
            Space::Something(_, value) => {
                let subtractions = Self::_subtract(other);

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
            Space::Everything(_) => {
                let subtractions = Self::_subtract(other);

                // Everything
                if subtractions
                    .iter()
                    .any(|x| matches!(x, Subtraction::Everything))
                {
                    return true;
                }

                // Array exhaustivity
                let mut cover = HashSet::<usize>::new();

                // -- collect covered length
                for subtraction in &subtractions {
                    if let Subtraction::ExactLength(n) = subtraction {
                        cover.insert(*n);
                    }
                }
                // -- If patterns have a rest pattern, returns `true` if other
                // patterns cover possible array lengths < minimal length.
                for subtraction in &subtractions {
                    if let Subtraction::MinimalLength(n) = subtraction {
                        if (0..*n).all(|i| cover.contains(&i)) {
                            return true;
                        }
                    }
                }

                false
            }
            Space::Array(_) => false,
            Space::Rest(_) => false,
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
