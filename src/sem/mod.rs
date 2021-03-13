pub mod binder;
pub mod inferencer;
pub mod validator;
use crate::asm;
use crate::parser;
use crate::util::wrap;
pub use binder::Binder;
pub use inferencer::TypeInferencer;
use std::cell::RefCell;
use std::collections::hash_map;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;
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
    pub name: String,
    // The type of a target being referenced.
    pub r#type: Rc<RefCell<Type>>,
    // The reference to a runtime storage
    pub storage: Option<Rc<asm::Storage>>,
}

impl Binding {
    // -- initializers
    pub fn builtin_function<S: AsRef<str>>(name: S, function_type: Type) -> Self {
        Self::defined_function(name, &wrap(function_type))
    }

    pub fn defined_function<S: AsRef<str>>(name: S, function_type: &Rc<RefCell<Type>>) -> Self {
        Self {
            name: name.as_ref().to_string(),
            r#type: Rc::clone(&function_type),
            storage: Some(Rc::new(asm::Storage::function(name, &function_type))),
        }
    }

    pub fn typed_name<S: AsRef<str>>(name: S, r#type: &Rc<RefCell<Type>>) -> Self {
        Self {
            name: name.as_ref().to_string(),
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

    pub fn insert(&mut self, binding: Rc<RefCell<Binding>>) {
        let name = &binding.borrow().name;
        self.bindings.insert(name.clone(), Rc::clone(&binding));
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

    /// `self` <: `other`: whether `self` is a subtype of `other`
    pub fn is_subspace_of(&self, other: &Space) -> bool {
        match self {
            Space::Empty => true,
            Space::Everything(ty1) => match other {
                Space::Empty => false,
                Space::Everything(ty2) => ty1 == ty2,
                Space::Something(_, _) => false,
                Space::Union(a, b) => self.is_subspace_of(a) || self.is_subspace_of(b),
                Space::Array(spaces) => {
                    // `[...x]` can consume all elements of an array.
                    if Type::element_type(&*ty1.borrow()).is_some() && spaces.len() == 1 {
                        if let Space::Rest(ty2) = &spaces[0] {
                            return ty1 == ty2;
                        }
                    }
                    false
                }
                Space::Rest(_) => false,
            },
            Space::Something(ty1, value1) => match other {
                Space::Empty => false,
                Space::Everything(ty2) => ty1 == ty2,
                Space::Something(ty2, value2) => ty1 == ty2 && value1 == value2,
                Space::Union(a, b) => self.is_subspace_of(a) || self.is_subspace_of(b),
                Space::Array(..) => false,
                Space::Rest(_) => false,
            },
            Space::Union(a, b) => a.is_subspace_of(other) && b.is_subspace_of(other),
            Space::Array(spaces1) => match other {
                Space::Empty => false,
                Space::Everything(..) => true,
                Space::Something(..) => false,
                Space::Union(a, b) => self.is_subspace_of(a) || self.is_subspace_of(b),
                Space::Array(spaces2) => {
                    spaces1.len() == spaces2.len()
                        && spaces1
                            .iter()
                            .zip(spaces2)
                            .all(|(a, b)| a.is_subspace_of(b))
                }
                Space::Rest(_) => false,
            },
            Space::Rest(ty1) => {
                if let Space::Rest(ty2) = other {
                    ty1 == ty2
                } else {
                    false
                }
            }
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
}
