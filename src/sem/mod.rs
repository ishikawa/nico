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

/// The name of the reference in the source code,
/// the type of the target being referenced, and
/// the reference to the runtime storage
#[derive(Debug, PartialEq)]
pub enum Binding {
    Variable {
        name: String,
        r#type: Rc<RefCell<Type>>,
        storage: Option<Rc<RefCell<asm::LocalStorage>>>,
    },
    Function {
        name: String,
        r#type: Rc<RefCell<Type>>,
    },
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
            env.insert(wrap(Binding::Function {
                name: op.to_string(),
                r#type: wrap(Type::Function {
                    params: vec![wrap(Type::Int32), wrap(Type::Int32)],
                    return_type: wrap(Type::Int32),
                }),
            }));
        }
        for op in &["<", ">", "<=", ">=", "==", "!="] {
            env.insert(wrap(Binding::Function {
                name: op.to_string(),
                r#type: wrap(Type::Function {
                    params: vec![wrap(Type::Int32), wrap(Type::Int32)],
                    return_type: wrap(Type::Boolean),
                }),
            }));
        }
        // print
        env.insert(wrap(Binding::Function {
            name: "println_str".to_string(),
            r#type: wrap(Type::Function {
                params: vec![wrap(Type::String)],
                return_type: wrap(Type::Int32),
            }),
        }));
        env.insert(wrap(Binding::Function {
            name: "println_i32".to_string(),
            r#type: wrap(Type::Function {
                params: vec![wrap(Type::Int32)],
                return_type: wrap(Type::Int32),
            }),
        }));

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
        let name = match *binding.borrow() {
            Binding::Variable { ref name, .. } | Binding::Function { ref name, .. } => name.clone(),
        };

        self.bindings.insert(name, binding);
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
    // Remmove type variable indirection.
    pub fn fixed_type(ty: &Rc<RefCell<Type>>) -> Rc<RefCell<Type>> {
        match &*ty.borrow() {
            Type::Array(element_type) => wrap(Type::Array(Type::fixed_type(&element_type))),
            Type::Function {
                params,
                return_type,
            } => wrap(Type::Function {
                params: params.iter().map(|p| Type::fixed_type(p)).collect(),
                return_type: Type::fixed_type(return_type),
            }),
            Type::TypeVariable {
                instance: Some(instance),
                ..
            } => Type::fixed_type(instance),
            /*
            Type::TypeVariable {
                name,
                instance: None,
            } => {
                panic!("Type variable `{}` must be unified", name)
            }
            */
            _ => Rc::clone(ty),
        }
    }

    pub fn new_type_var(name: &str) -> Self {
        Type::TypeVariable {
            name: name.to_string(),
            instance: None,
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
            Type::Array(element_type1) => match other {
                Type::Array(element_type2) => element_type1 == element_type2,
                _ => false,
            },
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
    fn contains_polytype() {
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
