pub mod binder;
pub mod inferencer;
use crate::asm;
use crate::parser;
use crate::util::wrap;
pub use binder::Binder;
pub use inferencer::TypeInferencer;
use std::cell::RefCell;
use std::collections::hash_map;
use std::collections::HashMap;
use std::rc::Rc;

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

impl Clone for Type {
    fn clone(&self) -> Self {
        match self {
            Type::Int32 => Type::Int32,
            Type::Boolean => Type::Boolean,
            Type::String => Type::String,
            Type::Void => Type::Void,
            Type::Array(element_type) => Type::Array(Rc::clone(element_type)),
            Type::Function {
                params,
                return_type,
            } => Type::Function {
                params: params.clone(),
                return_type: Rc::clone(return_type),
            },
            Type::TypeVariable { name, instance } => Type::TypeVariable {
                name: name.clone(),
                instance: instance.as_ref().map(|x| Rc::clone(&x)),
            },
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
