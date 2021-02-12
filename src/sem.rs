use std::cell::RefCell;
use std::rc::Rc;

#[derive(Debug)]
pub enum Type {
    Int32,
    Boolean,
    String,
    Function {
        params: Vec<Rc<RefCell<Type>>>,
        return_type: Rc<RefCell<Type>>,
    },
    TypeVariable {
        name: String,
        instance: Option<Rc<RefCell<Type>>>,
    },
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
mod tests {
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
