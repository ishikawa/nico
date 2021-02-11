use std::cell::RefCell;
use std::rc::Rc;

#[derive(Debug)]
pub enum Type {
    Int32,
    Boolean,
    String,
    Function {
        params: Vec<Rc<Type>>,
        return_type: Rc<Type>,
    },
    TypeVariable {
        name: String,
        instance: Option<Rc<RefCell<Type>>>,
    },
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
}
