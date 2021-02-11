use std::cell::RefCell;
use std::rc::Rc;

#[derive(Debug, PartialEq, Clone)]
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

pub struct Binding {
    pub name: String,
    pub r#type: Rc<Type>,
}
