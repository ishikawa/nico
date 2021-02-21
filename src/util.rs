use std::cell::RefCell;
use std::rc::Rc;

pub fn wrap<T>(ty: T) -> Rc<RefCell<T>> {
    Rc::new(RefCell::new(ty))
}

pub trait UniqueNaming {
    fn next(&mut self) -> String;
}

/// Generates a unique string while continuously incrementing the index internally.
/// The user can specify a prefix for the generated string.
#[derive(Debug)]
pub struct SequenceNaming {
    type_var_index: usize,
    prefix: String,
}

impl SequenceNaming {
    pub fn new(prefix: &str) -> Self {
        Self {
            type_var_index: 0,
            prefix: prefix.to_string(),
        }
    }
}

impl UniqueNaming for SequenceNaming {
    fn next(&mut self) -> String {
        let i = self.type_var_index;
        self.type_var_index += 1;
        format!("{}{}", self.prefix, i)
    }
}
