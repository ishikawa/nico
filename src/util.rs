pub mod collections;
pub mod naming;

use std::cell::RefCell;
use std::rc::Rc;

pub fn wrap<T>(ty: T) -> Rc<RefCell<T>> {
    Rc::new(RefCell::new(ty))
}

/// Unwraps an optional value or early return.
#[macro_export]
macro_rules! unwrap_or_return {
    ($expr:expr $(,)?) => {
        match $expr {
            Some(val) => val,
            None => {
                return;
            }
        }
    };
}
