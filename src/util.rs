pub mod naming;
use std::cell::RefCell;
use std::rc::Rc;

pub fn wrap<T>(ty: T) -> Rc<RefCell<T>> {
    Rc::new(RefCell::new(ty))
}
