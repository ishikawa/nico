use super::{traverse, NodeKind, NodePath, Visitor};
use crate::util::wrap;
use std::{
    cell::RefCell,
    collections::HashMap,
    fmt::Display,
    rc::{Rc, Weak},
};

#[derive(Debug)]
pub struct Binding {
    id: String,
    node: NodeKind,
}

impl Binding {
    pub fn id(&self) -> &str {
        &self.id
    }

    pub fn node(&self) -> &NodeKind {
        &self.node
    }
}

#[derive(Debug, Default)]
pub struct Scope {
    bindings: HashMap<String, Rc<RefCell<Binding>>>,
    pub parent: Weak<RefCell<Scope>>,
}

impl Scope {
    pub fn new() -> Self {
        Self::default()
    }

    fn insert_binding(&mut self, binding: Binding) {
        self.bindings.insert(binding.id.to_string(), wrap(binding));
    }

    pub fn register_declaration(&mut self, declaration: &NodeKind) {
        if let Some(fun) = declaration.function_definition() {
            if let Some(name) = fun.name() {
                self.insert_binding(Binding {
                    id: name.to_string(),
                    node: declaration.clone(),
                });
            }
        } else if let Some(def) = declaration.struct_definition() {
            if let Some(name) = def.name() {
                self.insert_binding(Binding {
                    id: name.to_string(),
                    node: declaration.clone(),
                });
            }
        } else if let Some(param) = declaration.function_parameter() {
            self.insert_binding(Binding {
                id: param.name().to_string(),
                node: declaration.clone(),
            });
        }
    }

    pub fn get_binding(&self, name: &str) -> Option<Rc<RefCell<Binding>>> {
        if let Some(binding) = self.bindings.get(name) {
            return Some(Rc::clone(binding));
        }

        if let Some(parent) = self.parent.upgrade() {
            return parent.borrow().get_binding(name);
        }

        None
    }
}

impl Display for Scope {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut peekable = self.bindings.iter().peekable();

        write!(f, "{{")?;
        while let Some((name, binding)) = peekable.next() {
            write!(f, " {}:", name)?;
            write!(f, " {}", binding.borrow().node())?;

            if peekable.peek().is_some() {
                write!(f, ",")?;
            } else if let Some(parent) = self.parent.upgrade() {
                write!(f, "{}", parent.borrow())?;
            } else {
                write!(f, " ")?;
            }
        }
        write!(f, "}}")
    }
}

/// A Visitor collects only top-level declarations in order to resolve forward references.
#[derive(Debug, Default)]
pub struct DeclarationBinder {
    declarations: Option<Rc<RefCell<Scope>>>,
}

impl DeclarationBinder {
    pub fn new() -> Self {
        Self::default()
    }

    fn register_declaration(&mut self, node: &NodeKind) {
        if let Some(ref declarations) = self.declarations {
            declarations.borrow_mut().register_declaration(node);
        }
    }
}

impl Visitor for DeclarationBinder {
    fn enter_program(&mut self, path: &mut NodePath) {
        let node = path.node();
        self.declarations = Some(Rc::clone(&node.program().unwrap().declarations));
    }

    fn enter_struct_definition(&mut self, path: &mut NodePath) {
        self.register_declaration(path.node());
    }

    fn enter_function_definition(&mut self, path: &mut NodePath) {
        self.register_declaration(path.node());
    }
}

#[derive(Debug, Default)]
pub struct BlockBinder {
    scope: Weak<RefCell<Scope>>,
}

impl BlockBinder {
    pub fn new() -> Self {
        Self::default()
    }
}

impl Visitor for BlockBinder {
    fn enter_program(&mut self, path: &mut NodePath) {
        let program = path.node().program().unwrap();

        self.scope = Rc::downgrade(&program.main_scope);
    }

    fn enter_block(&mut self, path: &mut NodePath) {
        let node = path.node();
        let block = node.block().unwrap();

        block.scope.borrow_mut().parent = Weak::clone(&self.scope);
        self.scope = Rc::downgrade(&block.scope);
    }

    fn enter_function_parameter(&mut self, path: &mut NodePath) {
        let node = path.node();

        let parent_path = path.parent().unwrap();
        let parent_path = parent_path.borrow();
        let fun = parent_path.node().function_definition().unwrap();

        let mut scope = fun.body().scope.borrow_mut();
        scope.register_declaration(node);
    }
}

pub fn bind_scopes(node: &NodeKind) {
    let mut binder = DeclarationBinder::new();
    traverse(&mut binder, node, None);

    let mut binder = BlockBinder::new();
    traverse(&mut binder, node, None);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::{traverse, NodeKind, Parser};

    #[test]
    fn top_level_declarations() {
        let mut visitor = DeclarationBinder::new();
        let program = Parser::parse_string("fun foo()\nend");

        traverse(&mut visitor, &NodeKind::Program(Rc::clone(&program)), None);

        let scope = program.declarations.borrow();
        let binding = scope.get_binding("foo");

        assert!(binding.is_some());

        let binding = binding.unwrap();
        assert_eq!(binding.borrow().id(), "foo");
    }
}
