use super::{
    traverse, Block, FunctionDefinition, FunctionParameter, NodeKind, NodePath, Program,
    StructDefinition, Visitor,
};
use crate::sem::Type;
use crate::util::wrap;
use std::{
    cell::RefCell,
    collections::HashMap,
    rc::{Rc, Weak},
};

#[derive(Debug)]
pub struct Binding {
    id: String,
    kind: BindingKind,
}

impl Binding {
    pub fn builtin_function<S: Into<String>>(name: S, function_type: Type) -> Self {
        Self::defined_function(name, &wrap(function_type))
    }

    pub fn defined_function<S: Into<String>>(name: S, function_type: &Rc<RefCell<Type>>) -> Self {
        let name = name.into();

        Self {
            id: name.clone(),
            kind: BindingKind::Builtin(Rc::clone(&function_type)),
        }
    }

    pub fn id(&self) -> &str {
        &self.id
    }

    pub fn builtin(&self) -> Option<&Rc<RefCell<Type>>> {
        if let BindingKind::Builtin(ref ty) = self.kind {
            Some(ty)
        } else {
            None
        }
    }

    pub fn struct_definition(&self) -> Option<&StructDefinition> {
        if let BindingKind::StructDefinition(ref node) = self.kind {
            Some(node)
        } else {
            None
        }
    }

    pub fn function_definition(&self) -> Option<&FunctionDefinition> {
        if let BindingKind::FunctionDefinition(ref node) = self.kind {
            Some(node)
        } else {
            None
        }
    }

    pub fn function_parameter(&self) -> Option<&FunctionParameter> {
        if let BindingKind::FunctionParameter(ref node) = self.kind {
            Some(node)
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub enum BindingKind {
    // Builtin functions, variables
    Builtin(Rc<RefCell<Type>>),
    // Declaration nodes
    StructDefinition(Rc<StructDefinition>),
    FunctionDefinition(Rc<FunctionDefinition>),
    FunctionParameter(Rc<FunctionParameter>),
}

#[derive(Debug, Default)]
pub struct Scope {
    bindings: HashMap<String, Rc<RefCell<Binding>>>,
    pub parent: Weak<RefCell<Scope>>,
}

impl Scope {
    pub fn prelude() -> Self {
        let mut scope = Self::new();

        // print
        scope.insert(Binding::builtin_function(
            "println_str",
            Type::Function {
                params: vec![wrap(Type::String)],
                return_type: wrap(Type::Int32),
            },
        ));
        scope.insert(Binding::builtin_function(
            "println_i32",
            Type::Function {
                params: vec![wrap(Type::Int32)],
                return_type: wrap(Type::Int32),
            },
        ));
        scope.insert(Binding::builtin_function(
            "debug_i32",
            Type::Function {
                params: vec![wrap(Type::String), wrap(Type::Int32)],
                return_type: wrap(Type::Int32),
            },
        ));

        scope
    }

    pub fn new() -> Self {
        Self::default()
    }

    fn insert(&mut self, binding: Binding) {
        self.bindings.insert(binding.id.to_string(), wrap(binding));
    }

    pub fn register_declaration(&mut self, declaration: &NodeKind) {
        if let Some(fun) = declaration.function_definition() {
            if let Some(name) = fun.name() {
                self.insert(Binding {
                    id: name.to_string(),
                    kind: BindingKind::FunctionDefinition(Rc::clone(&fun)),
                });
            }
        } else if let Some(param) = declaration.function_parameter() {
            self.insert(Binding {
                id: param.name().to_string(),
                kind: BindingKind::FunctionParameter(Rc::clone(&param)),
            });
        } else if let Some(def) = declaration.struct_definition() {
            if let Some(name) = def.name() {
                self.insert(Binding {
                    id: name.to_string(),
                    kind: BindingKind::StructDefinition(Rc::clone(&def)),
                });
            }
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
    fn enter_program(&mut self, _path: &mut NodePath, program: &Program) {
        self.declarations = Some(Rc::clone(&program.declarations));
    }

    fn enter_struct_definition(&mut self, path: &mut NodePath, _definition: &StructDefinition) {
        self.register_declaration(path.node());
    }

    fn enter_function_definition(&mut self, path: &mut NodePath, _definition: &FunctionDefinition) {
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
    fn enter_program(&mut self, _path: &mut NodePath, program: &Program) {
        self.scope = Rc::downgrade(&program.main_scope);
    }

    fn enter_function_parameter(&mut self, path: &mut NodePath, _param: &FunctionParameter) {
        let node = path.node();

        let parent_path = path.parent().unwrap();
        let parent_path = parent_path.borrow();
        let fun = parent_path.node().function_definition().unwrap();

        let mut scope = fun.body().scope.borrow_mut();
        scope.register_declaration(node);
    }

    fn enter_block(&mut self, _path: &mut NodePath, block: &Block) {
        block.scope.borrow_mut().parent = Weak::clone(&self.scope);
        self.scope = Rc::downgrade(&block.scope);
    }

    fn exit_block(&mut self, _path: &mut NodePath, _block: &Block) {
        if let Some(scope) = self.scope.upgrade() {
            self.scope = Weak::clone(&scope.borrow().parent);
        }
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
