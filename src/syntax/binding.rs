use super::{
    traverse, Block, Builtin, CaseArm, DefinitionKind, FunctionDefinition, FunctionParameter,
    NodeKind, NodePath, Pattern, Program, StructDefinition, VariableDeclaration, Visitor,
};
use crate::sem::Type;
use crate::util::wrap;
use std::{
    cell::RefCell,
    collections::HashMap,
    fmt,
    rc::{Rc, Weak},
};

#[derive(Debug, Clone)]
pub struct Binding {
    id: String,
    kind: DefinitionKind,
}

impl Binding {
    pub fn builtin_function<S: Into<String>>(name: S, function_type: Type) -> Self {
        Self::defined_function(name, &wrap(function_type))
    }

    pub fn defined_function<S: Into<String>>(name: S, function_type: &Rc<RefCell<Type>>) -> Self {
        let name = name.into();

        Self {
            id: name.clone(),
            kind: DefinitionKind::Builtin(Rc::new(Builtin::new(name, function_type))),
        }
    }

    pub fn id(&self) -> &str {
        &self.id
    }

    pub fn kind(&self) -> &DefinitionKind {
        &self.kind
    }
}

impl fmt::Display for Binding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            DefinitionKind::Builtin(_) => write!(f, "builtin `{}`", self.id),
            DefinitionKind::StructDefinition(_) => write!(f, "struct `{}`", self.id),
            DefinitionKind::FunctionDefinition(_) => write!(f, "function `{}`", self.id),
            DefinitionKind::FunctionParameter(_) => write!(f, "function parameter `{}`", self.id),
            DefinitionKind::Pattern(_) => write!(f, "local variable `{}`", self.id),
        }
    }
}

#[derive(Debug, Default)]
pub struct Scope {
    bindings: HashMap<String, Rc<RefCell<Binding>>>,
    parent: Weak<RefCell<Scope>>,
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

    pub fn parent(&self) -> &Weak<RefCell<Scope>> {
        &self.parent
    }

    fn insert(&mut self, binding: Binding) {
        self.bindings.insert(binding.id.to_string(), wrap(binding));
    }

    pub fn register_declaration(&mut self, declaration: &NodeKind) {
        if let Some(fun) = declaration.function_definition() {
            if let Some(name) = fun.name() {
                self.insert(Binding {
                    id: name.to_string(),
                    kind: DefinitionKind::FunctionDefinition(Rc::clone(&fun)),
                });
            }
        } else if let Some(param) = declaration.function_parameter() {
            self.insert(Binding {
                id: param.name().to_string(),
                kind: DefinitionKind::FunctionParameter(Rc::clone(&param)),
            });
        } else if let Some(def) = declaration.struct_definition() {
            if let Some(name) = def.name() {
                self.insert(Binding {
                    id: name.to_string(),
                    kind: DefinitionKind::StructDefinition(Rc::clone(&def)),
                });
            }
        } else if let Some(ref pattern) = declaration.pattern() {
            self.register_pattern(pattern);
        }
    }

    pub fn register_pattern(&mut self, pattern: &Rc<Pattern>) {
        match &pattern.kind {
            super::PatternKind::IntegerPattern(_) => {}
            super::PatternKind::StringPattern(_) => {}
            super::PatternKind::VariablePattern(id) => {
                self.insert(Binding {
                    id: id.to_string(),
                    kind: DefinitionKind::Pattern(Rc::clone(pattern)),
                });
            }
            super::PatternKind::ArrayPattern(pat) => {
                for pat in pat.elements() {
                    self.register_pattern(pat);
                }
            }
            super::PatternKind::RestPattern(pat) => {
                if let Some(ref id) = pat.id {
                    self.insert(Binding {
                        id: id.to_string(),
                        kind: DefinitionKind::Pattern(Rc::clone(pattern)),
                    });
                }
            }
            super::PatternKind::StructPattern(pat) => {
                for field in pat.fields() {
                    if let Some(ref value) = field.value {
                        self.register_pattern(value);
                    } else {
                        // omitted
                        let pattern = Pattern::variable_pattern(&field.name);

                        self.insert(Binding {
                            id: field.name.to_string(),
                            kind: DefinitionKind::Pattern(Rc::new(pattern)),
                        });
                    }
                }
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
struct DeclarationBinder {
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
    fn enter_program(&mut self, _path: &mut NodePath, program: &Rc<Program>) {
        self.declarations = Some(Rc::clone(program.declarations_scope()));
    }

    fn enter_struct_definition(&mut self, path: &mut NodePath, _definition: &Rc<StructDefinition>) {
        self.register_declaration(path.node());
    }

    fn enter_function_definition(
        &mut self,
        path: &mut NodePath,
        _definition: &Rc<FunctionDefinition>,
    ) {
        self.register_declaration(path.node());
    }
}

#[derive(Debug, Default)]
struct BlockBinder {
    scope: Weak<RefCell<Scope>>,
}

impl BlockBinder {
    pub fn new() -> Self {
        Self::default()
    }

    fn _enter_scope(&mut self, _path: &mut NodePath, scope: &Rc<RefCell<Scope>>) {
        scope.borrow_mut().parent = Weak::clone(&self.scope);
        self.scope = Rc::downgrade(scope);
    }

    fn _exit_scope(&mut self, _path: &mut NodePath, _scope: &Rc<RefCell<Scope>>) {
        if let Some(scope) = self.scope.upgrade() {
            self.scope = Weak::clone(&scope.borrow().parent);
        }
    }
}

impl Visitor for BlockBinder {
    fn enter_program(&mut self, _path: &mut NodePath, program: &Rc<Program>) {
        program.main_scope().borrow_mut().parent = Rc::downgrade(program.declarations_scope());
        self.scope = Rc::downgrade(program.main_scope());
    }

    fn enter_function_parameter(&mut self, path: &mut NodePath, _param: &Rc<FunctionParameter>) {
        let node = path.node();

        let parent_path = path.parent().unwrap();
        let parent_path = parent_path.borrow();
        let fun = parent_path.node().function_definition().unwrap();

        let mut scope = fun.body().scope().borrow_mut();
        scope.register_declaration(node);
    }

    fn enter_variable_declaration(
        &mut self,
        _path: &mut NodePath,
        declaration: &Rc<VariableDeclaration>,
    ) {
        if let Some(scope) = self.scope.upgrade() {
            if let Some(ref pattern) = declaration.pattern {
                let mut scope = scope.borrow_mut();
                scope.register_declaration(&NodeKind::Pattern(Rc::clone(pattern)));
            }
        }
    }

    fn enter_block(&mut self, path: &mut NodePath, block: &Rc<Block>) {
        self._enter_scope(path, block.scope());
    }

    fn exit_block(&mut self, path: &mut NodePath, block: &Rc<Block>) {
        self._exit_scope(path, block.scope());
    }

    fn enter_case_arm(&mut self, path: &mut NodePath, arm: &Rc<CaseArm>) {
        self._enter_scope(path, arm.scope());

        if let Some(ref pattern) = arm.pattern {
            let mut scope = arm.scope().borrow_mut();
            scope.register_declaration(&NodeKind::Pattern(Rc::clone(pattern)));
        }
    }

    fn exit_case_arm(&mut self, path: &mut NodePath, arm: &Rc<CaseArm>) {
        self._exit_scope(path, &arm.scope());
    }
}

pub fn bind_scopes(node: &Rc<Program>) {
    let mut binder = DeclarationBinder::new();
    traverse(&mut binder, node);

    let mut binder = BlockBinder::new();
    traverse(&mut binder, node);
}

#[cfg(test)]
mod tests {
    use crate::syntax::Parser;

    #[test]
    fn top_level_declarations() {
        let program = Parser::parse_string("fun foo()\nend");

        let scope = program.declarations_scope().borrow();
        let binding = scope.get_binding("foo");

        assert!(binding.is_some());

        let binding = binding.unwrap();
        assert_eq!(binding.borrow().id(), "foo");
    }
}
