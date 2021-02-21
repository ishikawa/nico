use super::ConstantString;
use super::LocalStorage;
use crate::parser;
use crate::sem::Binding;
use crate::util::{wrap, SequenceNaming, UniqueNaming};
use parser::{Expr, Node};
use std::cell::RefCell;
use std::rc::Rc;

// Allocate storages
#[derive(Debug, Default)]
pub struct Allocator {}

impl Allocator {
    pub fn new() -> Self {
        Allocator::default()
    }

    pub fn analyze(&mut self, module: &mut parser::Module) {
        let mut strings = vec![];

        if let Some(ref mut function) = module.function {
            self.analyze_function(function, &mut strings);
        }
        if let Some(ref mut main) = module.main {
            self.analyze_function(main, &mut strings);
        }

        module.strings = Some(strings);
    }

    fn analyze_function(
        &self,
        function: &mut parser::Function,
        strings: &mut Vec<Rc<RefCell<ConstantString>>>,
    ) {
        let mut locals = vec![];
        let mut naming = SequenceNaming::new("");

        // Storage for parameters
        for ref mut binding in &function.params {
            match *binding.borrow_mut() {
                Binding::Variable {
                    ref mut storage,
                    ref r#type,
                    ..
                } => {
                    let v = wrap(LocalStorage {
                        name: naming.next(),
                        r#type: Rc::clone(r#type),
                    });

                    storage.replace(Rc::clone(&v));
                }
                Binding::Function { .. } => panic!("Unexpected binding"),
            }
        }

        self.analyze_expr(&mut function.body, &mut naming, &mut locals, strings);

        function.locals = locals;
    }

    fn analyze_expr<N: UniqueNaming>(
        &self,
        node: &mut Node,
        naming: &mut N,
        locals: &mut Vec<Rc<RefCell<LocalStorage>>>,
        strings: &mut Vec<Rc<RefCell<ConstantString>>>,
    ) {
        match node.expr {
            Expr::Integer(_) => {}
            Expr::String {
                ref content,
                ref mut storage,
            } => {
                let len = strings.iter().fold(0, |accum, x| accum + x.borrow().len());
                let constant = wrap(ConstantString::from_str(&content, len));

                storage.replace(Rc::clone(&constant));
                strings.push(Rc::clone(&constant));
            }
            Expr::Identifier { .. } => {}
            Expr::Invocation {
                name: _,
                ref mut arguments,
                ..
            } => {
                for a in arguments {
                    self.analyze_expr(a, naming, locals, strings);
                }
            }
            // binary op
            Expr::Add(ref mut lhs, ref mut rhs, _)
            | Expr::Sub(ref mut lhs, ref mut rhs, _)
            | Expr::Rem(ref mut lhs, ref mut rhs, _)
            | Expr::Mul(ref mut lhs, ref mut rhs, _)
            | Expr::Div(ref mut lhs, ref mut rhs, _)
            | Expr::LT(ref mut lhs, ref mut rhs, _)
            | Expr::GT(ref mut lhs, ref mut rhs, _)
            | Expr::LE(ref mut lhs, ref mut rhs, _)
            | Expr::GE(ref mut lhs, ref mut rhs, _)
            | Expr::EQ(ref mut lhs, ref mut rhs, _)
            | Expr::NE(ref mut lhs, ref mut rhs, _) => {
                self.analyze_expr(lhs, naming, locals, strings);
                self.analyze_expr(rhs, naming, locals, strings);
            }
            Expr::If {
                ref mut condition,
                ref mut then_body,
                ref mut else_body,
            } => {
                self.analyze_expr(condition, naming, locals, strings);
                self.analyze_expr(then_body, naming, locals, strings);
                if let Some(ref mut else_body) = else_body {
                    self.analyze_expr(else_body, naming, locals, strings);
                }
            }
            Expr::Case {
                ref mut head,
                ref mut head_storage,
                ref mut arms,
                ref mut else_body,
            } => {
                // Allocate a temporary variable for storing the result of
                // head expression.
                self.analyze_expr(head, naming, locals, strings);
                {
                    let temp = wrap(LocalStorage {
                        name: naming.next(),
                        r#type: Rc::clone(&node.r#type),
                    });

                    locals.push(Rc::clone(&temp));
                    head_storage.replace(Rc::clone(&temp));
                }

                for parser::CaseArm {
                    ref mut pattern,
                    ref mut condition,
                    ref mut then_body,
                } in arms
                {
                    if let Some(ref mut else_body) = else_body {
                        self.analyze_expr(else_body, naming, locals, strings);
                    }

                    // Currntly, only "Variable pattern" is supported.
                    // - A variable pattern introduces a new environment into arm body.
                    // - The type of a this kind of pattern is always equal to the type of head.
                    match pattern.as_mut() {
                        parser::Pattern::Variable(ref name, ref mut binding) => {
                            let binding = binding
                                .as_ref()
                                .unwrap_or_else(|| panic!("Unbound pattern `{}`", name));

                            match *(binding.borrow_mut()) {
                                Binding::Variable {
                                    name: _,
                                    ref r#type,
                                    ref mut storage,
                                } => {
                                    let v = wrap(LocalStorage {
                                        name: naming.next(),
                                        r#type: Rc::clone(&r#type),
                                    });

                                    locals.push(Rc::clone(&v));
                                    storage.replace(Rc::clone(&v));
                                }
                                Binding::Function { .. } => panic!("Unexpected binding"),
                            }
                        }
                    };

                    // guard
                    if let Some(ref mut condition) = condition {
                        self.analyze_expr(condition, naming, locals, strings);
                    }

                    self.analyze_expr(then_body, naming, locals, strings);
                }
            }
        };
    }
}
