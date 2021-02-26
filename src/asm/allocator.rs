use super::ConstantString;
use super::LocalStorage;
use crate::parser;
use crate::sem::Binding;
use crate::util::naming::SequenceNaming;
use crate::util::wrap;
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

        for function in &mut module.functions {
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
        let mut naming = SequenceNaming::new();

        // Storage for parameters
        for ref mut binding in &function.params {
            match *binding.borrow_mut() {
                Binding::Variable {
                    ref name,
                    ref mut storage,
                    ref r#type,
                    ..
                } => {
                    let v = wrap(LocalStorage {
                        name: naming.next(name),
                        r#type: Rc::clone(r#type),
                    });

                    storage.replace(Rc::clone(&v));
                }
                Binding::Function { .. } => panic!("Unexpected binding"),
            }
        }

        for node in &mut function.body {
            self.analyze_expr(node, &mut naming, &mut locals, strings);
        }

        function.locals = locals;
    }

    fn analyze_expr(
        &self,
        node: &mut Node,
        naming: &mut SequenceNaming,
        locals: &mut Vec<Rc<RefCell<LocalStorage>>>,
        strings: &mut Vec<Rc<RefCell<ConstantString>>>,
    ) {
        match &mut node.expr {
            Expr::Stmt(expr) => self.analyze_expr(expr, naming, locals, strings),
            Expr::Integer(_) => {}
            Expr::String {
                ref content,
                storage,
            } => {
                let len = strings.iter().fold(0, |accum, x| accum + x.borrow().len());
                let constant = wrap(ConstantString::from_str(&content, len));

                storage.replace(Rc::clone(&constant));
                strings.push(Rc::clone(&constant));
            }
            Expr::Identifier { .. } => {}
            Expr::Invocation {
                name: _, arguments, ..
            } => {
                for a in arguments {
                    self.analyze_expr(a, naming, locals, strings);
                }
            }
            // binary op
            Expr::Add(lhs, rhs, _)
            | Expr::Sub(lhs, rhs, _)
            | Expr::Rem(lhs, rhs, _)
            | Expr::Mul(lhs, rhs, _)
            | Expr::Div(lhs, rhs, _)
            | Expr::LT(lhs, rhs, _)
            | Expr::GT(lhs, rhs, _)
            | Expr::LE(lhs, rhs, _)
            | Expr::GE(lhs, rhs, _)
            | Expr::EQ(lhs, rhs, _)
            | Expr::NE(lhs, rhs, _) => {
                self.analyze_expr(lhs, naming, locals, strings);
                self.analyze_expr(rhs, naming, locals, strings);
            }
            Expr::If {
                condition,
                then_body,
                else_body,
            } => {
                self.analyze_expr(condition, naming, locals, strings);

                for node in then_body {
                    self.analyze_expr(node, naming, locals, strings);
                }
                for node in else_body {
                    self.analyze_expr(node, naming, locals, strings);
                }
            }
            Expr::Case {
                head,
                head_storage,
                arms,
                else_body,
            } => {
                // Allocate a temporary variable for storing the result of
                // head expression.
                self.analyze_expr(head, naming, locals, strings);
                {
                    let temp = wrap(LocalStorage {
                        name: naming.next("_case_head"),
                        r#type: Rc::clone(&head.r#type),
                    });

                    locals.push(Rc::clone(&temp));
                    head_storage.replace(Rc::clone(&temp));
                }

                for node in else_body {
                    self.analyze_expr(node, naming, locals, strings);
                }

                for parser::CaseArm {
                    pattern,
                    condition,
                    then_body,
                } in arms
                {
                    // Currntly, only "Variable pattern" is supported.
                    // - A variable pattern introduces a new environment into arm body.
                    // - The type of a this kind of pattern is always equal to the type of head.
                    match pattern {
                        parser::Pattern::Variable(ref name, binding) => {
                            let binding = binding
                                .as_ref()
                                .unwrap_or_else(|| panic!("Unbound pattern `{}`", name));

                            match *(binding.borrow_mut()) {
                                Binding::Variable {
                                    ref name,
                                    ref r#type,
                                    ref mut storage,
                                } => {
                                    let v = wrap(LocalStorage {
                                        name: naming.next(name),
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
                    if let Some(condition) = condition {
                        self.analyze_expr(condition, naming, locals, strings);
                    }

                    for node in then_body {
                        self.analyze_expr(node, naming, locals, strings);
                    }
                }
            }
            Expr::Var { .. } => {
                panic!("not implemented")
            }
        };
    }
}
