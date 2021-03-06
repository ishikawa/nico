use super::{wasm, wasm_type, ConstantString, LocalStorage, StackFrame};
use crate::parser;
use crate::sem::{Binding, Type};
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
        let mut naming = SequenceNaming::new();
        let mut locals = vec![];
        let mut frame = StackFrame::default();

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
            self.analyze_expr(node, &mut naming, &mut locals, strings, &mut frame);
        }

        function.locals = locals;
        function.frame = Some(frame);
    }

    fn analyze_expr(
        &self,
        node: &mut Node,
        naming: &mut SequenceNaming,
        locals: &mut Vec<Rc<RefCell<LocalStorage>>>,
        strings: &mut Vec<Rc<RefCell<ConstantString>>>,
        frame: &mut StackFrame,
    ) {
        match &mut node.expr {
            Expr::Stmt(expr) => self.analyze_expr(expr, naming, locals, strings, frame),
            Expr::Integer(_) => {}
            Expr::String {
                ref content,
                storage,
            } => {
                let len = strings
                    .iter()
                    .fold(0, |accum, x| accum + x.borrow().memory_size());
                let constant = wrap(ConstantString::from_str(&content, len));

                storage.replace(Rc::clone(&constant));
                strings.push(Rc::clone(&constant));
            }
            Expr::Identifier { .. } => {}
            Expr::Array {
                elements,
                ref mut object_offset,
            } => {
                // Reserve stack frame for elements and a reference to array.
                {
                    let length = elements.len();

                    let element_type = match &*node.r#type.borrow() {
                        Type::Array(element_type) => Rc::clone(element_type),
                        ty => {
                            panic!("Expected Array<T> but was `{:?}` for node `{:?}`", ty, node)
                        }
                    };

                    let element_size = wasm_type(&element_type).unwrap().num_bytes();

                    // - Reserve elements in "Static" frame area and store it in the node.
                    frame.reserve(element_size * (length as wasm::Size));
                    object_offset.replace(frame.static_size());

                    // Reserve a reference in "Static" frame area.
                    // - length
                    frame.reserve(wasm::SIZE_BYTES);
                    // - index
                    frame.reserve(wasm::SIZE_BYTES);
                }

                // Allocate every elements
                for element in elements {
                    self.analyze_expr(element, naming, locals, strings, frame);
                }
            }
            Expr::Subscript { operand, index } => {
                self.analyze_expr(operand, naming, locals, strings, frame);
                self.analyze_expr(index, naming, locals, strings, frame);
            }
            Expr::Invocation {
                name: _, arguments, ..
            } => {
                for a in arguments {
                    self.analyze_expr(a, naming, locals, strings, frame);
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
                self.analyze_expr(lhs, naming, locals, strings, frame);
                self.analyze_expr(rhs, naming, locals, strings, frame);
            }
            Expr::If {
                condition,
                then_body,
                else_body,
            } => {
                self.analyze_expr(condition, naming, locals, strings, frame);

                for node in then_body {
                    self.analyze_expr(node, naming, locals, strings, frame);
                }
                if let Some(else_body) = else_body {
                    for node in else_body {
                        self.analyze_expr(node, naming, locals, strings, frame);
                    }
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
                self.analyze_expr(head, naming, locals, strings, frame);
                {
                    let temp = wrap(LocalStorage {
                        name: naming.next("_case_head"),
                        r#type: Rc::clone(&head.r#type),
                    });

                    locals.push(Rc::clone(&temp));
                    head_storage.replace(Rc::clone(&temp));
                }

                if let Some(else_body) = else_body {
                    for node in else_body {
                        self.analyze_expr(node, naming, locals, strings, frame);
                    }
                }

                for parser::CaseArm {
                    pattern,
                    condition,
                    then_body,
                } in arms
                {
                    self.analyze_pattern(pattern, naming, locals);

                    // guard
                    if let Some(condition) = condition {
                        self.analyze_expr(condition, naming, locals, strings, frame);
                    }

                    for node in then_body {
                        self.analyze_expr(node, naming, locals, strings, frame);
                    }
                }
            }
            Expr::Var {
                pattern,
                ref mut init,
            } => {
                self.analyze_expr(init, naming, locals, strings, frame);
                self.analyze_pattern(pattern, naming, locals);
            }
        };
    }

    fn analyze_pattern(
        &self,
        pattern: &mut parser::Pattern,
        naming: &mut SequenceNaming,
        locals: &mut Vec<Rc<RefCell<LocalStorage>>>,
    ) {
        // Currntly, only "Variable pattern" is supported.
        match pattern {
            parser::Pattern::Variable(ref name, ref mut binding) => {
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
    }
}
