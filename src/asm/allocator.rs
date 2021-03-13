use super::{wasm, wasm_type, ConstantString, LocalVariables, StackFrame, Storage};
use crate::parser;
use crate::sem::{Binding, Type};
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
        let mut locals = LocalVariables::new(".");
        let mut frame = StackFrame::default();

        // Storage for parameters
        for ref mut binding in &function.params {
            match *binding.borrow_mut() {
                Binding {
                    ref name,
                    ref mut storage,
                    ref r#type,
                    ..
                } => {
                    let v = Storage::local_variable(name, r#type);
                    storage.replace(Rc::new(v));
                }
            }
        }

        locals.push_scope();
        for node in &mut function.body {
            self.analyze_expr(node, &mut locals, strings, &mut frame);
        }
        locals.pop_scope();

        function.locals = Some(locals);
        function.frame = Some(frame);
    }

    fn analyze_expr(
        &self,
        node: &mut Node,
        locals: &mut LocalVariables,
        strings: &mut Vec<Rc<RefCell<ConstantString>>>,
        frame: &mut StackFrame,
    ) {
        match &mut node.expr {
            Expr::Stmt(expr) => self.analyze_expr(expr, locals, strings, frame),
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

                    let element_type = Type::unwrap_element_type_or_else(&node.r#type, |ty| {
                        panic!("Expected Array<T> but was `{}`", ty);
                    });

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
                    self.analyze_expr(element, locals, strings, frame);
                }
            }
            Expr::Subscript { operand, index } => {
                self.analyze_expr(operand, locals, strings, frame);
                self.analyze_expr(index, locals, strings, frame);
            }
            Expr::Invocation {
                name: _, arguments, ..
            } => {
                for a in arguments {
                    self.analyze_expr(a, locals, strings, frame);
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
                self.analyze_expr(lhs, locals, strings, frame);
                self.analyze_expr(rhs, locals, strings, frame);
            }
            Expr::Plus(operand, _) | Expr::Minus(operand, _) => {
                self.analyze_expr(operand, locals, strings, frame)
            }
            Expr::If {
                condition,
                then_body,
                else_body,
            } => {
                locals.push_scope();

                self.analyze_expr(condition, locals, strings, frame);

                {
                    locals.push_scope();
                    for node in then_body {
                        self.analyze_expr(node, locals, strings, frame);
                    }
                    locals.pop_scope();
                }

                if let Some(else_body) = else_body {
                    locals.push_scope();
                    for node in else_body {
                        self.analyze_expr(node, locals, strings, frame);
                    }
                    locals.pop_scope();
                }

                locals.pop_scope();
            }
            Expr::Case {
                head,
                head_storage,
                arms,
                else_body,
            } => {
                locals.push_scope();

                // Allocate a temporary variable for storing the result of
                // head expression.
                self.analyze_expr(head, locals, strings, frame);
                {
                    let temp = locals.reserve(&head.r#type);
                    head_storage.replace(temp);
                }

                if let Some(else_body) = else_body {
                    locals.push_scope();
                    for node in else_body {
                        self.analyze_expr(node, locals, strings, frame);
                    }
                    locals.pop_scope();
                }

                for parser::CaseArm {
                    pattern,
                    condition,
                    then_body,
                } in arms
                {
                    locals.push_scope();
                    self.analyze_pattern(pattern, locals);

                    // guard
                    if let Some(condition) = condition {
                        self.analyze_expr(condition, locals, strings, frame);
                    }

                    for node in then_body {
                        self.analyze_expr(node, locals, strings, frame);
                    }
                    locals.pop_scope();
                }

                locals.pop_scope();
            }
            Expr::Var {
                pattern,
                ref mut init,
            } => {
                self.analyze_expr(init, locals, strings, frame);
                self.analyze_pattern(pattern, locals);
            }
        };
    }

    fn analyze_pattern(&self, pattern: &mut parser::Pattern, locals: &mut LocalVariables) {
        match pattern {
            parser::Pattern::Variable(_name, ref mut binding)
            | parser::Pattern::Rest(_name, ref mut binding) => match *binding.borrow_mut() {
                Binding {
                    ref r#type,
                    ref mut storage,
                    ..
                } => {
                    let v = locals.reserve(r#type);
                    storage.replace(v);
                }
            },
            parser::Pattern::Integer(_) => {}
            parser::Pattern::Array(patterns) => {
                for pattern in patterns {
                    self.analyze_pattern(pattern, locals);
                }
            }
        };
    }
}
