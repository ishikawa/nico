use super::wasm;
use crate::asm::LocalStorage;
use crate::parser;
use crate::parser::Expr;
use crate::sem::{Binding, Type};
use std::cell::RefCell;
use std::rc::Rc;

fn wasm_type(ty: &Rc<RefCell<Type>>) -> wasm::Type {
    match *ty.borrow() {
        Type::Int32 => wasm::Type::I32,
        Type::Boolean => wasm::Type::I32,
        Type::String => wasm::Type::I32,
        ref ty => panic!("No wasm type for {:?}", ty),
    }
}

#[derive(Debug, Default)]
pub struct AsmBuilder {}

impl AsmBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn build_module(&self, module_node: &parser::Module) -> wasm::Module {
        let mut module = wasm::Module::new();

        // import - memory
        let import_memory = wasm::Builders::import()
            .module("js")
            .name("mem")
            .desc(wasm::Builders::memory().min(1).build())
            .build();
        module.imports.push(import_memory);

        // import - println_i32
        let import_println_i32 = wasm::Builders::import()
            .module("printer")
            .name("println_i32")
            .desc(
                wasm::Builders::func_desc()
                    .id("println_i32")
                    .param(wasm::Type::I32)
                    .result_type(wasm::Type::I32)
                    .build(),
            )
            .build();
        module.imports.push(import_println_i32);

        // import - println_str
        let import_println_str = wasm::Builders::import()
            .module("printer")
            .name("println_str")
            .desc(
                wasm::Builders::func_desc()
                    .id("println_str")
                    .param(wasm::Type::I32)
                    .result_type(wasm::Type::I32)
                    .build(),
            )
            .build();
        module.imports.push(import_println_str);

        self.build_data_segments(&mut module, module_node);
        self.build_module_functions(&mut module, module_node);

        module
    }

    fn build_data_segments(&self, module: &mut wasm::Module, module_node: &parser::Module) {
        let strings = module_node
            .strings
            .as_ref()
            .unwrap_or_else(|| panic!("string constant pool was not initialized."));
        for s in strings {
            let s = s.borrow();
            let bytes = s.bytes().copied().collect::<Vec<_>>();
            let segment = wasm::Builders::data_segment()
                .offset(s.offset())
                .bytes(bytes)
                .build();

            module.data_segments.push(segment);
        }
    }

    fn build_module_functions(&self, module: &mut wasm::Module, module_node: &parser::Module) {
        if let Some(ref function) = module_node.function {
            module.functions.push(self.build_function(function));
        }
        if let Some(ref function) = module_node.main {
            module.functions.push(self.build_function(function));
        }
    }

    fn build_function(&self, fun_node: &parser::Function) -> wasm::Function {
        let mut builder = wasm::Builders::function();
        let name = fun_node.name.as_str();

        let builder = builder.id(name).export(name);

        // typeuse
        for binding in &fun_node.params {
            match *binding.borrow() {
                Binding::Variable {
                    storage: Some(ref storage),
                    ..
                } => match *storage.borrow() {
                    LocalStorage {
                        ref name,
                        ref r#type,
                    } => builder.named_param(name, wasm_type(r#type)),
                },
                _ => panic!("Invalid binding or allocation"),
            };
        }

        match *fun_node.r#type.borrow() {
            Type::Function {
                ref return_type, ..
            } => {
                builder.result_type(wasm_type(return_type));
            }
            ref ty => panic!("Invalid type signature: {:?}", ty),
        }

        // locals
        for storage in &fun_node.locals {
            match *storage.borrow() {
                LocalStorage {
                    ref name,
                    ref r#type,
                } => builder.named_local(name, wasm_type(r#type)),
            };
        }

        builder.body(self.build_body(&fun_node.body));
        builder.build()
    }

    fn build_body(&self, body: &[parser::Node]) -> Vec<wasm::Instruction> {
        let mut builder = wasm::Builders::instructions();

        let mut body = body.iter().peekable();
        while let Some(node) = body.next() {
            self.build_expr(&mut builder, node);

            // Drop the top value(s) of stack if an expression left a value or
            // the node is not the last one.
            match *node.r#type.borrow() {
                Type::Void => {}
                _ => {
                    // not the last one.
                    if body.peek().is_some() {
                        builder.drop();
                    }
                }
            }
        }

        builder.build()
    }

    fn build_expr(&self, builder: &mut wasm::InstructionsBuilder, node: &parser::Node) {
        let node_type = wasm_type(&node.r#type);

        match &node.expr {
            Expr::Identifier { name, binding } => {
                let binding = binding
                    .as_ref()
                    .unwrap_or_else(|| panic!("Undefined local variable `{}`", name));

                match *binding.borrow() {
                    Binding::Variable { ref storage, .. } => {
                        let storage = storage
                            .as_ref()
                            .unwrap_or_else(|| panic!("Unbound local variable `{}`", name));
                        match *storage.borrow() {
                            LocalStorage { ref name, .. } => builder.local_get(name),
                        };
                    }
                    _ => panic!("Invalid binding for local variable `{}`", name),
                };
            }
            Expr::Integer(n) => {
                builder.i32_const(*n);
            }
            Expr::String { storage, .. } => {
                let storage = storage
                    .as_ref()
                    .unwrap_or_else(|| panic!("The constant string was not allocated."));
                builder.u32_const(storage.borrow().offset());
            }
            Expr::Invocation {
                name,
                arguments,
                binding,
            } => {
                let binding = binding
                    .as_ref()
                    .unwrap_or_else(|| panic!("Undefined function `{}`", name));

                match *binding.borrow() {
                    Binding::Function { ref name, .. } => {
                        for arg in arguments {
                            self.build_expr(builder, arg);
                        }
                        builder.call(name);
                    }
                    _ => panic!("Invalid binding for function `{}`", name),
                }
            }
            // binop
            Expr::Add(lhs, rhs, _) => {
                self.build_expr(builder, lhs);
                self.build_expr(builder, rhs);
                builder.i32_add();
            }
            Expr::Sub(lhs, rhs, _) => {
                self.build_expr(builder, lhs);
                self.build_expr(builder, rhs);
                builder.i32_sub();
            }
            Expr::Rem(lhs, rhs, _) => {
                self.build_expr(builder, lhs);
                self.build_expr(builder, rhs);
                builder.i32_rem_s();
            }
            Expr::Mul(lhs, rhs, _) => {
                self.build_expr(builder, lhs);
                self.build_expr(builder, rhs);
                builder.i32_mul();
            }
            Expr::Div(lhs, rhs, _) => {
                self.build_expr(builder, lhs);
                self.build_expr(builder, rhs);
                builder.i32_div_s();
            }
            // relation
            Expr::LT(lhs, rhs, _) => {
                self.build_expr(builder, lhs);
                self.build_expr(builder, rhs);
                builder.i32_lt_s();
            }
            Expr::GT(lhs, rhs, _) => {
                self.build_expr(builder, lhs);
                self.build_expr(builder, rhs);
                builder.i32_gt_s();
            }
            Expr::LE(lhs, rhs, _) => {
                self.build_expr(builder, lhs);
                self.build_expr(builder, rhs);
                builder.i32_le_s();
            }
            Expr::GE(lhs, rhs, _) => {
                self.build_expr(builder, lhs);
                self.build_expr(builder, rhs);
                builder.i32_ge_s();
            }
            Expr::EQ(lhs, rhs, _) => {
                self.build_expr(builder, lhs);
                self.build_expr(builder, rhs);
                builder.i32_eq();
            }
            Expr::NE(lhs, rhs, _) => {
                self.build_expr(builder, lhs);
                self.build_expr(builder, rhs);
                builder.i32_neq();
            }
            Expr::If {
                condition,
                then_body,
                else_body,
            } => {
                let mut then_builder = wasm::Builders::instructions();
                let mut else_builder = wasm::Builders::instructions();

                self.build_expr(builder, condition);
                self.build_expr(&mut then_builder, then_body);
                match else_body {
                    Some(else_body) => {
                        self.build_expr(&mut else_builder, else_body);
                    }
                    None => {
                        // TODO: Think about what to do when there are no `else` clause.
                        else_builder.i32_const(0);
                    }
                };

                builder.push(wasm::Instruction::If {
                    result_type: node_type,
                    then: then_builder.build(),
                    r#else: Some(else_builder.build()),
                });
            }
            Expr::Case {
                ref head,
                ref head_storage,
                ref arms,
                ref else_body,
            } => {
                // 1. head - push the result of head expression and copy it to
                // the temporary variable.
                self.build_expr(builder, head);

                let head_temp = match head_storage {
                    Some(head_storage) => match *head_storage.borrow() {
                        LocalStorage { ref name, .. } => name.clone(),
                    },
                    None => panic!("No allocation for head expression."),
                };

                builder.local_set(head_temp.clone());

                // Build all arms, including the `else` clause, in reverse order.
                let else_insts = {
                    let mut else_builder = wasm::Builders::instructions();

                    if let Some(ref else_body) = else_body {
                        self.build_expr(&mut else_builder, else_body);
                    } else {
                        // TODO: Think about what to do when there are no `else` clause.
                        else_builder.i32_const(0);
                    }

                    else_builder.build()
                };

                let arm_insts = arms.iter().rev().fold(else_insts, |acc, arm| {
                    let mut arm_builder = wasm::Builders::instructions();

                    // 2. Bind the head value to local variable.
                    match arm.pattern.as_ref() {
                        // variable pattern
                        parser::Pattern::Variable(ref name, ref binding) => {
                            let binding = binding
                                .as_ref()
                                .unwrap_or_else(|| panic!("Unbound pattern `{}`", name));

                            match *(binding.borrow_mut()) {
                                Binding::Variable { ref storage, .. } => {
                                    let storage = storage.as_ref().unwrap_or_else(|| {
                                        panic!("Unallocated pattern `{}`", name)
                                    });

                                    match *storage.borrow() {
                                        LocalStorage { ref name, .. } => {
                                            // set the result of head expression to the variable.
                                            arm_builder.local_get(head_temp.clone());
                                            arm_builder.local_set(name);
                                        }
                                    };
                                }
                                Binding::Function { .. } => panic!("Unexpected binding"),
                            }
                        }
                    };

                    // 3. Build a guard condition.
                    if let Some(ref condition) = arm.condition {
                        self.build_expr(&mut arm_builder, condition);
                    } else {
                        // Without guard, push `true` value.
                        arm_builder.i32_const(1);
                    }

                    // 4. Build an `if` instruction for arm body and `else` to the next arm or `else` clause.
                    let mut then_builder = wasm::Builders::instructions();

                    self.build_expr(&mut then_builder, &arm.then_body);

                    arm_builder.push(wasm::Instruction::If {
                        then: then_builder.build(),
                        r#else: Some(acc),
                        result_type: node_type,
                    });

                    arm_builder.build()
                });

                for inst in arm_insts {
                    builder.push(inst);
                }
            }
        };
    }
}
