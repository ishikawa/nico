use super::wasm;
use crate::asm::LocalStorage;
use crate::parser;
use crate::parser::Expr;
use crate::sem::{Binding, Type};
use crate::util::naming::PrefixNaming;
use std::cell::RefCell;
use std::rc::Rc;

// The size of the virtual stack segment (bytes). Default: 32KB (half of page size)
const STACK_SIZE: u32 = wasm::PAGE_SIZE / 2;

const STACK_OFFSET: u32 = STACK_SIZE;

const CONSTANT_OFFSET: u32 = STACK_SIZE;

fn wasm_type(ty: &Rc<RefCell<Type>>) -> Option<wasm::Type> {
    let ty = Type::unwrap(ty);
    let wty = match *ty.borrow() {
        Type::Int32 => Some(wasm::Type::I32),
        Type::Boolean => Some(wasm::Type::I32),
        Type::String => Some(wasm::Type::I32),
        Type::Void => None,
        Type::Array(_) => Some(wasm::Type::I32),
        Type::TypeVariable { .. } => {
            panic!("Type variable `{:?}` can't be resolved to WASM type.", ty)
        }
        Type::Function { .. } => panic!("Function type `{:?}` can't be resolved to WASM type.", ty),
    };
    wty
}

#[derive(Debug)]
pub struct AsmBuilder {
    // For now, asm emitter can use only one scratch pad.
    i32_tmp_locals: Vec<String>,
    naming: PrefixNaming,
}

impl Default for AsmBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl AsmBuilder {
    pub fn new() -> Self {
        AsmBuilder {
            i32_tmp_locals: vec![],
            // To avoid colision with user's local variables, use special prefix
            naming: PrefixNaming::new("%tmp."),
        }
    }

    pub fn build_module(&mut self, module_node: &parser::Module) -> wasm::Module {
        let mut module = wasm::Module::new();

        // -- import: environment
        let import_memory = wasm::Builders::import()
            .module("nico.runtime")
            .name("mem")
            .desc(wasm::Builders::memory_desc().min(1).build())
            .build();
        module.imports.push(import_memory);

        // -- import: external libraries
        // println_i32
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

        // println_str
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

        // Writes constants to constant pool and increments hp (heap pointer).
        let hp = self.build_data_segments(&mut module, module_node);

        self.build_module_functions(&mut module, module_node);

        // -- globals
        let global_stack_pointer = wasm::Builders::global()
            .id("sp")
            .r#type(wasm::Type::I32)
            .mutable(true)
            .init(
                wasm::Builders::instructions()
                    .u32_const(STACK_OFFSET)
                    .build(),
            )
            .build();
        module.globals.push(global_stack_pointer);

        let global_heap_pointer = wasm::Builders::global()
            .id("hp")
            .r#type(wasm::Type::I32)
            .mutable(true)
            .init(wasm::Builders::instructions().u32_const(hp).build())
            .build();
        module.globals.push(global_heap_pointer);

        let global_frame_pointer = wasm::Builders::global()
            .id("fp")
            .r#type(wasm::Type::I32)
            .mutable(true)
            .init(wasm::Builders::instructions().i32_const(-1).build())
            .build();
        module.globals.push(global_frame_pointer);

        module
    }

    fn build_data_segments(
        &mut self,
        module: &mut wasm::Module,
        module_node: &parser::Module,
    ) -> u32 {
        let strings = module_node
            .strings
            .as_ref()
            .unwrap_or_else(|| panic!("string constant pool was not initialized."));
        for s in strings {
            let s = s.borrow();
            let bytes = s.bytes().copied().collect::<Vec<_>>();
            let segment = wasm::Builders::data_segment()
                .offset(CONSTANT_OFFSET + s.offset())
                .bytes(bytes)
                .build();

            module.data_segments.push(segment);
        }

        if let Some(s) = strings.last() {
            let s = s.borrow();
            CONSTANT_OFFSET + s.offset() + s.len()
        } else {
            CONSTANT_OFFSET
        }
    }

    fn build_module_functions(&mut self, module: &mut wasm::Module, module_node: &parser::Module) {
        for function in &module_node.functions {
            module.functions.push(self.build_function(function));
        }

        if let Some(ref function) = module_node.main {
            module.functions.push(self.build_function(function));
        }
    }

    fn build_function(&mut self, fun_node: &parser::Function) -> wasm::Function {
        // Before building function signature, builds the body of function. Because it may
        // add temporary variables which must be included in locals.
        let body = self.build_body(&fun_node.body);

        let mut builder = wasm::Builders::function();
        let name = fun_node.name.as_str();

        builder.id(name);

        if fun_node.export {
            builder.export(name);
        }

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
                    } => builder.named_param(name, wasm_type(r#type).unwrap()),
                },
                _ => panic!("Invalid binding or allocation"),
            };
        }

        // params
        match *Type::unwrap(&fun_node.r#type).borrow() {
            Type::Function {
                ref return_type, ..
            } => {
                if let Some(return_type) = wasm_type(return_type) {
                    builder.result_type(return_type);
                }
            }
            ref ty => panic!("Invalid type signature: {:?}", ty),
        }

        // locals
        for storage in &fun_node.locals {
            match *storage.borrow() {
                LocalStorage {
                    ref name,
                    ref r#type,
                } => builder.named_local(name, wasm_type(r#type).unwrap()),
            };
        }

        for name in &self.i32_tmp_locals {
            builder.named_local(name, wasm::Type::I32);
        }

        builder.body(body);
        builder.build()
    }

    fn build_body(&mut self, body: &[parser::Node]) -> Vec<wasm::Instruction> {
        let mut builder = wasm::Builders::instructions();

        for node in body {
            self.build_expr(&mut builder, node);
        }

        builder.build()
    }

    fn build_expr(&mut self, builder: &mut wasm::InstructionsBuilder, node: &parser::Node) {
        match &node.expr {
            Expr::Stmt(expr) => {
                // Drop a value if the type of expression is not Void.
                self.build_expr(builder, expr);
                match *Type::unwrap(&expr.r#type).borrow() {
                    Type::Void => {}
                    _ => {
                        builder.drop();
                    }
                };
            }
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
                builder.u32_const(CONSTANT_OFFSET + storage.borrow().offset());
            }
            Expr::Array { elements } => {
                for element in elements {
                    let ty = wasm_type(&element.r#type).unwrap();

                    // Store the value to SP
                    self.push_stack(builder, ty.num_bytes());
                    self.build_expr(builder, element);
                    builder.i32_store();
                }

                // Create a reference

                // Save SP to temporary variable
                builder.global_get("sp").local_set(self.tmp_i32_0());

                // Reference - the number of elements
                self.push_stack(builder, wasm::Type::I32.num_bytes());
                builder.u32_const(elements.len() as u32).i32_store();

                // Reference - saved SP
                self.push_stack(builder, wasm::Type::I32.num_bytes());
                builder.local_get(self.tmp_i32_0()).i32_store();

                // Returns a reference
                builder.global_get("sp");
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
                self.build_expr(builder, condition);

                let then_insts = self.build_body(then_body);
                let else_insts = if !else_body.is_empty() {
                    Some(self.build_body(else_body))
                } else {
                    None
                };

                builder.push(wasm::Instruction::If {
                    result_type: wasm_type(&node.r#type),
                    then: then_insts,
                    r#else: else_insts,
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
                    if !else_body.is_empty() {
                        Some(self.build_body(else_body))
                    } else {
                        None
                    }
                };

                let arm_insts = arms.iter().rev().fold(else_insts, |acc, arm| {
                    let mut arm_builder = wasm::Builders::instructions();

                    // 2. Bind the head value to local variable.
                    match arm.pattern {
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
                        // Pattern without guard always push `true` value.
                        arm_builder.i32_const(1);
                    }

                    // 4. Build an `if` instruction for arm body and `else` to the next arm or `else` clause.
                    let then_insts = self.build_body(&arm.then_body);

                    arm_builder.push(wasm::Instruction::If {
                        then: then_insts,
                        r#else: acc,
                        result_type: wasm_type(&node.r#type),
                    });

                    Some(arm_builder.build())
                });

                if let Some(arm_insts) = arm_insts {
                    for inst in arm_insts {
                        builder.push(inst);
                    }
                }
            }
            Expr::Var { pattern, init } => {
                self.build_expr(builder, init);
                match pattern {
                    // variable pattern
                    parser::Pattern::Variable(ref name, ref binding) => {
                        let binding = binding
                            .as_ref()
                            .unwrap_or_else(|| panic!("Unbound pattern `{}`", name));

                        match *(binding.borrow_mut()) {
                            Binding::Variable { ref storage, .. } => {
                                let storage = storage
                                    .as_ref()
                                    .unwrap_or_else(|| panic!("Unallocated pattern `{}`", name));

                                match *storage.borrow() {
                                    LocalStorage { ref name, .. } => {
                                        builder.local_set(name);
                                    }
                                };
                            }
                            Binding::Function { .. } => panic!("Unexpected binding"),
                        }
                    }
                };
                // Pattern without guard always push `true` value.
                builder.i32_const(1);
            }
        };
    }

    /// Forward SP by `num_bytes` bytes and push the SP to value stack.
    fn push_stack(&self, builder: &mut wasm::InstructionsBuilder, num_bytes: u32) {
        builder
            .global_get("sp")
            .u32_const(num_bytes)
            .i32_sub()
            .global_set("sp")
            .global_get("sp");
    }
    // Local variable names for temporary scratch pad
    fn tmp_i32_0(&mut self) -> &str {
        if self.i32_tmp_locals.is_empty() {
            self.i32_tmp_locals.push(self.naming.next());
        }

        &self.i32_tmp_locals[0]
    }
}
