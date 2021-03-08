use super::{wasm, wasm_type, StackFrame};
use crate::parser;
use crate::parser::Expr;
use crate::sem::Type;
use crate::util::naming::PrefixNaming;
use std::rc::Rc;

// The size of the virtual stack segment (bytes). Default: 32KB (half of page size)
const STACK_SIZE: wasm::Size = wasm::PAGE_SIZE / 2;

const STACK_BASE: wasm::Size = STACK_SIZE;

const CONSTANT_POOL_BASE: wasm::Size = STACK_SIZE;

#[derive(Debug)]
struct BuildWork {
    i32_naming: PrefixNaming,
}

impl BuildWork {
    pub fn new() -> Self {
        Self {
            // To avoid colision with user's local variables, use special prefix,
            //     $.i32.0, $.i32.1, ...
            i32_naming: PrefixNaming::new(".i32."),
        }
    }

    // Local variable names for temporary scratch pad
    pub fn reserve_i32(&mut self) -> String {
        self.i32_naming.next()
    }

    pub fn i32_locals(&self) -> Vec<String> {
        // Regenerate local variable names
        (0..self.i32_naming.index())
            .map(|i| self.i32_naming.name(i))
            .collect()
    }

    /// Returns a new instance whose local variable naming is `A & B`.
    pub fn union(&self, other: &Self) -> Self {
        let i32_naming = if self.i32_naming.index() > other.i32_naming.index() {
            self.i32_naming.clone()
        } else {
            other.i32_naming.clone()
        };

        Self { i32_naming }
    }
    pub fn extend(&mut self, other: &Self) -> &mut Self {
        if other.i32_naming.index() > self.i32_naming.index() {
            self.i32_naming = other.i32_naming.clone();
        }

        self
    }
}

#[derive(Debug, Default)]
pub struct AsmBuilder {}

impl AsmBuilder {
    pub fn new() -> Self {
        AsmBuilder::default()
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
            .init(wasm::Builders::instructions().u32_const(STACK_BASE).build())
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
            .init(wasm::Builders::instructions().u32_const(STACK_BASE).build())
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
            let segment = wasm::Builders::data_segment()
                .offset(CONSTANT_POOL_BASE + s.offset())
                .bytes(s.bytes(CONSTANT_POOL_BASE))
                .build();

            module.data_segments.push(segment);
        }

        if let Some(s) = strings.last() {
            let s = s.borrow();
            CONSTANT_POOL_BASE + s.offset() + s.memory_size()
        } else {
            CONSTANT_POOL_BASE
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
        let mut body = wasm::Builders::instructions();

        // -- function body
        // Before building function signature, builds the body of function. Because it may
        // add temporary variables which must be included in locals.
        let locals = {
            let frame = fun_node.frame.as_ref().unwrap();
            let static_size = frame.static_size();

            // prologue
            // --------
            // 1. Push caller's FP on stack
            // 3. Set FP to current SP
            // 4. Forward SP to reserve space for stack frame
            body.comment("-- function prologue")
                .global_get("sp")
                .u32_const(wasm::SIZE_BYTES)
                .i32_sub()
                .global_set("sp")
                .global_get("sp")
                .global_get("fp")
                .i32_store(0);
            body.global_get("sp").global_set("fp");

            if static_size > 0 {
                body.global_get("sp")
                    .u32_const(static_size)
                    .i32_sub()
                    .global_set("sp");
            }

            // body
            let locals = self.build_expr_nodes(&mut body, &fun_node.body, frame);

            // epilogue
            // --------
            // 1. Restore SP to caller's SP = FP + sizeof(Static) + sizeof(FP)
            // 2. Restore FP to caller's FP = Load(FP + sizeof(Static))
            body.comment("-- function epilogue")
                .global_get("fp")
                .u32_const(static_size + wasm::SIZE_BYTES)
                .i32_add()
                .global_set("sp");
            body.global_get("fp").i32_load(static_size).global_set("fp");

            locals
        };

        // -- function signature
        let mut builder = wasm::Builders::function();
        let name = fun_node.name.as_str();

        builder.id(name);

        if fun_node.export {
            builder.export(name);
        }

        // typeuse
        for binding in &fun_node.params {
            let binding = binding.borrow();
            let storage = binding
                .storage
                .as_ref()
                .unwrap_or_else(|| panic!("Invalid binding or allocation"));

            let name = &storage.name;
            let r#type = &storage.r#type;

            builder.named_param(name, wasm_type(r#type).unwrap());
        }

        // params
        match &*fun_node.r#type.borrow() {
            Type::Function { return_type, .. } => {
                if let Some(return_type) = wasm_type(return_type) {
                    builder.result_type(return_type);
                }
            }
            ref ty => panic!("Invalid type signature: {:?}", ty),
        }

        // locals
        for storage in &fun_node.locals {
            builder.named_local(&storage.name, wasm_type(&storage.r#type).unwrap());
        }

        for name in locals.i32_locals() {
            builder.named_local(name, wasm::Type::I32);
        }

        builder.body(body.build());
        builder.build()
    }

    fn build_expr(
        &mut self,
        builder: &mut wasm::InstructionsBuilder,
        node: &parser::Node,
        frame: &StackFrame,
    ) -> BuildWork {
        let mut work = BuildWork::new();

        match &node.expr {
            Expr::Stmt(expr) => {
                // Drop a value if the type of expression is not Void.
                let t = self.build_expr(builder, expr, frame);
                work.extend(&t);

                match *expr.r#type.borrow() {
                    Type::Void => {}
                    _ => {
                        builder
                            .comment("Drop unused result of the statement.")
                            .drop();
                    }
                };
            }
            Expr::Identifier { name, binding } => {
                let binding = binding
                    .as_ref()
                    .unwrap_or_else(|| panic!("Undefined local variable `{}`", name))
                    .borrow();

                let storage = binding
                    .storage
                    .as_ref()
                    .unwrap_or_else(|| panic!("Unbound local variable `{}`", name));

                builder.local_get(&storage.name);
            }
            Expr::Integer(n) => {
                builder.i32_const(*n);
            }
            Expr::String { storage, .. } => {
                let storage = storage
                    .as_ref()
                    .unwrap_or_else(|| panic!("The constant string was not allocated."));

                builder.u32_const(CONSTANT_POOL_BASE + storage.borrow().offset());
            }
            Expr::Array {
                elements,
                object_offset,
            } => {
                let element_type = match &*node.r#type.borrow() {
                    Type::Array(element_type) => Rc::clone(element_type),
                    ty => panic!("Operand must be an array, but was {:?}", ty),
                };
                let element_size = wasm_type(&element_type).unwrap().num_bytes();
                let num_elements = elements.len();
                let object_offset = frame.static_size() - object_offset.unwrap();

                builder.comment(format!(
                    "-- Literal {}[{}]",
                    element_type.borrow(),
                    num_elements
                ));

                for (i, element) in elements.iter().enumerate() {
                    builder
                        .comment(format!(
                            "store the result of {}[{}] at `FP + {} + element size({}) * index({})`",
                            element_type.borrow(),
                            i,
                            object_offset,
                            element_size,
                            i
                        ))
                        .global_get("fp");

                    let offset = object_offset + element_size * (i as wasm::Size);

                    let t = self.build_expr(builder, element, frame);
                    work.extend(&t);
                    builder.i32_store(offset);
                }

                // Store a reference on "Static" frame area.
                let reference_offset = object_offset - wasm::SIZE_BYTES * 2;

                builder
                    .comment(format!("store a reference at `FP + {}`", reference_offset))
                    .comment(format!(
                        "  index  = `FP + object offset({})`",
                        object_offset
                    ))
                    .comment(format!("  length = {}", num_elements))
                    .global_get("fp")
                    .global_get("fp")
                    .u32_const(object_offset)
                    .i32_add()
                    .i32_store(reference_offset)
                    .global_get("fp")
                    .u32_const(num_elements as wasm::Size)
                    .i32_store(reference_offset + wasm::SIZE_BYTES);

                // Returns a reference
                builder
                    .comment(format!("push a reference `FP + {}`", reference_offset))
                    .global_get("fp");
                if reference_offset > 0 {
                    builder.u32_const(reference_offset).i32_add();
                }
            }
            Expr::Subscript { operand, index } => {
                let element_type = match &*operand.r#type.borrow() {
                    Type::Array(element_type) => Rc::clone(element_type),
                    ty => panic!("Operand must be an array, but was {:?}", ty),
                };

                let element_size = wasm_type(&element_type).unwrap().num_bytes();

                // Load the reference of the operand to a local variable
                builder.comment(format!("-- Subscript {}", operand.r#type.borrow()));

                let tmp_memidx = work.reserve_i32();
                let tmp_length = work.reserve_i32();
                let tmp_index = work.reserve_i32();

                let t = self.build_expr(builder, operand, frame);
                work.extend(&t);

                builder
                    .comment("load the reference (index, length) of an array to local variables")
                    .i32_load(0)
                    .local_tee(&tmp_memidx)
                    .i32_load(wasm::SIZE_BYTES)
                    .local_tee(&tmp_length);

                // index
                let t = self.build_expr(builder, index, frame);
                work.extend(&t);
                builder.local_tee(&tmp_index);

                // Check overflow
                builder.comment("boundary check");
                builder.i32_lt_s();
                builder.push(wasm::Instruction::If {
                    result_type: None,
                    then: wasm::Builders::instructions()
                        .local_get(&tmp_index)
                        .call("println_i32")
                        .drop()
                        .local_get(&tmp_length)
                        .call("println_i32")
                        .drop()
                        .unreachable()
                        .build(),
                    r#else: None,
                });

                // Access
                builder
                    .comment(format!(
                        "access {}[i] at memory index + element size({}) * index",
                        element_type.borrow(),
                        element_size
                    ))
                    .u32_const(element_size)
                    .local_get(&tmp_index)
                    .i32_mul()
                    .local_get(&tmp_memidx)
                    .i32_add()
                    .i32_load(0);
            }
            Expr::Invocation {
                name,
                arguments,
                binding,
            } => {
                let binding = binding
                    .as_ref()
                    .unwrap_or_else(|| panic!("Undefined function `{}`", name))
                    .borrow();
                let storage = binding
                    .storage
                    .as_ref()
                    .unwrap_or_else(|| panic!("no storage for function `{}`", name));

                for arg in arguments {
                    let t = self.build_expr(builder, arg, frame);
                    work.extend(&t);
                }

                builder.call(&storage.name);
            }
            // binop
            Expr::Add(lhs, rhs, _) => {
                let t1 = self.build_expr(builder, lhs, frame);
                let t2 = self.build_expr(builder, rhs, frame);
                work.extend(&t1).extend(&t2);
                builder.i32_add();
            }
            Expr::Sub(lhs, rhs, _) => {
                let t1 = self.build_expr(builder, lhs, frame);
                let t2 = self.build_expr(builder, rhs, frame);
                work.extend(&t1).extend(&t2);
                builder.i32_sub();
            }
            Expr::Rem(lhs, rhs, _) => {
                let t1 = self.build_expr(builder, lhs, frame);
                let t2 = self.build_expr(builder, rhs, frame);
                work.extend(&t1).extend(&t2);
                builder.i32_rem_s();
            }
            Expr::Mul(lhs, rhs, _) => {
                let t1 = self.build_expr(builder, lhs, frame);
                let t2 = self.build_expr(builder, rhs, frame);
                work.extend(&t1).extend(&t2);
                builder.i32_mul();
            }
            Expr::Div(lhs, rhs, _) => {
                let t1 = self.build_expr(builder, lhs, frame);
                let t2 = self.build_expr(builder, rhs, frame);
                work.extend(&t1).extend(&t2);
                builder.i32_div_s();
            }
            // relation
            Expr::LT(lhs, rhs, _) => {
                let t1 = self.build_expr(builder, lhs, frame);
                let t2 = self.build_expr(builder, rhs, frame);
                work.extend(&t1).extend(&t2);
                builder.i32_lt_s();
            }
            Expr::GT(lhs, rhs, _) => {
                let t1 = self.build_expr(builder, lhs, frame);
                let t2 = self.build_expr(builder, rhs, frame);
                work.extend(&t1).extend(&t2);
                builder.i32_gt_s();
            }
            Expr::LE(lhs, rhs, _) => {
                let t1 = self.build_expr(builder, lhs, frame);
                let t2 = self.build_expr(builder, rhs, frame);
                work.extend(&t1).extend(&t2);
                builder.i32_le_s();
            }
            Expr::GE(lhs, rhs, _) => {
                let t1 = self.build_expr(builder, lhs, frame);
                let t2 = self.build_expr(builder, rhs, frame);
                work.extend(&t1).extend(&t2);
                builder.i32_ge_s();
            }
            Expr::EQ(lhs, rhs, _) => {
                let t1 = self.build_expr(builder, lhs, frame);
                let t2 = self.build_expr(builder, rhs, frame);
                work.extend(&t1).extend(&t2);
                builder.i32_eq();
            }
            Expr::NE(lhs, rhs, _) => {
                let t1 = self.build_expr(builder, lhs, frame);
                let t2 = self.build_expr(builder, rhs, frame);
                work.extend(&t1).extend(&t2);
                builder.i32_neq();
            }
            Expr::If {
                condition,
                then_body,
                else_body,
            } => {
                let result_type = wasm_type(&node.r#type);
                let t = self.build_expr(builder, condition, frame);
                work.extend(&t);

                let then_insts = {
                    let mut then_builder = wasm::Builders::instructions();
                    let t = self.build_expr_nodes(&mut then_builder, then_body, frame);
                    work.extend(&t);

                    if result_type.is_none() {
                        self.drop_values(&mut then_builder, then_body);
                    }
                    then_builder.build()
                };

                let mut else_insts = None;

                if let Some(else_body) = else_body {
                    if !else_body.is_empty() {
                        let mut else_builder = wasm::Builders::instructions();
                        let t = self.build_expr_nodes(&mut else_builder, else_body, frame);
                        work.extend(&t);

                        if result_type.is_none() {
                            self.drop_values(&mut else_builder, else_body);
                        }
                        else_insts.replace(else_builder.build());
                    }
                }

                builder.push(wasm::Instruction::If {
                    result_type,
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
                let t = self.build_expr(builder, head, frame);
                work.extend(&t);

                let head_storage = head_storage
                    .as_ref()
                    .unwrap_or_else(|| panic!("No allocation for head expression."));

                builder.local_set(&head_storage.name);

                // Build all arms, including the `else` clause, in reverse order.
                let mut else_builder = wasm::Builders::instructions();

                if let Some(else_body) = else_body {
                    // `else` must not be empty.
                    let t = self.build_expr_nodes(&mut else_builder, else_body, frame);
                    work.extend(&t);
                } else {
                    // if omitted, all arms must be exhausted.
                    // TODO: remove redundant `if`
                    else_builder.unreachable();
                }

                let else_insts = Some(else_builder.build());

                let arm_insts = arms.iter().rev().fold(else_insts, |acc, arm| {
                    let mut arm_builder = wasm::Builders::instructions();
                    let mut is_pattern_pushed_value = false;

                    // 2. Each pattern will push the value whether pattern matched or not.
                    match &arm.pattern {
                        // variable pattern
                        parser::Pattern::Variable(name, binding) => {
                            let binding = binding.borrow();
                            let storage = binding
                                .storage
                                .as_ref()
                                .unwrap_or_else(|| panic!("Unallocated pattern `{}`", name));

                            // set the result of head expression to the variable.
                            arm_builder.local_get(&head_storage.name);
                            arm_builder.local_set(&storage.name);
                        }
                        parser::Pattern::Integer(i) => {
                            // Constant pattern is semantically identical to `_ if head == pattern`,
                            // but it can be more preciously handled in exhaustivity check.
                            arm_builder
                                .local_get(&head_storage.name)
                                .i32_const(*i)
                                .i32_eq();
                            is_pattern_pushed_value = true;
                        }
                        pat @ parser::Pattern::Array(_) => {
                            // `block` [i32] ->
                            // - Push the result `0`
                            // - Push the length of head (`L1`) on the stack
                            // - Compare the length of pattern (`L2`) and `L1`
                            // - Break if `L1` != `l2`
                            // - Push the element at index `0` of head on the stack
                            // - Evaluate a child pattern at index `0`
                            // - Break if pottern match failed
                            // - ... and so on
                            // - Drop the result `0`
                            // - Push the result `1`
                            let mut block_builder = wasm::Builders::instructions();

                            block_builder.comment(format!("array pattern -- {}", pat));

                            arm_builder.push(wasm::Instruction::Block {
                                result_type: Some(wasm::Type::I32),
                                body: block_builder.build(),
                            });
                        }
                    };

                    // TODO: remove redundant `i32_const`, `if`
                    // 3. Build a guard condition.
                    if let Some(ref condition) = arm.condition {
                        let t = self.build_expr(&mut arm_builder, condition, frame);
                        work.extend(&t);
                    } else {
                        // Pattern without guard always push `true` value.
                        arm_builder.i32_const(1);
                    }

                    if is_pattern_pushed_value {
                        arm_builder.i32_and();
                    }

                    // 4. Build an `if` instruction for arm body and `else` to the next arm or `else` clause.
                    let then_insts = {
                        let mut then_builder = wasm::Builders::instructions();
                        let t = self.build_expr_nodes(&mut then_builder, &arm.then_body, frame);

                        work.extend(&t);
                        then_builder.build()
                    };

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
                let t = self.build_expr(builder, init, frame);
                work.extend(&t);

                match pattern {
                    // variable pattern
                    parser::Pattern::Variable(ref name, ref binding) => {
                        let binding = binding.borrow();
                        let storage = binding
                            .storage
                            .as_ref()
                            .unwrap_or_else(|| panic!("Unallocated pattern `{}`", name));

                        builder.local_set(&storage.name);
                    }
                    parser::Pattern::Integer(_) => {
                        panic!("invalid local binding");
                    }
                    parser::Pattern::Array(_) => {
                        todo!("Local binding with array pattern is not yet implemented. ")
                    }
                };
                builder
                    .comment("Pattern without guard always push `true` value.")
                    .i32_const(1);
            }
        };

        work
    }
}

impl AsmBuilder {
    fn build_expr_nodes(
        &mut self,
        builder: &mut wasm::InstructionsBuilder,
        body: &[parser::Node],
        frame: &StackFrame,
    ) -> BuildWork {
        body.iter().fold(BuildWork::new(), |locals, node| {
            let t = self.build_expr(builder, node, frame);
            locals.union(&t)
        })
    }

    fn drop_values(&mut self, builder: &mut wasm::InstructionsBuilder, body: &[parser::Node]) {
        let node = match body.last() {
            None => return,
            Some(node) => node,
        };

        if wasm_type(&node.r#type).is_some() {
            // Currently, only one value will be remian on the stack.
            builder.drop();
        }
    }
}
