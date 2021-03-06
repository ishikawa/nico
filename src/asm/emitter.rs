use super::{wasm, wasm_type, LocalVariables, StackFrame};
use crate::parser;
use crate::parser::Expr;
use crate::sem::{Binding, Type};
use std::{cell::RefCell, rc::Rc};
use std::{collections::HashMap, convert::TryFrom};

// The size of the virtual stack segment (bytes). Default: 32KB (half of page size)
const STACK_SIZE: wasm::Size = wasm::PAGE_SIZE / 2;

const STACK_BASE: wasm::Size = STACK_SIZE;

const CONSTANT_POOL_BASE: wasm::Size = STACK_SIZE;

#[derive(Debug, Default)]
pub struct AsmBuilder {}

impl AsmBuilder {
    pub fn new() -> Self {
        AsmBuilder::default()
    }

    pub fn build_module(&self, module_node: &parser::Module) -> wasm::Module {
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

        // debug_i32
        let import_debug_i32 = wasm::Builders::import()
            .module("printer")
            .name("debug_i32")
            .desc(
                wasm::Builders::func_desc()
                    .id("debug_i32")
                    .param(wasm::Type::I32)
                    .param(wasm::Type::I32)
                    .result_type(wasm::Type::I32)
                    .build(),
            )
            .build();
        module.imports.push(import_debug_i32);

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

    fn build_data_segments(&self, module: &mut wasm::Module, module_node: &parser::Module) -> u32 {
        let strings = module_node
            .strings
            .as_ref()
            .expect("string constant pool was not initialized.");
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

    fn build_module_functions(&self, module: &mut wasm::Module, module_node: &parser::Module) {
        for function in &module_node.functions {
            module.functions.push(self.build_function(function));
        }

        if let Some(ref function) = module_node.main {
            module.functions.push(self.build_function(function));
        }
    }

    fn build_function(&self, fun_node: &parser::Function) -> wasm::Function {
        let mut body = wasm::Builders::instructions();
        let mut temp = LocalVariables::new(".tmp.");

        // -- function body
        // Before building function signature, builds the body of function. Because it may
        // add temporary variables which must be included in locals.
        {
            let frame = fun_node.frame.as_ref().unwrap();
            let static_size = frame.static_size();

            // prologue
            // --------
            // 1. Push caller's FP on stack
            // 3. Set FP to current SP
            // 4. Forward FP to reserve space ("Static") for stack frame
            // 5. Forward SP to reserve space ("Static" and "Dynamic") for stack frame
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
                body.global_get("fp")
                    .u32_const(static_size)
                    .i32_sub()
                    .global_set("fp");
            }

            if static_size > 0 {
                body.global_get("sp")
                    .u32_const(static_size)
                    .i32_sub()
                    .global_set("sp");
            }

            // body
            self.build_expr_nodes(&mut body, &fun_node.body, &mut temp, frame);

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
        };

        // -- function signature
        let mut builder = wasm::Builders::function();
        let name = fun_node.name.as_str();

        builder.id(name);

        if fun_node.export {
            builder.export(name);
        }

        // params
        for binding in &fun_node.params {
            let binding = binding.borrow();
            let var = binding
                .storage
                .as_ref()
                .expect("Invalid binding or allocation")
                .unwrap_local_variable();

            builder.named_param(&var.name, var.r#type);
        }

        match &*fun_node.r#type.borrow() {
            Type::Function { return_type, .. } => {
                if let Some(return_type) = wasm_type(return_type) {
                    builder.result_type(return_type);
                }
            }
            ref ty => panic!("Invalid type signature: {}", ty),
        }

        {
            temp.push_scope();
            builder.body(body.build());
            temp.pop_scope();
        }

        // locals/temporary variables
        for storage in fun_node.locals.as_ref().unwrap().variables() {
            let var = storage.unwrap_local_variable();
            builder.named_local(&var.name, var.r#type);
        }

        for storage in temp.variables() {
            let var = storage.unwrap_local_variable();
            builder.named_local(&var.name, var.r#type);
        }

        builder.build()
    }

    fn build_expr(
        &self,
        builder: &mut wasm::InstructionsBuilder,
        node: &parser::Node,
        temp: &mut LocalVariables,
        frame: &StackFrame,
    ) {
        match &node.expr {
            Expr::Stmt(expr) => {
                // Drop a value if the type of expression is not Void.
                self.build_expr(builder, expr, temp, frame);

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

                let var = binding
                    .storage
                    .as_ref()
                    .unwrap_or_else(|| panic!("Unbound local variable `{}`", name))
                    .unwrap_local_variable();

                builder.local_get(&var.name);
            }
            Expr::Integer(n) => {
                builder.i32_const(*n);
            }
            Expr::String { storage, content } => {
                let storage = storage
                    .as_ref()
                    .expect("The constant string was not allocated.");

                builder.u32_const_(
                    CONSTANT_POOL_BASE + storage.borrow().offset(),
                    format!("string {:?}", content),
                );
            }
            Expr::Array {
                elements,
                object_offset,
            } => {
                let element_type = Type::unwrap_element_type_or_else(&node.r#type, |ty| {
                    panic!("Operand must be an array, but was {}", ty);
                });

                let num_elements = elements.len();
                let object_offset = frame.static_size() - object_offset.unwrap();

                builder.comment(format!(
                    "-- Literal {}[{}]",
                    element_type.borrow(),
                    num_elements
                ));

                // This guard is needed because the type of an empty array is undetermined.
                if !elements.is_empty() {
                    let element_size = wasm_type(&element_type).unwrap().num_bytes();

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

                        let offset =
                            object_offset + element_size * wasm::Size::try_from(i).unwrap();

                        self.build_expr(builder, element, temp, frame);
                        builder.i32_store(offset);
                    }
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
                    .u32_const(wasm::Size::try_from(num_elements).unwrap())
                    .i32_store(reference_offset + wasm::SIZE_BYTES);

                // Returns a reference
                builder
                    .comment(format!("push a reference `FP + {}`", reference_offset))
                    .global_get("fp");
                if reference_offset > 0 {
                    builder.u32_const(reference_offset).i32_add();
                }
            }
            Expr::Struct {
                name: struct_name,
                fields,
                object_offset,
            } => {
                // Emit each field of a struct.
                // We have to align the order with that of the struct type fields.
                let type_fields = self.unwrap_struct_type_fields(&node.r#type);

                builder.comment(format!("-- struct {}{{...}}", struct_name));

                let object_offset = frame.static_size() - object_offset.unwrap();

                type_fields
                    .iter()
                    .enumerate()
                    .fold(0, |current_offset, (i, (name, ty))| {
                        // Pick the value field.
                        let value_field = fields.iter().find(|x| x.name == *name).unwrap();
                        let field_size = wasm_type(&ty).unwrap().num_bytes();

                        builder
                            .comment(format!(
                                "store the field #{} `{}.{}` at `FP + {}`",
                                i, struct_name, name, current_offset
                            ))
                            .global_get("fp");

                        if object_offset != 0 {
                            builder.u32_const(object_offset).i32_add();
                        }

                        self.build_expr(builder, &value_field.value, temp, frame);
                        builder.i32_store(current_offset);

                        current_offset + field_size
                    });

                // Returns a reference (the index of the beginning of a struct)
                builder
                    .comment(format!("push a reference `FP + {}`", object_offset))
                    .global_get("fp");
                if object_offset > 0 {
                    builder.u32_const(object_offset).i32_add();
                }
            }
            Expr::Subscript { operand, index } => {
                temp.push_scope();

                let element_type = Type::unwrap_element_type_or_else(&operand.r#type, |ty| {
                    panic!("Operand must be an array, but was {}", ty);
                });
                let element_size = wasm_type(&element_type).unwrap().num_bytes();

                // Load the reference of the operand to a local variable
                builder.comment(&format!("-- Subscript {}", operand.r#type.borrow()));

                let tmp_operand = temp.reserve_name_i32();
                let tmp_index = temp.reserve_name_i32();
                let tmp_memidx = temp.reserve_name_i32();
                let tmp_length = temp.reserve_name_i32();

                self.build_expr(builder, operand, temp, frame);

                builder
                    .comment("load the reference (index, length) of an array to local variables")
                    .local_tee_(&tmp_operand, "operand")
                    .i32_load(0)
                    .local_set_(&tmp_memidx, "memory index")
                    .local_get_(&tmp_operand, "operand")
                    .i32_load(wasm::SIZE_BYTES)
                    .local_tee_(&tmp_length, "length");

                // index
                self.build_expr(builder, index, temp, frame);
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
                    .comment(&format!(
                        "access {}[i] at memory index + element size({}) * index",
                        element_type.borrow(),
                        element_size
                    ))
                    .u32_const(element_size)
                    .local_get_(&tmp_index, "index")
                    .i32_mul()
                    .local_get_(&tmp_memidx, "memory index")
                    .i32_add()
                    .i32_load(0);

                temp.pop_scope();
            }
            Expr::Access {
                operand,
                field: field_name,
            } => {
                temp.push_scope();

                let type_fields = self.unwrap_struct_type_fields(&operand.r#type);

                // Load the memory index of the operand to a local variable
                builder
                    .comment(&format!(
                        "-- Access the field `{}` of {}",
                        field_name,
                        operand.r#type.borrow()
                    ))
                    .comment("operand");

                self.build_expr(builder, operand, temp, frame);

                // Calculate the offset
                let mut offset = 0;

                for (name, ty) in type_fields {
                    if &name == field_name {
                        break;
                    }

                    let field_size = wasm_type(&ty).unwrap().num_bytes();
                    offset += field_size;
                }

                builder.i32_load_(
                    offset,
                    format!("access .{} at base + {}", field_name, offset),
                );

                temp.pop_scope();
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
                let function = binding
                    .storage
                    .as_ref()
                    .unwrap_or_else(|| panic!("no storage for function `{}`", name))
                    .unwrap_function();

                for arg in arguments {
                    self.build_expr(builder, arg, temp, frame);
                }

                builder.call(&function.name);
            }
            Expr::Add(lhs, rhs, _) => {
                self.build_expr(builder, lhs, temp, frame);
                self.build_expr(builder, rhs, temp, frame);

                builder.i32_add();
            }
            Expr::Sub(lhs, rhs, _) => {
                self.build_expr(builder, lhs, temp, frame);
                self.build_expr(builder, rhs, temp, frame);

                builder.i32_sub();
            }
            Expr::Rem(lhs, rhs, _) => {
                self.build_expr(builder, lhs, temp, frame);
                self.build_expr(builder, rhs, temp, frame);

                builder.i32_rem_s();
            }
            Expr::Mul(lhs, rhs, _) => {
                self.build_expr(builder, lhs, temp, frame);
                self.build_expr(builder, rhs, temp, frame);

                builder.i32_mul();
            }
            Expr::Div(lhs, rhs, _) => {
                self.build_expr(builder, lhs, temp, frame);
                self.build_expr(builder, rhs, temp, frame);

                builder.i32_div_s();
            }
            // relation
            Expr::Lt(lhs, rhs, _) => {
                self.build_expr(builder, lhs, temp, frame);
                self.build_expr(builder, rhs, temp, frame);

                builder.i32_lt_s();
            }
            Expr::Gt(lhs, rhs, _) => {
                self.build_expr(builder, lhs, temp, frame);
                self.build_expr(builder, rhs, temp, frame);

                builder.i32_gt_s();
            }
            Expr::Le(lhs, rhs, _) => {
                self.build_expr(builder, lhs, temp, frame);
                self.build_expr(builder, rhs, temp, frame);

                builder.i32_le_s();
            }
            Expr::Ge(lhs, rhs, _) => {
                self.build_expr(builder, lhs, temp, frame);
                self.build_expr(builder, rhs, temp, frame);

                builder.i32_ge_s();
            }
            Expr::Eq(lhs, rhs, _) => {
                self.build_expr(builder, lhs, temp, frame);
                self.build_expr(builder, rhs, temp, frame);

                builder.i32_eq();
            }
            Expr::Ne(lhs, rhs, _) => {
                self.build_expr(builder, lhs, temp, frame);
                self.build_expr(builder, rhs, temp, frame);

                builder.i32_neq();
            }
            Expr::Plus(operand, _) => {
                self.build_expr(builder, operand, temp, frame);
            }
            Expr::Minus(operand, _) => {
                // There is no `ineg` instruction.
                builder.i32_const(0);
                self.build_expr(builder, operand, temp, frame);
                builder.i32_sub();
            }
            Expr::If {
                condition,
                then_body,
                else_body,
            } => {
                let result_type = wasm_type(&node.r#type);
                self.build_expr(builder, condition, temp, frame);

                let then_insts = {
                    let mut then_builder = wasm::Builders::instructions();

                    self.build_expr_nodes(&mut then_builder, then_body, temp, frame);

                    if result_type.is_none() {
                        self.drop_values(&mut then_builder, then_body);
                    }
                    then_builder.build()
                };

                let mut else_insts = None;

                if let Some(else_body) = else_body {
                    if !else_body.is_empty() {
                        let mut else_builder = wasm::Builders::instructions();

                        self.build_expr_nodes(&mut else_builder, else_body, temp, frame);

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
                self.build_expr(builder, head, temp, frame);

                let head_var = head_storage
                    .as_ref()
                    .expect("No allocation for head expression.")
                    .unwrap_local_variable();

                builder.local_set(&head_var.name);

                // Build all arms, including the `else` clause, in reverse order.
                let mut else_builder = wasm::Builders::instructions();

                if let Some(else_body) = else_body {
                    // `else` must not be empty.
                    self.build_expr_nodes(&mut else_builder, else_body, temp, frame);
                } else {
                    // if omitted, all arms must be exhausted.
                    // TODO: remove redundant `if`
                    else_builder.unreachable();
                }

                let else_insts = Some(else_builder.build());

                let arm_insts = arms.iter().rev().fold(else_insts, |acc, arm| {
                    let mut arm_builder = wasm::Builders::instructions();

                    arm_builder.comment(&format!("when {}", arm.pattern)).block(
                        wasm::Type::I32,
                        &mut |builder| {
                            // Pattern
                            builder.local_get(&head_var.name).note("head value");
                            self.build_case_pattern(
                                builder,
                                &arm.pattern,
                                &head.r#type,
                                temp,
                                frame,
                            );

                            // Build the guard expression if exists.
                            if let Some(ref condition) = arm.condition {
                                builder.i32_const(0);

                                self.build_expr(builder, condition, temp, frame);

                                builder
                                    .comment("if the guard condition fails, return with `0`")
                                    .i32_eqz()
                                    .br_if(0)
                                    .drop();
                            }
                        },
                    );

                    // 4. Build an `if` instruction for arm body and `else` to the next arm or `else` clause.
                    let then_insts = {
                        let mut then_builder = wasm::Builders::instructions();

                        self.build_expr_nodes(&mut then_builder, &arm.then_body, temp, frame);

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
                builder.comment(format!("let {} = ...", pattern));
                self.build_expr(builder, init, temp, frame);
                self.build_let_pattern(builder, pattern, &init.r#type, temp, frame);
            }
        };
    }

    fn build_let_pattern(
        &self,
        builder: &mut wasm::InstructionsBuilder,
        pattern: &parser::Pattern,
        init_type: &Rc<RefCell<Type>>,
        temp: &mut LocalVariables,
        frame: &StackFrame,
    ) {
        match pattern {
            parser::Pattern::Variable(ref name, ref binding) => {
                self.build_variable_pattern(builder, name, binding);
            }
            parser::Pattern::Integer(_) => {
                panic!("invalid local binding");
            }
            parser::Pattern::Array(patterns) => {
                // Currently, only the pattern `let [...x] = a` is allowed.
                if patterns.len() == 1 {
                    if let parser::Pattern::Rest {
                        ref name,
                        ref binding,
                        ..
                    } = patterns[0]
                    {
                        let binding = binding.borrow();
                        let var = binding
                            .storage
                            .as_ref()
                            .unwrap_or_else(|| panic!("Unallocated pattern `{}`", name))
                            .unwrap_local_variable();

                        builder.local_set(&var.name);
                        builder.i32_const_(1, "success value");
                        return;
                    }
                }

                todo!("Local binding with array pattern is not yet implemented. ")
            }
            parser::Pattern::Struct { fields, .. } => {
                self.build_struct_pattern(
                    builder,
                    &fields,
                    init_type,
                    temp,
                    frame,
                    |builder, field_pattern, field_type, temp, frame| {
                        self.build_let_pattern(builder, field_pattern, field_type, temp, frame);
                    },
                );
            }
            parser::Pattern::Rest { .. } => panic!("Rest pattern should not be here."),
        };
    }

    fn build_variable_pattern(
        &self,
        builder: &mut wasm::InstructionsBuilder,
        name: &str,
        binding: &Rc<RefCell<Binding>>,
    ) {
        let binding = binding.borrow();

        match &binding.storage {
            None => {
                // Ignored
                builder.drop_("ignored");
            }
            Some(storage) => {
                let var = storage.unwrap_local_variable();

                // set the result of head expression to the variable.
                builder.local_set_(&var.name, format!("capture variable `{}`", name));
            }
        };

        builder.i32_const_(1, "success value");
    }

    fn build_struct_pattern<F>(
        &self,
        builder: &mut wasm::InstructionsBuilder,
        fields: &[parser::PatternField],
        target_type: &Rc<RefCell<Type>>,
        temp: &mut LocalVariables,
        frame: &StackFrame,
        build_sub_pattern: F,
    ) where
        F: Fn(
            &mut wasm::InstructionsBuilder,
            &parser::Pattern,
            &Rc<RefCell<Type>>,
            &mut LocalVariables,
            &StackFrame,
        ),
    {
        temp.push_scope();

        let pattern_fields = fields
            .iter()
            .map(|f| (f.name.clone(), &f.pattern))
            .collect::<HashMap<_, _>>();

        // Load the memory index of the operand to a local variable
        let temp_memidx = temp.reserve_name_i32();

        builder
            .comment(&format!(
                "-- Destructuring assignment of {}",
                target_type.borrow()
            ))
            .local_set_(&temp_memidx, "memidx");

        // Calculate the offset
        let mut offset = 0;

        builder.labeled_block("struct_pattern", wasm::Type::I32, &mut |block| {
            let type_fields = self.unwrap_struct_type_fields(target_type);

            for (field_name, field_type) in type_fields {
                if let Some(pattern) = pattern_fields.get(&field_name) {
                    block.i32_const_(0, "failure value");

                    block.local_get(&temp_memidx).i32_load_(
                        offset,
                        format!("access .{} at base + {}", field_name, offset),
                    );

                    build_sub_pattern(block, pattern, &field_type, temp, frame);
                    block.i32_eqz().br_if(0).drop();
                }

                let field_size = wasm_type(&field_type).unwrap().num_bytes();
                offset += field_size;
            }

            block.i32_const_(1, "success value");
        });

        temp.pop_scope();
    }

    /// Build a pattern.
    /// - Assert: a value of target is on the top of the stack.
    /// - Push the value whether the pattern succeeded or not to the stack.
    fn build_case_pattern(
        &self,
        builder: &mut wasm::InstructionsBuilder,
        pattern: &parser::Pattern,
        target_type: &Rc<RefCell<Type>>,
        temp: &mut LocalVariables,
        frame: &StackFrame,
    ) {
        // 2. Each pattern will push the value whether pattern matched or not.
        match pattern {
            // variable pattern
            parser::Pattern::Variable(name, binding) => {
                self.build_variable_pattern(builder, name, binding);
            }
            parser::Pattern::Integer(i) => {
                // Constant pattern is semantically identical to `_ if head == pattern`,
                // but it can be more preciously handled in exhaustivity check.
                builder.i32_const_(*i, "constant pattern").i32_eq();
            }
            parser::Pattern::Array(ref patterns) => {
                temp.push_scope();

                let element_type = Type::unwrap_element_type_or_else(&target_type, |ty| {
                    panic!("Operand must be an array, but was {}", ty);
                });

                // Before entering the block, save the target value.
                let tmp_target = temp.reserve_name_i32();
                let tmp_memidx = temp.reserve_name_i32();
                let tmp_length = temp.reserve_name_i32();

                builder
                    .comment("load the reference (index, length) of an array to local variables")
                    .local_tee_(&tmp_target, "store target value to tmp")
                    .i32_load(0)
                    .local_set_(&tmp_memidx, "memory index")
                    .local_get_(&tmp_target, "target")
                    .i32_load(wasm::SIZE_BYTES)
                    .local_set_(&tmp_length, "length");

                // `block` [i32] ->
                // - Push the result `0`
                // - Push the length of head (`L1`) on the stack
                // - Compare the length of pattern (`L2`) and `L1`
                // - Break if `L1` != `l2`
                // - Push the element at index `0` of head on the stack
                // - Evaluate a child pattern at index `0`
                // - Break if the pattern match failed
                // - ... and so on
                // - Drop the result `0`
                // - Push the result `1`
                let ends_with_rest = patterns
                    .last()
                    .map_or(false, |x| matches!(x, parser::Pattern::Rest { .. }));
                let n_patterns = wasm::Size::try_from(patterns.len()).unwrap();

                builder.labeled_block("case_pattern", wasm::Type::I32, &mut |block| {
                    if ends_with_rest {
                        block
                            .comment(format!(
                                "Assert: target must have at least {} elements of {}",
                                patterns.len() - 1,
                                element_type.borrow(),
                            ))
                            .i32_const_(0, "failure value")
                            .local_get_(&tmp_length, "length")
                            .u32_const_(n_patterns - 1, "minimum required length")
                            .i32_lt_u()
                            .br_if(0)
                            .drop();
                    } else {
                        block
                            .comment(format!(
                                "Assert: target must be {}[{}]",
                                element_type.borrow(),
                                patterns.len()
                            ))
                            .i32_const_(0, "failure value")
                            .local_get_(&tmp_length, "length")
                            .u32_const_(n_patterns, "expected length")
                            .i32_neq()
                            .br_if(0)
                            .drop();
                    }

                    // If an empty array is given and the pattern is also empty array,
                    // the type of element is undetermined at this point.
                    if !patterns.is_empty() {
                        let element_size = wasm_type(&element_type).unwrap().num_bytes();

                        // Push the value of the element
                        for (i, pattern) in patterns.iter().enumerate() {
                            let i = wasm::Size::try_from(i).unwrap();

                            block.i32_const_(0, "failure value");

                            if let parser::Pattern::Rest {
                                reference_offset, ..
                            } = pattern
                            {
                                // If the target rest pattern is ignored, we can simply skip
                                // emitting code.
                                if let Some(reference_offset) = reference_offset {
                                    // Create a temporary reference to a sub array.
                                    let reference_offset = frame.static_size() - *reference_offset;

                                    block
                                        .comment(format!(
                                            "rest {}[{}...] with element size({})",
                                            element_type.borrow(),
                                            i,
                                            element_size
                                        ))
                                        .comment(format!("-- index + {}", i))
                                        .global_get("fp")
                                        .local_get_(&tmp_memidx, "memory index")
                                        .u32_const_(
                                            element_size * i,
                                            format!("element size ({}) * {}", element_size, i),
                                        )
                                        .i32_add()
                                        .i32_store_(
                                            reference_offset,
                                            "write memory index to reference",
                                        )
                                        .global_get("fp")
                                        .local_get_(&tmp_length, "length")
                                        .u32_const_(i, "i")
                                        .i32_sub()
                                        .i32_store_(
                                            reference_offset + wasm::SIZE_BYTES,
                                            "write length to reference",
                                        )
                                        .global_get("fp")
                                        .u32_const_(reference_offset, "reference")
                                        .i32_add();
                                }
                            } else {
                                // Access
                                // TODO: Don't emit anything for ignored pattern.
                                block
                                    .comment(format!(
                                        "access {}[{}] at memory index + element size({}) * index",
                                        element_type.borrow(),
                                        i,
                                        element_size
                                    ))
                                    .local_get_(&tmp_memidx, "memory index")
                                    .i32_load_(
                                        element_size * i,
                                        format!("element size ({}) * {}", element_size, i),
                                    );
                            }

                            self.build_case_pattern(block, pattern, &element_type, temp, frame);
                            block.i32_eqz().br_if(0).drop();
                        }
                    }

                    block.i32_const_(1, "success value");
                });

                temp.pop_scope();
            }
            parser::Pattern::Struct { ref fields, .. } => {
                self.build_struct_pattern(
                    builder,
                    &fields,
                    target_type,
                    temp,
                    frame,
                    |builder, field_pattern, field_type, temp, frame| {
                        self.build_case_pattern(builder, field_pattern, field_type, temp, frame);
                    },
                );
            }
            parser::Pattern::Rest {
                ref binding,
                ref name,
                ..
            } => {
                let binding = binding.borrow();

                match &binding.storage {
                    None => {
                        // Ignored
                        builder.i32_const_(1, "ignored. success value");
                    }
                    Some(storage) => {
                        let var = storage.unwrap_local_variable();

                        // set the result of head expression to the variable.
                        builder
                            .local_set_(&var.name, format!("capture variable `{}`", name))
                            .i32_const_(1, "success value");
                    }
                };
            }
        };
    }

    fn build_expr_nodes(
        &self,
        builder: &mut wasm::InstructionsBuilder,
        body: &[parser::Node],
        locals: &mut LocalVariables,
        frame: &StackFrame,
    ) {
        for node in body {
            self.build_expr(builder, node, locals, frame);
        }
    }

    fn unwrap_struct_type_fields(
        &self,
        ty: &Rc<RefCell<Type>>,
    ) -> Vec<(String, Rc<RefCell<Type>>)> {
        // Emit each field of a struct.
        // We have to align the order with that of the struct type fields.
        let struct_type = ty.borrow();
        let struct_type = struct_type
            .struct_type()
            .unwrap_or_else(|| panic!("Expected struct type, but was {}", struct_type));
        let mut type_fields = struct_type
            .fields()
            .iter()
            .map(|(name, ty)| (name.clone(), Rc::clone(ty)))
            .collect::<Vec<_>>();

        // To keep memory layout consistency, sort fields by name.
        type_fields.sort_by(|(a, _), (b, _)| a.partial_cmp(b).unwrap());
        type_fields
    }

    fn drop_values(&self, builder: &mut wasm::InstructionsBuilder, body: &[parser::Node]) {
        let node = match body.last() {
            None => return,
            Some(node) => node,
        };

        if wasm_type(&node.r#type).is_some() {
            // Currently, only one value will be left on the stack.
            builder.drop();
        }
    }
}
