use std::mem;

// The length of the vector always is a multiple of the WebAssembly page size,
// which is defined to be the constant 65536 – abbreviated 64Ki.
// Like in a memory type, the maximum size in a memory instance is given in units of
// this page size.
//
// https://webassembly.github.io/spec/core/exec/runtime.html#page-size
pub const PAGE_SIZE: u32 = 65536;

/// `usize` for WebAssembly.
///
/// the largest amount of memory possible with 32-bit pointers,
/// which is what WebAssembly currently supports
pub type Size = u32;

/// The size of `Size` type in bytes.
pub const SIZE_BYTES: Size = mem::size_of::<Size>() as Size;

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Type {
    I32,
    I64,
}

impl Type {
    fn numeric_type_str(ty: &Type) -> &'static str {
        match ty {
            Type::I32 => "i32",
            Type::I64 => "i64",
        }
    }

    pub fn num_bytes(&self) -> Size {
        match self {
            Type::I32 => 4,
            Type::I64 => 8,
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Instruction {
    // Numeric instructions.
    I32Const(i32),
    I32Eqz,
    I32Eq,
    I32Neq,
    I32LtS,
    I32LtU,
    I32GtS,
    I32GtU,
    I32LeS,
    I32LeU,
    I32GeS,
    I32GeU,
    I32Add,
    I32Sub,
    I32Mul,
    I32DivS,
    I32DivU,
    I32RemS,
    I32RemU,
    I32And,
    I32Or,

    // Parametric instructions.
    Drop,
    Select,

    // Variable instructions
    LocalGet(Index),
    LocalSet(Index),
    LocalTee(Index),
    GlobalGet(Index),
    GlobalSet(Index),

    // Memory instructions
    I32Load(MemArg),
    I32Store(MemArg),

    // Control Instructions
    Unreachable,
    Call(Index),
    If {
        result_type: Option<Type>,
        then: Vec<Instruction>,
        r#else: Option<Vec<Instruction>>,
    },
    Block {
        result_type: Option<Type>,
        body: Vec<Instruction>,
    },
    Br(Index),
    BrIf(Index),

    // For unsigned values
    U32Const(u32),

    // line comment
    Comment(String),
}

#[derive(Debug, PartialEq, Clone)]
pub struct Identifier(String);

// https://webassembly.github.io/spec/core/text/modules.html#text-localidx
#[derive(Debug, PartialEq, Clone)]
pub enum Index {
    Id(Identifier),
    Index(Size),
}

#[derive(Debug, Default, PartialEq, Clone)]
pub struct MemArg {
    offset: Option<Size>,
    align: Option<u32>,
}

#[derive(Debug, Default)]
pub struct Module {
    pub imports: Vec<Import>,
    pub globals: Vec<Global>,
    pub data_segments: Vec<DataSegment>,
    pub functions: Vec<Function>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Import {
    module: String,
    name: String,
    desc: ImportDescriptor,
}

#[derive(Debug, PartialEq, Clone)]
pub enum ImportDescriptor {
    Function {
        id: Option<Identifier>,
        params: Vec<Type>,
        result_type: Type,
    },
    Memory {
        id: Option<Identifier>,
        min: i32,
        max: Option<i32>,
    },
    Global {
        id: Option<Identifier>,
        r#type: Type,
        mutable: bool,
    },
}

#[derive(Debug, PartialEq, Clone)]
pub struct Global {
    id: Option<Identifier>,
    r#type: Type,
    mutable: bool,
    init: Vec<Instruction>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct DataSegment {
    offset: Size,
    bytes: Vec<u8>,
}

#[derive(Debug, PartialEq)]
pub struct Function {
    export: Option<String>,
    id: Option<Identifier>,
    params: Vec<Param>,
    result_type: Option<Type>,
    locals: Vec<Local>,
    body: Vec<Instruction>,
}

#[derive(Debug, PartialEq)]
pub struct Param {
    id: Option<Identifier>,
    r#type: Type,
}

#[derive(Debug, PartialEq)]
pub struct Local {
    id: Option<Identifier>,
    r#type: Type,
}

impl Module {
    pub fn new() -> Self {
        Self::default()
    }
}

pub struct Builders {}

impl Builders {
    pub fn import() -> ImportBuilder {
        ImportBuilder::default()
    }

    pub fn memory_desc() -> MemoryDescriptorBuilder {
        MemoryDescriptorBuilder::default()
    }

    pub fn global_desc() -> GlobalDescriptorBuilder {
        GlobalDescriptorBuilder::default()
    }

    pub fn func_desc() -> FunctionDescriptorBuilder {
        FunctionDescriptorBuilder::default()
    }

    pub fn global() -> GlobalBuilder {
        GlobalBuilder::default()
    }

    pub fn data_segment() -> DataSegmentBuilder {
        DataSegmentBuilder::default()
    }

    pub fn function() -> FunctionBuilder {
        FunctionBuilder::default()
    }

    pub fn instructions() -> InstructionsBuilder {
        InstructionsBuilder::default()
    }
}

#[derive(Debug, Default)]
pub struct ImportBuilder {
    module: Option<String>,
    name: Option<String>,
    desc: Option<ImportDescriptor>,
}

impl ImportBuilder {
    pub fn module<T: AsRef<str>>(&mut self, module: T) -> &mut Self {
        self.module = Some(module.as_ref().to_string());
        self
    }

    pub fn name<T: AsRef<str>>(&mut self, name: T) -> &mut Self {
        self.name = Some(name.as_ref().to_string());
        self
    }

    pub fn desc(&mut self, desc: ImportDescriptor) -> &mut Self {
        self.desc = Some(desc);
        self
    }

    pub fn build(&mut self) -> Import {
        Import {
            module: self.module.take().unwrap(),
            name: self.name.take().unwrap(),
            desc: self.desc.take().unwrap(),
        }
    }
}

#[derive(Debug, Default)]
pub struct MemoryDescriptorBuilder {
    id: Option<Identifier>,
    min: Option<i32>,
    max: Option<i32>,
}

impl MemoryDescriptorBuilder {
    pub fn id<T: AsRef<str>>(&mut self, id: T) -> &mut Self {
        self.id = Some(Identifier(id.as_ref().to_string()));
        self
    }

    pub fn min(&mut self, min: i32) -> &mut Self {
        self.min = Some(min);
        self
    }

    pub fn max(&mut self, max: i32) -> &mut Self {
        self.max = Some(max);
        self
    }

    pub fn build(&mut self) -> ImportDescriptor {
        ImportDescriptor::Memory {
            id: self.id.take(),
            min: self.min.unwrap(),
            max: self.max,
        }
    }
}

#[derive(Debug, Default)]
pub struct GlobalDescriptorBuilder {
    id: Option<Identifier>,
    r#type: Option<Type>,
    mutable: bool,
}

impl GlobalDescriptorBuilder {
    pub fn id<T: AsRef<str>>(&mut self, id: T) -> &mut Self {
        self.id = Some(Identifier(id.as_ref().to_string()));
        self
    }

    pub fn r#type(&mut self, ty: Type) -> &mut Self {
        self.r#type = Some(ty);
        self
    }

    pub fn mutable(&mut self, mutable: bool) -> &mut Self {
        self.mutable = mutable;
        self
    }

    pub fn build(&mut self) -> ImportDescriptor {
        ImportDescriptor::Global {
            id: self.id.take(),
            r#type: self.r#type.unwrap(),
            mutable: self.mutable,
        }
    }
}

#[derive(Debug, Default)]
pub struct FunctionDescriptorBuilder {
    id: Option<Identifier>,
    params: Vec<Type>,
    result_type: Option<Type>,
}

impl FunctionDescriptorBuilder {
    pub fn id<T: AsRef<str>>(&mut self, id: T) -> &mut Self {
        self.id = Some(Identifier(id.as_ref().to_string()));
        self
    }

    pub fn param(&mut self, ty: Type) -> &mut Self {
        self.params.push(ty);
        self
    }

    pub fn result_type(&mut self, ty: Type) -> &mut Self {
        self.result_type = Some(ty);
        self
    }

    pub fn build(&mut self) -> ImportDescriptor {
        ImportDescriptor::Function {
            id: self.id.take(),
            params: mem::take(&mut self.params),
            result_type: self.result_type.unwrap(),
        }
    }
}

#[derive(Debug, Default)]
pub struct DataSegmentBuilder {
    offset: Option<Size>,
    bytes: Option<Vec<u8>>,
}

impl DataSegmentBuilder {
    pub fn offset(&mut self, offset: Size) -> &mut Self {
        self.offset = Some(offset);
        self
    }

    pub fn bytes(&mut self, bytes: Vec<u8>) -> &mut Self {
        self.bytes = Some(bytes);
        self
    }

    pub fn build(&mut self) -> DataSegment {
        let bytes = self.bytes.take().unwrap();

        DataSegment {
            offset: self.offset.unwrap(),
            bytes,
        }
    }
}

#[derive(Debug, Default)]
pub struct GlobalBuilder {
    id: Option<Identifier>,
    r#type: Option<Type>,
    mutable: bool,
    init: Option<Vec<Instruction>>,
}

impl GlobalBuilder {
    pub fn id<T: AsRef<str>>(&mut self, id: T) -> &mut Self {
        self.id = Some(Identifier(id.as_ref().to_string()));
        self
    }

    pub fn r#type(&mut self, ty: Type) -> &mut Self {
        self.r#type = Some(ty);
        self
    }

    pub fn mutable(&mut self, mutable: bool) -> &mut Self {
        self.mutable = mutable;
        self
    }

    pub fn init(&mut self, instructions: Vec<Instruction>) -> &mut Self {
        self.init = Some(instructions);
        self
    }

    pub fn build(&mut self) -> Global {
        Global {
            id: self.id.take(),
            r#type: self.r#type.take().unwrap(),
            mutable: self.mutable,
            init: mem::take(self.init.take().unwrap().as_mut()),
        }
    }
}

#[derive(Debug, Default)]
pub struct FunctionBuilder {
    export: Option<String>,
    id: Option<Identifier>,
    params: Vec<Param>,
    locals: Vec<Local>,
    result_type: Option<Type>,
    body: Vec<Instruction>,
}

impl FunctionBuilder {
    pub fn export<T: AsRef<str>>(&mut self, export: T) -> &mut Self {
        self.export = Some(export.as_ref().to_string());
        self
    }

    pub fn id<T: AsRef<str>>(&mut self, id: T) -> &mut Self {
        self.id = Some(Identifier(id.as_ref().to_string()));
        self
    }

    pub fn param(&mut self, ty: Type) -> &mut Self {
        self.params.push(Param {
            id: None,
            r#type: ty,
        });
        self
    }

    pub fn named_param<T: AsRef<str>>(&mut self, name: T, ty: Type) -> &mut Self {
        self.params.push(Param {
            id: Some(Identifier(name.as_ref().to_string())),
            r#type: ty,
        });
        self
    }

    pub fn local(&mut self, ty: Type) -> &mut Self {
        self.locals.push(Local {
            id: None,
            r#type: ty,
        });
        self
    }

    pub fn named_local<T: AsRef<str>>(&mut self, name: T, ty: Type) -> &mut Self {
        self.locals.push(Local {
            id: Some(Identifier(name.as_ref().to_string())),
            r#type: ty,
        });
        self
    }

    pub fn result_type(&mut self, ty: Type) -> &mut Self {
        self.result_type = Some(ty);
        self
    }

    pub fn body(&mut self, insts: Vec<Instruction>) -> &mut Self {
        self.body = insts;
        self
    }

    pub fn build(&mut self) -> Function {
        Function {
            export: self.export.take(),
            id: self.id.take(),
            result_type: self.result_type,
            params: mem::take(&mut self.params),
            locals: mem::take(&mut self.locals),
            body: mem::take(&mut self.body),
        }
    }
}

#[derive(Debug, Default)]
pub struct InstructionsBuilder {
    instructions: Vec<Instruction>,
}

impl InstructionsBuilder {
    pub fn i32_const(&mut self, n: i32) -> &mut Self {
        self.instructions.push(Instruction::I32Const(n));
        self
    }

    pub fn u32_const(&mut self, n: u32) -> &mut Self {
        self.instructions.push(Instruction::U32Const(n));
        self
    }

    pub fn i32_eqz(&mut self) -> &mut Self {
        self.instructions.push(Instruction::I32Eqz);
        self
    }

    pub fn i32_eq(&mut self) -> &mut Self {
        self.instructions.push(Instruction::I32Eq);
        self
    }

    pub fn i32_neq(&mut self) -> &mut Self {
        self.instructions.push(Instruction::I32Neq);
        self
    }

    pub fn i32_lt_s(&mut self) -> &mut Self {
        self.instructions.push(Instruction::I32LtS);
        self
    }

    pub fn i32_lt_u(&mut self) -> &mut Self {
        self.instructions.push(Instruction::I32LtU);
        self
    }

    pub fn i32_gt_s(&mut self) -> &mut Self {
        self.instructions.push(Instruction::I32GtS);
        self
    }

    pub fn i32_gt_u(&mut self) -> &mut Self {
        self.instructions.push(Instruction::I32GtU);
        self
    }

    pub fn i32_le_s(&mut self) -> &mut Self {
        self.instructions.push(Instruction::I32LeS);
        self
    }

    pub fn i32_le_u(&mut self) -> &mut Self {
        self.instructions.push(Instruction::I32LeU);
        self
    }

    pub fn i32_ge_s(&mut self) -> &mut Self {
        self.instructions.push(Instruction::I32GeS);
        self
    }

    pub fn i32_ge_u(&mut self) -> &mut Self {
        self.instructions.push(Instruction::I32GeU);
        self
    }

    pub fn i32_add(&mut self) -> &mut Self {
        self.instructions.push(Instruction::I32Add);
        self
    }

    pub fn i32_sub(&mut self) -> &mut Self {
        self.instructions.push(Instruction::I32Sub);
        self
    }

    pub fn i32_mul(&mut self) -> &mut Self {
        self.instructions.push(Instruction::I32Mul);
        self
    }

    pub fn i32_div_s(&mut self) -> &mut Self {
        self.instructions.push(Instruction::I32DivS);
        self
    }

    pub fn i32_div_u(&mut self) -> &mut Self {
        self.instructions.push(Instruction::I32DivU);
        self
    }

    pub fn i32_rem_s(&mut self) -> &mut Self {
        self.instructions.push(Instruction::I32RemS);
        self
    }

    pub fn i32_rem_u(&mut self) -> &mut Self {
        self.instructions.push(Instruction::I32RemU);
        self
    }

    pub fn i32_and(&mut self) -> &mut Self {
        self.instructions.push(Instruction::I32And);
        self
    }

    pub fn i32_or(&mut self) -> &mut Self {
        self.instructions.push(Instruction::I32Or);
        self
    }

    pub fn drop(&mut self) -> &mut Self {
        self.instructions.push(Instruction::Drop);
        self
    }

    pub fn select(&mut self) -> &mut Self {
        self.instructions.push(Instruction::Select);
        self
    }

    pub fn local_get<T: AsRef<str>>(&mut self, name: T) -> &mut Self {
        self.instructions
            .push(Instruction::LocalGet(Index::Id(Identifier(
                name.as_ref().to_string(),
            ))));
        self
    }

    pub fn local_set<T: AsRef<str>>(&mut self, name: T) -> &mut Self {
        self.instructions
            .push(Instruction::LocalSet(Index::Id(Identifier(
                name.as_ref().to_string(),
            ))));
        self
    }

    pub fn local_tee<T: AsRef<str>>(&mut self, name: T) -> &mut Self {
        self.instructions
            .push(Instruction::LocalTee(Index::Id(Identifier(
                name.as_ref().to_string(),
            ))));
        self
    }

    pub fn global_get<T: AsRef<str>>(&mut self, name: T) -> &mut Self {
        self.instructions
            .push(Instruction::GlobalGet(Index::Id(Identifier(
                name.as_ref().to_string(),
            ))));
        self
    }

    pub fn global_set<T: AsRef<str>>(&mut self, name: T) -> &mut Self {
        self.instructions
            .push(Instruction::GlobalSet(Index::Id(Identifier(
                name.as_ref().to_string(),
            ))));
        self
    }

    pub fn i32_load(&mut self, offset: Size) -> &mut Self {
        self.instructions.push(Instruction::I32Load(MemArg {
            offset: Some(offset),
            align: None,
        }));
        self
    }

    pub fn i32_store(&mut self, offset: Size) -> &mut Self {
        self.instructions.push(Instruction::I32Store(MemArg {
            offset: Some(offset),
            align: None,
        }));
        self
    }

    pub fn unreachable(&mut self) -> &mut Self {
        self.instructions.push(Instruction::Unreachable);
        self
    }

    pub fn call<T: AsRef<str>>(&mut self, name: T) -> &mut Self {
        self.instructions
            .push(Instruction::Call(Index::Id(Identifier(
                name.as_ref().to_string(),
            ))));
        self
    }

    pub fn br(&mut self, index: Size) -> &mut Self {
        self.instructions.push(Instruction::Br(Index::Index(index)));
        self
    }

    pub fn br_if(&mut self, index: Size) -> &mut Self {
        self.instructions
            .push(Instruction::BrIf(Index::Index(index)));
        self
    }

    pub fn comment<T: AsRef<str>>(&mut self, comment: T) -> &mut Self {
        self.instructions
            .push(Instruction::Comment(comment.as_ref().to_string()));
        self
    }

    pub fn block<F>(&mut self, result_type: Option<Type>, builder_fn: &mut F) -> &mut Self
    where
        F: FnMut(&mut Self),
    {
        let mut builder = Self::default();

        builder_fn(&mut builder);

        let block = Instruction::Block {
            result_type,
            body: builder.build(),
        };

        self.push(block)
    }

    pub fn push(&mut self, instruction: Instruction) -> &mut Self {
        self.instructions.push(instruction);
        self
    }

    pub fn build(&mut self) -> Vec<Instruction> {
        mem::take(&mut self.instructions)
    }
}

#[derive(Debug)]
pub struct Printer {
    buffer: String,
    level: i32,
    pub indent: i32,
    pub pretty: bool,
    indent_no_newline: bool,
}

impl ToString for Printer {
    fn to_string(&self) -> String {
        self.buffer.clone()
    }
}

impl Default for Printer {
    fn default() -> Self {
        Self::new()
    }
}

impl Printer {
    pub fn print(module: &Module) -> String {
        let mut printer = Printer::new();

        printer.write_module(module);
        printer.to_string()
    }

    pub fn new() -> Self {
        Self {
            buffer: String::new(),
            level: 0,
            indent: 2,
            pretty: false,
            indent_no_newline: false,
        }
    }

    pub fn as_str(&self) -> &str {
        self.buffer.as_str()
    }

    fn indent(&mut self) {
        if self.level == 0 {
            return;
        }
        if self.pretty {
            if !self.indent_no_newline {
                self.buffer.push('\n');
            }
            self.indent_no_newline = false;

            for _ in 0..self.level {
                for _ in 0..self.indent {
                    self.buffer.push(' ');
                }
            }
        } else {
            self.buffer.push(' ');
        }
    }

    fn push_indent(&mut self) {
        self.level += 1;
    }

    fn pop_indent(&mut self) {
        self.level += -1;
    }

    fn close_indent(&mut self) {
        self.pop_indent();
        self.buffer.push(')');
    }

    fn start_plain(&mut self) {
        self.indent();
        if !self.pretty {
            self.buffer.push('(');
        }
    }

    fn end_plain(&mut self) {
        if !self.pretty {
            self.buffer.push(')');
        }
    }

    pub fn write_module(&mut self, module: &Module) {
        self.indent();
        self.buffer.push('(');
        self.buffer.push_str("module");
        self.push_indent();
        self.write_imports(&module.imports);
        self.write_data_segments(&module.data_segments);
        self.write_globals(&module.globals);
        self.write_functions(&module.functions);
        self.close_indent();
    }

    fn write_imports(&mut self, imports: &[Import]) {
        for import in imports {
            self.write_import(import);
        }
    }

    fn write_import(&mut self, import: &Import) {
        self.indent();
        self.buffer.push('(');
        self.buffer.push_str("import");
        self.buffer.push(' ');
        self.write_string(&import.module);
        self.buffer.push(' ');
        self.write_string(&import.name);
        self.buffer.push(' ');
        self.write_import_descriptor(&import.desc);
        self.buffer.push(')');
    }

    fn write_import_descriptor(&mut self, desc: &ImportDescriptor) {
        match desc {
            ImportDescriptor::Function {
                id,
                params,
                result_type,
            } => {
                self.buffer.push('(');
                self.buffer.push_str("func");

                if let Some(id) = id {
                    self.buffer.push(' ');
                    self.write_identifier(id);
                }

                for param in params {
                    self.buffer.push(' ');
                    self.write_param(&Param {
                        id: None,
                        r#type: *param,
                    });
                }

                self.buffer.push(' ');
                self.write_return_type(result_type);

                self.buffer.push(')');
            }
            ImportDescriptor::Memory { id, min, max } => {
                self.buffer.push('(');
                self.buffer.push_str("memory");

                if let Some(id) = id {
                    self.buffer.push(' ');
                    self.write_identifier(id);
                }

                self.buffer.push(' ');
                self.buffer.push_str(&format!("{}", min));
                max.iter().for_each(|max| {
                    self.buffer.push(' ');
                    self.buffer.push_str(&format!("{}", max));
                });
                self.buffer.push(')');
            }
            ImportDescriptor::Global {
                id,
                r#type,
                mutable,
            } => {
                self.buffer.push('(');
                self.buffer.push_str("global");

                if let Some(id) = id {
                    self.buffer.push(' ');
                    self.write_identifier(id);
                }

                self.buffer.push(' ');
                if *mutable {
                    self.buffer.push('(');
                    self.buffer.push_str("mut");
                    self.buffer.push(' ');
                    self.buffer.push_str(Type::numeric_type_str(r#type));
                    self.buffer.push(')');
                } else {
                    self.buffer.push_str(Type::numeric_type_str(r#type));
                }
                self.buffer.push(')');
            }
        }
    }

    fn write_param(&mut self, param: &Param) {
        self.buffer.push('(');
        self.buffer.push_str("param");
        self.buffer.push(' ');
        param.id.iter().for_each(|id| {
            self.write_identifier(id);
            self.buffer.push(' ');
        });
        self.buffer.push_str(Type::numeric_type_str(&param.r#type));
        self.buffer.push(')');
    }

    fn write_local(&mut self, local: &Local) {
        self.buffer.push('(');
        self.buffer.push_str("local");
        self.buffer.push(' ');
        local.id.iter().for_each(|id| {
            self.write_identifier(id);
            self.buffer.push(' ');
        });
        self.buffer.push_str(Type::numeric_type_str(&local.r#type));
        self.buffer.push(')');
    }

    fn write_return_type(&mut self, ty: &Type) {
        self.buffer.push('(');
        self.buffer.push_str("result");
        self.buffer.push(' ');
        self.buffer.push_str(Type::numeric_type_str(&ty));
        self.buffer.push(')');
    }

    fn write_data_segments(&mut self, data_segments: &[DataSegment]) {
        for data_segment in data_segments {
            self.write_data_segment(data_segment);
        }
    }

    fn write_globals(&mut self, globals: &[Global]) {
        for global in globals {
            self.write_global(global);
        }
    }

    fn write_data_segment(&mut self, data_segment: &DataSegment) {
        self.indent();
        self.buffer.push('(');
        self.buffer.push_str("data");
        self.buffer.push(' ');
        self.buffer
            .push_str(&format!("(i32.const {})", data_segment.offset));
        self.buffer.push(' ');
        self.write_bytes(&data_segment.bytes);
        self.buffer.push(')');
    }

    fn write_global(&mut self, global: &Global) {
        self.indent();

        self.buffer.push('(');
        self.buffer.push_str("global");

        if let Some(id) = &global.id {
            self.buffer.push(' ');
            self.write_identifier(id);
        }

        self.buffer.push(' ');
        if global.mutable {
            self.buffer.push('(');
            self.buffer.push_str("mut");
            self.buffer.push(' ');
            self.buffer.push_str(Type::numeric_type_str(&global.r#type));
            self.buffer.push(')');
        } else {
            self.buffer.push_str(Type::numeric_type_str(&global.r#type));
        }

        // Pretty printing should be temporary disabled.
        let pretty = self.pretty;
        self.pretty = false;

        for instruction in &global.init {
            self.write_instruction(instruction);
        }
        self.buffer.push(')');

        self.pretty = pretty;
    }

    fn write_functions(&mut self, functions: &[Function]) {
        for function in functions {
            self.write_function(function);
        }
    }

    fn write_function(&mut self, function: &Function) {
        self.indent();
        self.buffer.push('(');
        self.buffer.push_str("func");

        if let Some(id) = &function.id {
            self.buffer.push(' ');
            self.write_identifier(id)
        }

        if let Some(export) = &function.export {
            self.buffer.push(' ');
            self.buffer.push('(');
            self.buffer.push_str("export");
            self.buffer.push(' ');
            self.write_string(export);
            self.buffer.push(')');
        }

        // params
        for param in &function.params {
            self.buffer.push(' ');
            self.write_param(param);
        }

        self.buffer.push(' ');
        if let Some(result_type) = function.result_type {
            self.write_return_type(&result_type);
        }

        // locals
        for local in &function.locals {
            self.buffer.push(' ');
            self.write_local(local);
        }

        self.push_indent();
        for instruction in &function.body {
            self.write_instruction(instruction);
        }
        self.close_indent();
    }

    fn write_identifier(&mut self, id: &Identifier) {
        self.buffer.push('$');
        self.buffer.push_str(&id.0);
    }

    fn write_index(&mut self, idx: &Index) {
        match idx {
            Index::Id(id) => self.write_identifier(id),
            Index::Index(i) => self.buffer.push_str(&format!("{}", i)),
        }
    }

    fn write_string(&mut self, string: &str) {
        self.write_bytes(string.as_bytes());
    }

    fn write_bytes(&mut self, bytes: &[u8]) {
        self.buffer.push('"');
        self.write_bytes_part(bytes);
        self.buffer.push('"');
    }

    fn write_bytes_part(&mut self, bytes: &[u8]) {
        for b in bytes {
            match *b as char {
                '"' => self.buffer.push_str("\\\""),
                '\t' => self.buffer.push_str("\\t"),
                '\n' => self.buffer.push_str("\\n"),
                '\r' => self.buffer.push_str("\\r"),
                '\\' => self.buffer.push_str("\\\\"),
                '′' => self.buffer.push_str("\\′"),
                _ => {
                    if (0x20..0x7f).contains(b) {
                        // printable
                        self.buffer.push(*b as char);
                    } else {
                        self.buffer.push_str(format!("\\{:02x}", b).as_ref())
                    }
                }
            };
        }
    }

    fn write_instructions(&mut self, instructions: &[Instruction]) {
        for instruction in instructions {
            self.write_instruction(instruction);
        }
    }

    fn write_instruction(&mut self, instruction: &Instruction) {
        match instruction {
            Instruction::I32Const(n) => {
                self.start_plain();
                self.buffer.push_str(&format!("i32.const {}", n));
                self.end_plain();
            }
            Instruction::U32Const(n) => {
                self.start_plain();
                self.buffer.push_str(&format!("i32.const {}", n));
                self.end_plain();
            }
            Instruction::I32Eqz => {
                self.start_plain();
                self.buffer.push_str(Type::numeric_type_str(&Type::I32));
                self.buffer.push_str(".eqz");
                self.end_plain();
            }
            Instruction::I32Eq => {
                self.start_plain();
                self.buffer.push_str(Type::numeric_type_str(&Type::I32));
                self.buffer.push_str(".eq");
                self.end_plain();
            }
            Instruction::I32Neq => {
                self.start_plain();
                self.buffer.push_str("i32.ne");
                self.end_plain();
            }
            Instruction::I32LtS => {
                self.start_plain();
                self.buffer.push_str("i32.lt_s");
                self.end_plain();
            }
            Instruction::I32LtU => {
                self.start_plain();
                self.buffer.push_str("i32.lt_u");
                self.end_plain();
            }
            Instruction::I32GtS => {
                self.start_plain();
                self.buffer.push_str("i32.ge_s");
                self.end_plain();
            }
            Instruction::I32GtU => {
                self.start_plain();
                self.buffer.push_str("i32.gt_u");
                self.end_plain();
            }
            Instruction::I32LeS => {
                self.start_plain();
                self.buffer.push_str("i32.le_s");
                self.end_plain();
            }
            Instruction::I32LeU => {
                self.start_plain();
                self.buffer.push_str("i32.le_u");
                self.end_plain();
            }
            Instruction::I32GeS => {
                self.start_plain();
                self.buffer.push_str("i32.ge_s");
                self.end_plain();
            }
            Instruction::I32GeU => {
                self.start_plain();
                self.buffer.push_str("i32.ge_u");
                self.end_plain();
            }
            Instruction::I32Add => {
                self.start_plain();
                self.buffer.push_str("i32.add");
                self.end_plain();
            }
            Instruction::I32Sub => {
                self.start_plain();
                self.buffer.push_str("i32.sub");
                self.end_plain();
            }
            Instruction::I32Mul => {
                self.start_plain();
                self.buffer.push_str("i32.mul");
                self.end_plain();
            }
            Instruction::I32DivS => {
                self.start_plain();
                self.buffer.push_str("i32.div_s");
                self.end_plain();
            }
            Instruction::I32DivU => {
                self.start_plain();
                self.buffer.push_str("i32.div_u");
                self.end_plain();
            }
            Instruction::I32RemS => {
                self.start_plain();
                self.buffer.push_str("i32.rem_s");
                self.end_plain();
            }
            Instruction::I32RemU => {
                self.start_plain();
                self.buffer.push_str("i32.rem_u");
                self.end_plain();
            }
            Instruction::I32And => {
                self.start_plain();
                self.buffer.push_str("i32.and");
                self.end_plain();
            }
            Instruction::I32Or => {
                self.start_plain();
                self.buffer.push_str("i32.or");
                self.end_plain();
            }
            Instruction::Drop => {
                self.start_plain();
                self.buffer.push_str("drop");
                self.end_plain();
            }
            Instruction::Select => {
                self.start_plain();
                self.buffer.push_str("select");
                self.end_plain();
            }
            Instruction::LocalGet(idx) => {
                self.start_plain();
                self.buffer.push_str("local.get ");
                self.write_index(&idx);
                self.end_plain();
            }
            Instruction::LocalSet(idx) => {
                self.start_plain();
                self.buffer.push_str("local.set ");
                self.write_index(&idx);
                self.end_plain();
            }
            Instruction::LocalTee(idx) => {
                self.start_plain();
                self.buffer.push_str("local.tee ");
                self.write_index(&idx);
                self.end_plain();
            }
            Instruction::GlobalGet(idx) => {
                self.start_plain();
                self.buffer.push_str("global.get ");
                self.write_index(&idx);
                self.end_plain();
            }
            Instruction::GlobalSet(idx) => {
                self.start_plain();
                self.buffer.push_str("global.set ");
                self.write_index(&idx);
                self.end_plain();
            }
            Instruction::Unreachable => {
                self.start_plain();
                self.buffer.push_str("unreachable");
                self.end_plain();
            }
            Instruction::Call(idx) => {
                self.start_plain();
                self.buffer.push_str("call ");
                self.write_index(&idx);
                self.end_plain();
            }
            Instruction::I32Load(memarg) => {
                self.start_plain();
                self.buffer.push_str("i32.load");

                match memarg.offset {
                    Some(offset) if offset > 0 => {
                        self.buffer.push(' ');
                        self.buffer.push_str(&format!("offset={} ", offset));
                    }
                    _ => {}
                }

                if let Some(align) = memarg.align {
                    self.buffer.push(' ');
                    self.buffer.push_str(&format!("align={} ", align));
                }

                self.end_plain();
            }
            Instruction::I32Store(memarg) => {
                self.start_plain();
                self.buffer.push_str("i32.store");

                match memarg.offset {
                    Some(offset) if offset > 0 => {
                        self.buffer.push(' ');
                        self.buffer.push_str(&format!("offset={} ", offset));
                    }
                    _ => {}
                }

                if let Some(align) = memarg.align {
                    self.buffer.push(' ');
                    self.buffer.push_str(&format!("align={} ", align));
                }

                self.end_plain();
            }
            Instruction::If {
                ref result_type,
                ref then,
                ref r#else,
            } => {
                self.indent();
                self.buffer.push_str("(if ");
                if let Some(result_type) = result_type {
                    self.write_return_type(result_type);
                }

                self.push_indent();
                self.indent();
                self.buffer.push_str("(then ");
                self.push_indent();
                self.write_instructions(then);
                self.close_indent();

                if let Some(instructions) = r#else {
                    self.indent();
                    self.buffer.push_str("(else ");
                    self.push_indent();
                    self.write_instructions(instructions);
                    self.close_indent();
                }

                self.close_indent();
            }
            Instruction::Br(idx) => {
                self.start_plain();
                self.buffer.push_str("br ");
                self.write_index(&idx);
                self.end_plain();
            }
            Instruction::BrIf(idx) => {
                self.start_plain();
                self.buffer.push_str("br_if ");
                self.write_index(&idx);
                self.end_plain();
            }
            Instruction::Block {
                ref result_type,
                ref body,
            } => {
                self.indent();
                self.buffer.push_str("(block ");
                if let Some(result_type) = result_type {
                    self.write_return_type(result_type);
                }

                self.push_indent();
                self.write_instructions(body);
                self.close_indent();
            }
            Instruction::Comment(comment) => {
                self.indent();
                self.buffer.push_str(";; ");
                self.buffer.push_str(comment);
                self.buffer.push('\n');
                self.indent_no_newline = true;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constant_value() {
        let mut printer = Printer::new();

        printer.write_instruction(&Instruction::I32Const(0));

        assert_eq!(printer.as_str(), "(i32.const 0)");
    }

    #[test]
    fn module1() {
        let mut module = Module::new();

        module.imports.push(Import {
            module: "test".to_string(),
            name: "jj".to_string(),
            desc: ImportDescriptor::Function {
                id: Some(Identifier("print".to_string())),
                params: vec![Type::I32],
                result_type: Type::I32,
            },
        });

        assert_eq!(
            Printer::print(&module),
            "(module (import \"test\" \"jj\" (func $print (param i32) (result i32))))"
        );
    }

    #[test]
    fn function1() {
        let mut module = Module::new();

        module.functions.push(
            Builders::function()
                .id("foo")
                .named_param("x", Type::I32)
                .named_local("y", Type::I32)
                .result_type(Type::I32)
                .body(
                    Builders::instructions()
                        .local_get("x")
                        .local_get("y")
                        .i32_add()
                        .build(),
                )
                .build(),
        );

        assert_eq!(
            Printer::print(&module),
            "(module (func $foo (param $x i32) (result i32) (local $y i32) (local.get $x) (local.get $y) (i32.add)))"
        );
    }
}
