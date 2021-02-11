use super::parser;
use parser::{Expr, Node};

pub struct WasmWriter {
    level: i32,
    buffer: String,
}

impl WasmWriter {
    fn bytes_sequence(buffer: &mut String, bytes: &[u8]) {
        for &b in bytes {
            if (0x20..0x7f).contains(&b) {
                // printable
                buffer.push(b as char);
            } else {
                buffer.push_str(format!("\\{:02x}", b).as_ref())
            }
        }
    }
}

impl WasmWriter {
    pub fn new() -> WasmWriter {
        WasmWriter {
            level: 0,
            buffer: String::new(),
        }
    }

    pub fn code(&self) -> &str {
        &self.buffer
    }

    pub fn write<S: AsRef<str>>(&mut self, asm: S) {
        self.indent();
        self.buffer.push_str(asm.as_ref());
        self.buffer.push('\n');
    }

    fn write_i32(&mut self, n: i32) {
        self.write(format!("(i32.const {})", n));
    }

    fn write_bytes(&mut self, bytes: &[u8]) -> i32 {
        self.indent();
        self.buffer.push('"');
        WasmWriter::bytes_sequence(&mut self.buffer, bytes);
        self.buffer.push('"');
        self.buffer.push('\n');

        bytes.len() as i32
    }

    fn write_string(&mut self, offset: i32, string: &str) -> i32 {
        let bytes = string.as_bytes();

        // Write length at head
        if bytes.len() > i32::MAX as usize {
            panic!("string literal is too long. max = {}", i32::MAX);
        }

        let mut n: i32 = 0;

        self.write("(data");
        self.push_scope();
        self.write_i32(offset);
        n += self.write_bytes(&(bytes.len() as i32).to_le_bytes());
        n += self.write_bytes(bytes);
        self.pop_scope();
        self.write(")");

        n
    }

    pub fn push_scope(&mut self) {
        self.level += 1;
    }

    pub fn pop_scope(&mut self) {
        self.level -= 1;
    }

    pub fn clear(&mut self) {
        self.buffer.clear();
    }

    fn indent(&mut self) {
        for _ in 0..self.level {
            self.buffer.push_str("  ");
        }
    }
}

impl Default for WasmWriter {
    fn default() -> Self {
        WasmWriter::new()
    }
}

pub struct AsmEmitter {
    writer: WasmWriter,
    memory: WasmWriter,
    memory_offset: i32,
    locals: Vec<String>,
    functions: Vec<Function>,
}

struct Param {
    //name: String,
    is_string: bool,
}
struct Function {
    name: String,           // The name of a function in .nico file
    reference_name: String, // The name of a function in .wat file
    params: Vec<Param>,
}

impl Default for AsmEmitter {
    fn default() -> Self {
        AsmEmitter::new()
    }
}

impl AsmEmitter {
    pub fn new() -> AsmEmitter {
        // imported functions
        let mut functions = vec![];

        functions.push(Function {
            name: "println!".to_string(),
            reference_name: "$println_i32".to_string(),
            params: vec![Param { is_string: false }],
        });
        functions.push(Function {
            name: "println!".to_string(),
            reference_name: "$println_str".to_string(),
            params: vec![Param { is_string: true }],
        });

        AsmEmitter {
            writer: WasmWriter::new(),
            memory: WasmWriter::new(),
            memory_offset: 0,
            locals: vec![],
            functions,
        }
    }

    pub fn generate_module(&mut self) -> String {
        let mut module = String::new();

        module.push_str(r#"(module"#);
        module.push('\n');
        module.push_str(r#"  (import "js" "mem" (memory 1))"#);
        module.push('\n');
        module.push_str(
            r#"  (import "printer" "println_i32" (func $println_i32 (param i32) (result i32)))"#,
        );
        module.push('\n');
        module.push_str(
            r#"  (import "printer" "println_str" (func $println_str (param i32) (result i32)))"#,
        );
        module.push('\n');
        module.push_str(self.memory.code());
        module.push_str(self.writer.code());
        module.push(')');

        module
    }

    pub fn emit_definition(
        &mut self,
        parser::Function {
            name,
            params,
            body,
            r#type: _,
        }: &parser::Function,
    ) {
        // function signature
        {
            let mut signature = String::new();

            signature.push_str(format!("(func ${} (export \"{}\")", name, name).as_str());
            for param in params {
                signature.push_str(format!(" (param ${} i32)", param).as_str());
            }
            signature.push_str(" (result i32)");

            self.emit(signature);
        }

        // Register function definition
        let typed_params = params
            .iter()
            .map(|_x| Param {
                //name: x.clone(),
                is_string: false,
            })
            .collect();

        self.functions.push(Function {
            name: name.clone(),
            reference_name: format!("${}", name),
            params: typed_params,
        });

        // Initialize local variables with parameters.
        self.locals.extend_from_slice(params);
        {
            self.push_scope();
            self.emit_expr(&*body);
            self.pop_scope();
            self.emit(")");
        }
        self.locals.clear();
    }

    fn emit_string(&mut self, s: &str) -> i32 {
        let offset = self.memory_offset;

        let length = self.memory.write_string(offset, s);
        self.memory_offset += length;
        offset
    }

    pub fn emit_expr(&mut self, node: &Node) {
        match &node.expr {
            Expr::Identifier(name) => {
                if !self.locals.iter().any(|local| local == name) {
                    panic!("Undefined local variable `{}`", name);
                }

                self.emit(format!("(get_local ${})", name));
            }
            Expr::Integer(n) => {
                self.writer.write_i32(*n);
            }
            Expr::String(s) => {
                let index = self.emit_string(&s);
                self.writer.write_i32(index);
            }
            Expr::Invocation { name, arguments } => {
                // name and the number of arguments
                let candidates: Vec<&Function> = self
                    .functions
                    .iter()
                    .filter(|f| f.name == *name)
                    .filter(|f| f.params.len() == arguments.len())
                    .filter(|f| {
                        f.params
                            .iter()
                            .zip(arguments.iter())
                            .all(|(p, a)| match a.expr {
                                Expr::String(_) => p.is_string,
                                _ => !p.is_string,
                            })
                    })
                    .collect();

                //let function = self.functions.iter().find(|f| f.name == *name);
                if candidates.is_empty() {
                    panic!("Undefined function `{}`", name);
                } else if candidates.len() > 1 {
                    panic!("Duplicate function `{}`", name);
                }

                let function = match candidates.len() {
                    0 => panic!("Undefined function `{}`", name),
                    1 => candidates[0],
                    _ => panic!("Duplicate function `{}`", name),
                };

                let name = function.reference_name.clone();

                self.emit(format!("(call {}", name));
                self.push_scope();
                for arg in arguments {
                    self.emit_expr(&arg);
                }
                self.pop_scope();
                self.emit(")")
            }
            // binop
            Expr::Add(lhs, rhs) => {
                self.emit_expr(&*lhs);
                self.emit_expr(&*rhs);
                self.emit("(i32.add)");
            }
            Expr::Sub(lhs, rhs) => {
                self.emit_expr(&*lhs);
                self.emit_expr(&*rhs);
                self.emit("(i32.sub)");
            }
            Expr::Mul(lhs, rhs) => {
                self.emit_expr(&*lhs);
                self.emit_expr(&*rhs);
                self.emit("(i32.mul)");
            }
            Expr::Div(lhs, rhs) => {
                self.emit_expr(&*lhs);
                self.emit_expr(&*rhs);
                self.emit("(i32.div_s)");
            }
            // relation
            Expr::LT(lhs, rhs) => {
                self.emit_expr(&*lhs);
                self.emit_expr(&*rhs);
                self.emit("(i32.lt_s)");
            }
            Expr::GT(lhs, rhs) => {
                self.emit_expr(&*lhs);
                self.emit_expr(&*rhs);
                self.emit("(i32.gt_s)");
            }
            Expr::LE(lhs, rhs) => {
                self.emit_expr(&*lhs);
                self.emit_expr(&*rhs);
                self.emit("(i32.le_s)");
            }
            Expr::GE(lhs, rhs) => {
                self.emit_expr(&*lhs);
                self.emit_expr(&*rhs);
                self.emit("(i32.ge_s)");
            }
            Expr::EQ(lhs, rhs) => {
                self.emit_expr(&*lhs);
                self.emit_expr(&*rhs);
                self.emit("(i32.eq)");
            }
            Expr::NE(lhs, rhs) => {
                self.emit_expr(&*lhs);
                self.emit_expr(&*rhs);
                self.emit("(i32.ne)");
            }
            Expr::If {
                condition,
                then_body,
                else_body,
            } => {
                self.emit_expr(&*condition);
                self.emit("(if (result i32)");
                self.push_scope();

                self.emit("(then");
                self.push_scope();
                self.emit_expr(&*then_body);
                self.pop_scope();
                self.emit(")");

                self.emit("(else");
                self.push_scope();
                match else_body {
                    Some(node) => self.emit_expr(&*node),
                    None => self.writer.write_i32(0),
                }
                self.pop_scope();
                self.emit("))");
                self.pop_scope();
            }
        }
    }

    pub fn emit<S: AsRef<str>>(&mut self, asm: S) {
        self.writer.write(asm);
    }

    pub fn push_scope(&mut self) {
        self.writer.push_scope()
    }

    pub fn pop_scope(&mut self) {
        self.writer.pop_scope()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn string_literal() {
        let mut writer = WasmWriter::new();

        writer.write_string(0, "");
        assert_eq!(
            writer.code(),
            "(data\n  (i32.const 0)\n  \"\\00\\00\\00\\00\"\n  \"\"\n)\n"
        );

        writer.clear();
        writer.write_string(0, "a");
        assert_eq!(
            writer.code(),
            "(data\n  (i32.const 0)\n  \"\\01\\00\\00\\00\"\n  \"a\"\n)\n"
        );

        writer.clear();
        writer.write_string(0, "あ");
        assert_eq!(
            writer.code(),
            "(data\n  (i32.const 0)\n  \"\\03\\00\\00\\00\"\n  \"\\e3\\81\\82\"\n)\n"
        );
    }
}
