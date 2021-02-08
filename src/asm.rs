use super::parser::{Definition, Expr};
pub struct AsmEmitter {
    level: i32,
    buffer: String,
    locals: Vec<String>,
    functions: Vec<Function>,
}

struct Function {
    name: String,
    params: Vec<String>,
}

impl Default for AsmEmitter {
    fn default() -> Self {
        AsmEmitter::new()
    }
}

impl AsmEmitter {
    pub fn new() -> AsmEmitter {
        AsmEmitter {
            level: 0,
            buffer: "".to_string(),
            locals: vec![],
            functions: vec![],
        }
    }

    pub fn code(&self) -> &String {
        &self.buffer
    }

    pub fn emit_definition(&mut self, definition: &Definition) {
        match definition {
            Definition::Function { name, params, body } => {
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
                self.functions.push(Function {
                    name: name.clone(),
                    params: params.clone(),
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
        }
    }

    fn emit_i32(&mut self, n: i32) {
        self.emit(format!("(i32.const {})", n));
    }

    fn emit_string(&mut self, _: &str) -> i32 {
        0
    }

    pub fn emit_expr(&mut self, node: &Expr) {
        match node {
            Expr::Identifier(name) => {
                if !self.locals.iter().any(|local| local == name) {
                    panic!("Undefined local variable `{}`", name);
                }

                self.emit(format!("(get_local ${})", name));
            }
            Expr::Integer(n) => {
                self.emit_i32(*n);
            }
            Expr::String(s) => {
                let index = self.emit_string(s);
                self.emit_i32(index);
            }
            Expr::Invocation { name, arguments } => {
                let function = self.functions.iter().find(|f| f.name == *name);

                match function {
                    None => panic!("Undefined function `{}`", name),
                    Some(function) if function.params.len() != arguments.len() => {
                        panic!(
                            "The function `{}` takes {} arguments, but {} given.",
                            name,
                            function.params.len(),
                            arguments.len()
                        );
                    }
                    _ => {}
                };

                self.emit(format!("(call ${}", name));
                self.push_scope();
                for arg in arguments {
                    self.emit_expr(arg);
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
                self.emit_expr(condition);
                self.emit("(if (result i32)");
                self.push_scope();

                self.emit("(then");
                self.push_scope();
                self.emit_expr(then_body);
                self.pop_scope();
                self.emit(")");

                self.emit("(else");
                self.push_scope();
                match else_body {
                    Some(node) => self.emit_expr(node),
                    None => self.emit_i32(0),
                }
                self.pop_scope();
                self.emit("))");
                self.pop_scope();
            }
        }
    }

    pub fn emit<S: AsRef<str>>(&mut self, asm: S) {
        self.indent();
        self.buffer.push_str(asm.as_ref());
        self.buffer.push('\n');
    }

    pub fn push_scope(&mut self) {
        self.level += 1;
    }

    pub fn pop_scope(&mut self) {
        self.level -= 1;
    }

    fn indent(&mut self) {
        for _ in 0..self.level {
            self.buffer.push_str("  ");
        }
    }
}
