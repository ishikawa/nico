use super::parser::Node;
pub struct AsmEmitter {
    level: i32,
    buffer: String,
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
        }
    }

    pub fn code(&self) -> &String {
        &self.buffer
    }

    pub fn emit_zero(&mut self) {
        self.emit("(i32.const 0)");
    }

    pub fn emit_expr(&mut self, node: &Node) {
        match node {
            Node::Integer(n) => {
                self.emit(format!("(i32.const {})", n));
            }
            // binop
            Node::Add(lhs, rhs) => {
                self.emit_expr(&*lhs);
                self.emit_expr(&*rhs);
                self.emit("(i32.add)");
            }
            Node::Sub(lhs, rhs) => {
                self.emit_expr(&*lhs);
                self.emit_expr(&*rhs);
                self.emit("(i32.sub)");
            }
            Node::Mul(lhs, rhs) => {
                self.emit_expr(&*lhs);
                self.emit_expr(&*rhs);
                self.emit("(i32.mul)");
            }
            Node::Div(lhs, rhs) => {
                self.emit_expr(&*lhs);
                self.emit_expr(&*rhs);
                self.emit("(i32.div_u)");
            }
            // relation
            Node::LT(lhs, rhs) => {
                self.emit_expr(&*lhs);
                self.emit_expr(&*rhs);
                self.emit("(i32.lt_u)");
            }
            Node::GT(lhs, rhs) => {
                self.emit_expr(&*lhs);
                self.emit_expr(&*rhs);
                self.emit("(i32.gt_u)");
            }
            Node::LE(lhs, rhs) => {
                self.emit_expr(&*lhs);
                self.emit_expr(&*rhs);
                self.emit("(i32.le_u)");
            }
            Node::GE(lhs, rhs) => {
                self.emit_expr(&*lhs);
                self.emit_expr(&*rhs);
                self.emit("(i32.ge_u)");
            }
            Node::EQ(lhs, rhs) => {
                self.emit_expr(&*lhs);
                self.emit_expr(&*rhs);
                self.emit("(i32.eq)");
            }
            Node::NE(lhs, rhs) => {
                self.emit_expr(&*lhs);
                self.emit_expr(&*rhs);
                self.emit("(i32.ne)");
            }
            Node::If {
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
                    None => self.emit_zero(),
                }
                self.pop_scope();
                self.emit("))");
                self.pop_scope();
            }
            Node::Function {
                name: _,
                params: _,
                body: _,
            } => {}
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
