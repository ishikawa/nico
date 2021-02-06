pub mod parser;
pub mod tokenizer;

use parser::Node;
use std::env;
use std::fs;
use std::io;
use tokenizer::Tokenizer;

use io::Read;

// Compiler
fn read_from_stdin() -> String {
    let mut content = String::new();

    io::stdin()
        .read_to_string(&mut content)
        .expect("Failed to read line.");

    content
}

fn read_from_file(filename: &str) -> String {
    match fs::read_to_string(filename) {
        Ok(s) => s,
        Err(_e) => panic!("Something went wrong reading the file at {}", filename),
    }
}

struct AsmEmitter {
    level: i32,
    code: String,
}

impl AsmEmitter {
    pub fn new() -> AsmEmitter {
        AsmEmitter {
            level: 0,
            code: "".to_string(),
        }
    }

    pub fn emit<S: AsRef<str>>(&mut self, asm: S) {
        self.indent();
        self.code.push_str(asm.as_ref());
        self.code.push('\n');
    }

    pub fn push_scope(&mut self) {
        self.level += 1;
    }

    pub fn pop_scope(&mut self) {
        self.level -= 1;
    }

    fn indent(&mut self) {
        for _ in 0..self.level {
            self.code.push_str("  ");
        }
    }
}

fn generate(node: &Node, emitter: &mut AsmEmitter) {
    match node {
        Node::Integer(n) => {
            emitter.emit(format!("(i32.const {})", n));
        }
        // binop
        Node::Add(lhs, rhs) => {
            generate(&*lhs, emitter);
            generate(&*rhs, emitter);
            emitter.emit("(i32.add)");
        }
        Node::Sub(lhs, rhs) => {
            generate(&*lhs, emitter);
            generate(&*rhs, emitter);
            emitter.emit("(i32.sub)");
        }
        Node::Mul(lhs, rhs) => {
            generate(&*lhs, emitter);
            generate(&*rhs, emitter);
            emitter.emit("(i32.mul)");
        }
        Node::Div(lhs, rhs) => {
            generate(&*lhs, emitter);
            generate(&*rhs, emitter);
            emitter.emit("(i32.div_u)");
        }
        // relation
        Node::LT(lhs, rhs) => {
            generate(&*lhs, emitter);
            generate(&*rhs, emitter);
            emitter.emit("(i32.lt_u)");
        }
        Node::GT(lhs, rhs) => {
            generate(&*lhs, emitter);
            generate(&*rhs, emitter);
            emitter.emit("(i32.gt_u)");
        }
        Node::LE(lhs, rhs) => {
            generate(&*lhs, emitter);
            generate(&*rhs, emitter);
            emitter.emit("(i32.le_u)");
        }
        Node::GE(lhs, rhs) => {
            generate(&*lhs, emitter);
            generate(&*rhs, emitter);
            emitter.emit("(i32.ge_u)");
        }
        Node::EQ(lhs, rhs) => {
            generate(&*lhs, emitter);
            generate(&*rhs, emitter);
            emitter.emit("(i32.eq)");
        }
        Node::NE(lhs, rhs) => {
            generate(&*lhs, emitter);
            generate(&*rhs, emitter);
            emitter.emit("(i32.ne)");
        }
        Node::If {
            condition,
            then_body,
            else_body,
        } => {
            generate(condition, emitter);
            emitter.emit("(if (result i32)");
            emitter.push_scope();

            emitter.emit("(then");
            emitter.push_scope();
            generate(then_body, emitter);
            emitter.pop_scope();
            emitter.emit(")");

            emitter.emit("(else");
            emitter.push_scope();
            match else_body {
                Some(node) => generate(node, emitter),
                None => generate(&Node::Integer(0), emitter),
            }
            emitter.pop_scope();
            emitter.emit("))");
            emitter.pop_scope();
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let src = if args.len() > 1 {
        read_from_file(&args[1])
    } else {
        read_from_stdin()
    };

    let mut tokenizer = Tokenizer::from_string(&src);
    let node = parser::parse_expression(&mut tokenizer).expect("no expression");

    //let node = parser::parse(&src).unwrap();
    let mut emitter = AsmEmitter::new();

    emitter.emit("(module");
    emitter.push_scope();

    emitter.emit("(func (export \"main\") (result i32)");
    emitter.push_scope();
    generate(&*node, &mut emitter);
    emitter.pop_scope();
    emitter.emit("))");
    emitter.pop_scope();

    print!("{}", emitter.code);
}
