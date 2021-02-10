pub mod analyzer;
pub mod asm;
pub mod parser;
pub mod sem;
pub mod tokenizer;

use analyzer::Semantic;
use asm::AsmEmitter;
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

fn main() {
    let args: Vec<String> = env::args().collect();
    let src = if args.len() > 1 {
        read_from_file(&args[1])
    } else {
        read_from_stdin()
    };

    let mut tokenizer = Tokenizer::from_string(&src);
    let mut module = parser::parse(&mut tokenizer);

    let mut semantic = Semantic::new();

    semantic.analyze(&mut module);

    let mut emitter = AsmEmitter::new();

    emitter.push_scope();

    // export function
    if let Some(function) = module.function {
        emitter.emit_definition(&*function);
    }

    // main function
    if let Some(expr) = module.expr {
        emitter.emit("(func (export \"main\") (result i32)");
        emitter.push_scope();
        emitter.emit_expr(&*expr);
        emitter.pop_scope();
        emitter.emit(")");
    }

    emitter.pop_scope();

    print!("{}", emitter.generate_module());
}
