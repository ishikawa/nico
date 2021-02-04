mod parser;

use parser::Node;
use std::env;
use std::fs;
use std::io;

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

fn generate(node: &Node) {
    match node {
        Node::Integer(n) => {
            println!("    (i32.const {})", n);
        }
        Node::Add(lhs, rhs) => {
            generate(&*lhs);
            generate(&*rhs);
            println!("    (i32.add)");
        }
        Node::Sub(lhs, rhs) => {
            generate(&*lhs);
            generate(&*rhs);
            println!("    (i32.add)");
        }
        Node::Mul(lhs, rhs) => {
            generate(&*lhs);
            generate(&*rhs);
            println!("    (i32.add)");
        }
        Node::Div(lhs, rhs) => {
            generate(&*lhs);
            generate(&*rhs);
            println!("    (i32.add)");
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

    let node = parser::parse(&src).unwrap();

    println!("(module");
    println!("  (func (export \"main\") (result i32)");
    generate(&*node);
    println!("  )");
    println!(")");
}
