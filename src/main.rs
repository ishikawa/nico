mod parser;
mod tokenizer;

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

fn generate(node: &Node, level: i32) {
    match node {
        Node::Integer(n) => {
            indent(level);
            println!("(i32.const {})", n);
        }
        // binop
        Node::Add(lhs, rhs) => {
            generate(&*lhs, level);
            generate(&*rhs, level);
            indent(level);
            println!("(i32.add)");
        }
        Node::Sub(lhs, rhs) => {
            generate(&*lhs, level);
            generate(&*rhs, level);
            indent(level);
            println!("(i32.sub)");
        }
        Node::Mul(lhs, rhs) => {
            generate(&*lhs, level);
            generate(&*rhs, level);
            indent(level);
            println!("(i32.mul)");
        }
        Node::Div(lhs, rhs) => {
            generate(&*lhs, level);
            generate(&*rhs, level);
            indent(level);
            println!("(i32.div_u)");
        }
        // relation
        Node::LT(lhs, rhs) => {
            generate(&*lhs, level);
            generate(&*rhs, level);
            indent(level);
            println!("(i32.lt_u)");
        }
        Node::GT(lhs, rhs) => {
            generate(&*lhs, level);
            generate(&*rhs, level);
            indent(level);
            println!("(i32.gt_u)");
        }
        Node::LE(lhs, rhs) => {
            generate(&*lhs, level);
            generate(&*rhs, level);
            indent(level);
            println!("(i32.le_u)");
        }
        Node::GE(lhs, rhs) => {
            generate(&*lhs, level);
            generate(&*rhs, level);
            indent(level);
            println!("(i32.ge_u)");
        }
        Node::EQ(lhs, rhs) => {
            generate(&*lhs, level);
            generate(&*rhs, level);
            indent(level);
            println!("(i32.eq)");
        }
        Node::NE(lhs, rhs) => {
            generate(&*lhs, level);
            generate(&*rhs, level);
            indent(level);
            println!("(i32.ne)");
        }
        Node::If {
            condition,
            then_body,
            else_body,
        } => {
            generate(condition, level);
            indent(level);
            println!("(if (result i32)");
            indent(level + 1);
            println!("(then");
            generate(then_body, level + 2);
            indent(level + 1);
            println!(")");
            indent(level + 1);
            println!("(else");
            match else_body {
                Some(node) => generate(node, level + 2),
                None => generate(&Node::Integer(0), level + 2),
            }
            indent(level + 1);
            println!(")");
            indent(level);
            println!(")");
        }
    }
}

fn indent(level: i32) {
    for _ in 0..level {
        print!("  ");
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
    indent(1);
    println!("(func (export \"main\") (result i32)");
    generate(&*node, 2);
    indent(1);
    println!(")");
    println!(")");
}
