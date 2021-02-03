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

fn read_from_file(filename: &String) -> String {
    fs::read_to_string(filename)
        .expect(format!("Something went wrong reading the file at {}", filename).as_str())
}

fn generate(node: &Node) {
    match node {
        Node::Integer(n) => {
            println!("    (i32.const {})", n);
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

    let node = parser::parse(&src);

    println!("(module");
    println!("  (func (export \"main\") (result i32)");
    generate(&node);
    println!("  )");
    println!(")");
}
