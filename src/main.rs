mod parser;

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

fn main() {
    let args: Vec<String> = env::args().collect();
    let integer = if args.len() > 1 {
        read_from_file(&args[1])
    } else {
        read_from_stdin()
    };

    let integer: u32 = integer.trim().parse().unwrap();

    println!("(module");
    println!("  (func (result i32)");
    println!("    (i32.const {})", integer);
    println!("  )");
    println!("  (export \"main\" (func 0))");
    println!(")");
}
