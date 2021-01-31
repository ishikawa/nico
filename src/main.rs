use std::io;

fn main() {
    let mut integer = String::new();

    io::stdin()
        .read_line(&mut integer)
        .expect("Failed to read line.");

    let integer: u32 = integer.trim().parse().unwrap();

    println!("(module");
    println!("  (func (result i32)");
    println!("    (i32.const {})", integer);
    println!("  )");
    println!("  (export \"main\" (func 0))");
    println!(")");
}
