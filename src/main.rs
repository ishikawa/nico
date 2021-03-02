use io::Read;
use nico::asm::wasm::Printer as WasmPrinter;
use nico::asm::AsmBuilder;
use nico::parser::Parser;
use nico::tokenizer::Tokenizer;
use nico::CompilerPasses;
use std::env;
use std::fs;
use std::io;

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
    let mut parser = Parser::new();
    let mut module = parser.parse(&mut tokenizer);

    let mut passes = CompilerPasses::new();
    passes.apply(&mut module);

    let mut builder = AsmBuilder::new();
    let mut printer = WasmPrinter::new();

    let wasm_module = builder.build_module(&module);

    printer.pretty = true;
    printer.write_module(&wasm_module);
    print!("{}", printer.to_string());
}
