use crate::asm::wasm::Printer as WasmPrinter;
use crate::asm::AsmBuilder;
use crate::compiler::CompilerError;
use crate::parser::Parser;
use crate::syntax::Tokenizer;
use crate::CompilerPasses;

pub fn compile(src: String) -> Result<String, CompilerError> {
    let mut tokenizer = Tokenizer::from_string(&src);
    let parser = Parser::new();
    let mut module = parser.parse(&mut tokenizer)?;

    let mut passes = CompilerPasses::new();
    passes.apply(&mut module);

    let builder = AsmBuilder::new();
    let mut printer = WasmPrinter::new();

    let wasm_module = builder.build_module(&module);

    printer.pretty = true;
    printer.write_module(&wasm_module);
    Ok(printer.to_string())
}
