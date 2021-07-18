use crate::arena::BumpaloArena;
use crate::compiler::CompilerError;
use crate::syntax::Parser;
use crate::syntax::Tokenizer;

pub fn compile(src: String, filename: &str) -> Result<String, CompilerError> {
    let arena = BumpaloArena::new();
    let tokenizer = Tokenizer::from_string(&src);
    let mut parser = Parser::new(&arena, tokenizer, filename);
    let program = parser.parse(&arena);

    // JSON
    let j = serde_json::to_string_pretty(&program).expect("JSON serialization");

    Ok(format!("{}\n", j))
}
