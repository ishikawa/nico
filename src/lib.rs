pub mod asm;
pub mod parser;
pub mod sem;
pub mod tokenizer;
mod util;
use sem::SemanticAnalyzer;

#[derive(Default)]
pub struct CompilerPasses {
    binder: sem::Binder,
    inferencer: sem::TypeInferencer,
    allocator: asm::Allocator,
}

impl CompilerPasses {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn binder(&self) -> &sem::Binder {
        &self.binder
    }

    pub fn inferencer(&self) -> &sem::TypeInferencer {
        &self.inferencer
    }

    pub fn allocator(&self) -> &asm::Allocator {
        &self.allocator
    }

    pub fn apply(&mut self, module: &mut parser::Module) {
        self.binder.analyze(module);
        self.inferencer.analyze(module);
        self.allocator.analyze(module);
    }
}