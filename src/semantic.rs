mod binding;
mod errors;
mod scope;
mod types;

pub use binding::Binding;
pub use errors::SemanticError;
pub use scope::Scope;
pub use types::*;

use crate::arena::BumpaloArena;
use crate::syntax::traverse;
use crate::syntax::Program;
use scope::{ScopeChainBinder, TopLevelDeclarationBinder, VariableBinder};

pub fn analyze<'a>(arena: &'a BumpaloArena, node: &'a Program<'a>) {
    let mut binder = InitialTypeBinder::new(arena);
    traverse(arena, &mut binder, node);

    let mut binder = TopLevelDeclarationBinder::new(arena);
    traverse(arena, &mut binder, node);

    let mut binder = ScopeChainBinder::new(arena);
    traverse(arena, &mut binder, node);

    let mut binder = VariableBinder::new(arena);
    traverse(arena, &mut binder, node);

    let mut binder = TypeQualifierResolver::new(arena);
    traverse(arena, &mut binder, node);

    let mut binder = TypeInferencer::new(arena);
    traverse(arena, &mut binder, node);

    let mut binder = TypeVariablePruner::new(arena);
    traverse(arena, &mut binder, node);
}

#[cfg(test)]
mod tests {
    use crate::arena::BumpaloArena;
    use crate::syntax::Parser;

    #[test]
    fn top_level_declarations() {
        let arena = BumpaloArena::new();
        let program = Parser::parse_string(&arena, "fun foo()\nend");

        let scope = program.declarations_scope();
        let binding = scope.get_binding("foo");

        assert!(binding.is_some());

        let binding = binding.unwrap();
        assert_eq!(binding.id(), "foo");
    }
}
