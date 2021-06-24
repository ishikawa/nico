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
use scope::{BindingResolver, ScopeChainBinder, TopLevelDeclarationBinder, VariableBinder};

pub fn analyze<'a>(arena: &'a BumpaloArena, node: &'a Program<'a>) {
    // Assign `.r#type()` with new type variables or primitive concrete type.
    let mut visitor = InitialTypeBinder::new(arena);
    traverse(arena, &mut visitor, node);

    // Register top level declarations in the scope.
    let mut visitor = TopLevelDeclarationBinder::new(arena);
    traverse(arena, &mut visitor, node);

    // Register local variables in scopes.
    let mut visitor = VariableBinder::new(arena);
    traverse(arena, &mut visitor, node);

    // Build parent-child scope chain.
    let mut visitor = ScopeChainBinder::new(arena);
    traverse(arena, &mut visitor, node);

    // Make sure all bindings exist and have an expected type.
    let mut visitor = BindingResolver::new(arena);
    traverse(arena, &mut visitor, node);

    // Assign concrete types to type annotations.
    let mut visitor = TypeQualifierResolver::new(arena);
    traverse(arena, &mut visitor, node);

    // Apply type inference
    let mut visitor = TypeInferencer::new(arena);
    traverse(arena, &mut visitor, node);

    // Remove unnecessary intermediate type variables.
    let mut visitor = TypeVariablePruner::new(arena);
    traverse(arena, &mut visitor, node);
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
