//! Show Code Completion Proposals
//! https://code.visualstudio.com/api/language-extensions/programmatic-language-features#show-code-completion-proposals
use crate::arena::BumpaloArena;
use crate::syntax::{self, MissingTokenKind, NodePath, Position, Program, Token};
use lsp_types::CompletionItem;

#[derive(Debug)]
pub struct Completion<'a> {
    arena: &'a BumpaloArena,
    position: Position,
}

impl<'a> Completion<'a> {
    pub fn new(arena: &'a BumpaloArena, position: Position) -> Self {
        Self { arena, position }
    }

    pub fn propose(&mut self, _program: &'a Program<'a>) -> Option<Vec<CompletionItem>> {
        None
    }
}

impl<'a> syntax::Visitor<'a> for Completion<'a> {
    fn enter_skipped_token(
        &mut self,
        _path: &'a NodePath<'a>,
        token: &Token,
        _expected: MissingTokenKind,
    ) {
        eprintln!("skipped = {}", token)
    }
}
