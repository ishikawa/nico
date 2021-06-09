//! Show Code Completion Proposals
//! https://code.visualstudio.com/api/language-extensions/programmatic-language-features#show-code-completion-proposals
use crate::arena::BumpaloArena;
use crate::semantic::Binding;
use crate::syntax::{self, Identifier, Node, NodePath, Position, Program};
use lsp_types::CompletionItem;
use lsp_types::CompletionItemKind;

use super::description;

#[derive(Debug)]
pub struct Completion<'a> {
    arena: &'a BumpaloArena,
    position: Position,
    candidates: Vec<CompletionItem>,
}

impl<'a> Completion<'a> {
    pub fn new(arena: &'a BumpaloArena, position: Position) -> Self {
        Self {
            arena,
            position,
            candidates: vec![],
        }
    }

    pub fn propose(&mut self, program: &'a Program<'a>) -> Option<Vec<CompletionItem>> {
        syntax::traverse(self.arena, self, program);

        if self.candidates.is_empty() {
            None
        } else {
            let candidates = std::mem::take(&mut self.candidates);
            Some(candidates)
        }
    }

    fn add_candidate(&mut self, name: &str, binding: &Binding<'_>) {
        let kind = if binding.is_defined_function() {
            Some(CompletionItemKind::Function)
        } else if binding.is_defined_struct() {
            Some(CompletionItemKind::Struct)
        } else if binding.is_function_parameter() || binding.is_local_variable() {
            Some(CompletionItemKind::Variable)
        } else {
            None
        };

        let detail = if let Some(pattern) = binding.variable_pattern() {
            Some(description::format_local_variable(pattern))
        } else if let Some(param) = binding.function_parameter() {
            Some(description::format_function_parameter(param))
        } else if let Some(function_type) = binding.defined_function_type() {
            Some(function_type.to_string())
        } else if let Some(struct_type) = binding.defined_struct_type() {
            Some(struct_type.to_string())
        } else {
            None
        };

        let item = CompletionItem {
            label: name.to_string(),
            kind,
            detail,
            ..CompletionItem::default()
        };

        self.candidates.push(item);
    }
}

impl<'a> syntax::Visitor<'a> for Completion<'a> {
    fn enter_identifier(&mut self, path: &'a NodePath<'a>, id: &'a Identifier<'a>) {
        // Find the position of the current input position.
        if id.range().contains(self.position) {
            path.stop();
        } else {
            return;
        }

        let input_str = id.as_str();
        let mut parent_scope = Some(path.scope());

        while let Some(scope) = parent_scope {
            for (name, binding) in scope.borrow_bindings().iter() {
                // Search case insensitively
                if input_str.chars().all(|c1| {
                    name.chars()
                        .any(|c2| c1.to_ascii_lowercase() == c2.to_ascii_lowercase())
                }) {
                    self.add_candidate(name, binding);
                }
            }

            parent_scope = scope.parent();
        }

        // Sort alphabetically
        // TODO: sort by matching score (edit distance).
        self.candidates
            .sort_by(|a, b| a.label.partial_cmp(&b.label).unwrap())
    }
}
