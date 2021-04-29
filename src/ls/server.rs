use lsp_types::{
    InitializeParams, SemanticTokenModifier, SemanticTokenType, SemanticTokensFullOptions,
    SemanticTokensLegend, SemanticTokensOptions, SemanticTokensServerCapabilities,
    ServerCapabilities, TextDocumentSyncCapability, TextDocumentSyncKind,
};
use std::collections::HashSet;
use std::iter::FromIterator;

#[derive(Debug, Default)]
pub struct ServerCapabilitiesBuilder<'a> {
    params: Option<&'a InitializeParams>,
    token_types: Option<&'a [SemanticTokenType]>,
    token_modifiers: Option<&'a [SemanticTokenModifier]>,
}

impl<'a> ServerCapabilitiesBuilder<'a> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn initialized(&mut self, params: &'a InitializeParams) -> &mut Self {
        self.params = Some(params);
        self
    }

    pub fn semantic_token_types(&mut self, token_types: &'a [SemanticTokenType]) -> &mut Self {
        self.token_types = Some(token_types);
        self
    }

    pub fn semantic_token_modifiers(
        &mut self,
        token_modifiers: &'a [SemanticTokenModifier],
    ) -> &mut Self {
        self.token_modifiers = Some(token_modifiers);
        self
    }

    pub fn build(&self) -> ServerCapabilities {
        let params = self.params.unwrap();

        let mut token_types: Vec<SemanticTokenType> = vec![];
        let mut token_modifiers: Vec<SemanticTokenModifier> = vec![];

        if let Some(ref text_document) = params.capabilities.text_document {
            if let Some(ref semantic_tokens) = text_document.semantic_tokens {
                // types
                if let Some(server_token_type) = self.token_types {
                    let client_set: HashSet<&SemanticTokenType> =
                        HashSet::from_iter(semantic_tokens.token_types.iter());

                    for ty in server_token_type {
                        if client_set.contains(ty) {
                            token_types.push(ty.clone());
                        }
                    }
                }

                // modifiers
                if let Some(server_token_modifiers) = self.token_modifiers {
                    let client_set: HashSet<&SemanticTokenModifier> =
                        HashSet::from_iter(semantic_tokens.token_modifiers.iter());

                    for m in server_token_modifiers {
                        if client_set.contains(m) {
                            token_modifiers.push(m.clone());
                        }
                    }
                }
            }
        }

        ServerCapabilities {
            text_document_sync: Some(TextDocumentSyncCapability::Kind(
                TextDocumentSyncKind::Incremental,
            )),
            semantic_tokens_provider: Some(
                SemanticTokensServerCapabilities::SemanticTokensOptions(SemanticTokensOptions {
                    legend: SemanticTokensLegend {
                        token_types,
                        token_modifiers,
                    },
                    full: Some(SemanticTokensFullOptions::Bool(true)),
                    ..SemanticTokensOptions::default()
                }),
            ),
            ..ServerCapabilities::default()
        }
    }
}
