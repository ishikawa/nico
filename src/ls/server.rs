use lsp_types::{
    InitializeParams, OneOf, RenameOptions, SemanticTokenModifier, SemanticTokenType,
    SemanticTokensFullOptions, SemanticTokensLegend, SemanticTokensOptions,
    SemanticTokensServerCapabilities, ServerCapabilities, SignatureHelpOptions,
    TextDocumentSyncCapability, TextDocumentSyncKind, WorkDoneProgressOptions,
};
use std::collections::HashSet;

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

        let token_types = self.build_semantic_token_types(params);
        let token_modifiers = self.build_semantic_token_modifiers(params);

        ServerCapabilities {
            rename_provider: self.build_rename_provider(params),
            signature_help_provider: self.build_signature_help_provider(params),
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

    fn build_rename_provider(
        &self,
        params: &InitializeParams,
    ) -> Option<OneOf<bool, RenameOptions>> {
        let text_document = params.capabilities.text_document.as_ref()?;
        let rename = text_document.rename.as_ref()?;

        if let Some(true) = rename.prepare_support {
            Some(OneOf::Right(RenameOptions {
                prepare_provider: Some(true),
                work_done_progress_options: WorkDoneProgressOptions {
                    work_done_progress: None,
                },
            }))
        } else {
            Some(OneOf::Left(true))
        }
    }

    fn build_signature_help_provider(
        &self,
        params: &InitializeParams,
    ) -> Option<SignatureHelpOptions> {
        let text_document = params.capabilities.text_document.as_ref()?;
        let _signature_help = text_document.signature_help.as_ref()?;

        Some(SignatureHelpOptions {
            trigger_characters: Some(["(", ")", "{", "}"].iter().map(|s| s.to_string()).collect()),
            retrigger_characters: Some([","].iter().map(|s| s.to_string()).collect()),
            work_done_progress_options: WorkDoneProgressOptions {
                work_done_progress: None,
            },
        })
    }

    fn build_semantic_token_types(&self, params: &InitializeParams) -> Vec<SemanticTokenType> {
        if let Some(ref text_document) = params.capabilities.text_document {
            if let Some(ref semantic_tokens) = text_document.semantic_tokens {
                // types
                if let Some(server_token_type) = self.token_types {
                    let client_set: HashSet<_> = semantic_tokens.token_types.iter().collect();

                    return server_token_type
                        .iter()
                        .filter(|t| client_set.contains(t))
                        .cloned()
                        .collect();
                }
            }
        }

        return vec![];
    }

    fn build_semantic_token_modifiers(
        &self,
        params: &InitializeParams,
    ) -> Vec<SemanticTokenModifier> {
        if let Some(ref text_document) = params.capabilities.text_document {
            if let Some(ref semantic_tokens) = text_document.semantic_tokens {
                // types
                if let Some(server_token_modifiers) = self.token_modifiers {
                    let client_set: HashSet<_> = semantic_tokens.token_modifiers.iter().collect();

                    return server_token_modifiers
                        .iter()
                        .filter(|t| client_set.contains(t))
                        .cloned()
                        .collect();
                }
            }
        }

        return vec![];
    }
}
