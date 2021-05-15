use log::{info, warn};
use lsp_types::*;
use nico::syntax::{
    self, Ast, EffectiveRange, Identifier, MissingTokenKind, Node, NodePath, ParseError, Parser,
    StructLiteral, TextToken, Token, TokenKind, Trivia,
};
use nico::{
    ls::{self, server::ServerCapabilitiesBuilder},
    syntax::Expression,
};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::cell::RefCell;
use std::convert::TryFrom;
use std::rc::Rc;
use std::{
    collections::HashMap,
    io::{Read, Write},
};
use std::{io, string};
use url::Url;

// --- JSON-RPC
#[derive(Debug, PartialEq, Clone, Deserialize, Serialize)]
#[serde(untagged)]
enum Id {
    Int(i32),
    Str(String),
}

// JSON-RPC
#[derive(Debug, PartialEq, Clone, Deserialize, Serialize)]
struct Request {
    jsonrpc: String,
    id: Option<Id>,
    method: String,
    params: Option<Value>,
}

#[derive(Debug, PartialEq, Clone, Deserialize, Serialize)]
struct Response {
    jsonrpc: String,
    id: Id,
    result: Option<Value>,
    error: Option<ResponseError>,
}

#[derive(Debug, PartialEq, Clone, Deserialize, Serialize)]
struct ResponseError {
    code: ResponseErrorCode,
    message: String,
    data: Option<Value>,
}

#[derive(Debug, PartialEq, Clone, Deserialize, Serialize)]
enum ResponseErrorCode {
    ParseError = -32700,
    InvalidRequest = -32600,
    MethodNotFound = -32601,
    InvalidParams = -32602,
    InternalError = -32603,
}

#[derive(Debug, PartialEq, Clone, Deserialize, Serialize)]
struct Notification {
    jsonrpc: String,
    method: String,
    params: Option<Value>,
}

#[derive(Debug)]
struct HandlerError {
    kind: HandlerErrorKind,
}

#[derive(Debug)]
enum HandlerErrorKind {
    // Errors
    ServerNotInitialized,
    Utf8Error(string::FromUtf8Error),
    IoError(io::Error),
    JsonError(serde_json::Error),

    #[allow(dead_code)]
    GenericError {
        id: Id,
        message: String,
    },

    // Warnings
    InvalidParams,
    DocumentNotFound(Url),
    ParseError(ParseError),
}

impl From<io::Error> for HandlerError {
    fn from(err: io::Error) -> Self {
        Self {
            kind: HandlerErrorKind::IoError(err),
        }
    }
}

impl From<string::FromUtf8Error> for HandlerError {
    fn from(err: string::FromUtf8Error) -> Self {
        Self {
            kind: HandlerErrorKind::Utf8Error(err),
        }
    }
}

impl From<serde_json::Error> for HandlerError {
    fn from(err: serde_json::Error) -> Self {
        Self {
            kind: HandlerErrorKind::JsonError(err),
        }
    }
}

impl From<ParseError> for HandlerError {
    fn from(err: ParseError) -> Self {
        Self {
            kind: HandlerErrorKind::ParseError(err),
        }
    }
}

impl Request {
    fn take_params<T: serde::de::DeserializeOwned>(&mut self) -> Result<T, HandlerError> {
        match self.params.take() {
            None => Err(HandlerError {
                kind: HandlerErrorKind::InvalidParams,
            }),
            Some(params) => Ok(serde_json::from_value::<T>(params)?),
        }
    }
}

impl Response {
    fn from_value(id: &Id, value: Value) -> Self {
        Self {
            jsonrpc: "2.0".to_string(),
            id: id.clone(),
            result: Some(value),
            error: None,
        }
    }

    fn from_error(id: &Id, error: ResponseError) -> Self {
        Self {
            jsonrpc: "2.0".to_string(),
            id: id.clone(),
            result: None,
            error: Some(error),
        }
    }
}

// Position & Range
fn syntax_position(position: Position) -> syntax::Position {
    syntax::Position {
        line: position.line,
        character: position.character,
    }
}

fn lsp_position(position: syntax::Position) -> Position {
    Position::new(position.line, position.character)
}

fn lsp_range(range: syntax::EffectiveRange) -> Range {
    Range::new(lsp_position(range.start), lsp_position(range.end))
}

// --- Language Server States
#[derive(Debug, Default)]
struct DiagnosticsCollector {
    pub diagnostics: Vec<Diagnostic>,
}

impl DiagnosticsCollector {
    pub fn new() -> Self {
        DiagnosticsCollector::default()
    }

    fn add_diagnostic<S: Into<String>>(&mut self, range: EffectiveRange, message: S) {
        let diagnostic = Diagnostic {
            range: Range {
                start: Position {
                    line: range.start.line,
                    character: range.start.character,
                },
                end: Position {
                    line: range.end.line,
                    character: range.end.character,
                },
            },
            severity: Some(DiagnosticSeverity::Error),
            message: message.into(),
            source: Some("nico-ls".to_string()),
            ..Diagnostic::default()
        };

        self.diagnostics.push(diagnostic);
    }

    fn add_missing_token_error(&mut self, range: EffectiveRange, expected: MissingTokenKind) {
        self.add_diagnostic(range, format!("Syntax Error: expected {}", expected));
    }
}

impl syntax::Visitor for DiagnosticsCollector {
    fn enter_variable(
        &mut self,
        tree: &Ast,
        path: &mut NodePath,
        expr: &Expression,
        id: &Identifier,
    ) {
        // Undefined variable
        if path.scope().borrow().get_binding(id.as_str()).is_none() {
            self.add_diagnostic(expr.range(tree), format!("Cannot find name '{}'.", id));
        }
    }

    fn enter_struct_literal(
        &mut self,
        tree: &Ast,
        path: &mut NodePath,
        _expr: &Expression,
        value: &StructLiteral,
    ) {
        // Expected struct for name
        if let Some(binding) = path.scope().borrow().get_binding(value.name(tree).as_str()) {
            if !binding.borrow().value().is_struct() {
                self.add_diagnostic(
                    value.name(tree).range(tree),
                    format!("Expected struct, found '{}'.", binding.borrow()),
                );
            }
        } else {
            self.add_diagnostic(
                value.name(tree).range(tree),
                format!("Cannot find name '{}'.", value.name(tree)),
            );
        }
    }

    fn enter_missing_token(
        &mut self,
        _tree: &Ast,
        _path: &mut NodePath,
        range: EffectiveRange,
        item: MissingTokenKind,
    ) {
        self.add_missing_token_error(range, item);
    }

    fn enter_skipped_token(
        &mut self,
        _tree: &Ast,
        _path: &mut NodePath,
        token: &Token,
        expected: MissingTokenKind,
    ) {
        self.add_missing_token_error(token.range, expected);
    }
}

#[derive(Debug)]
struct SemanticTokenAbsoluteParams {
    line: u32,
    character: u32,
    length: u32,
    token_type: SemanticTokenType,
    token_modifiers_bitset: u32,
}

#[derive(Debug, Default)]
struct SemanticTokenizer {
    token_type_legend: Rc<HashMap<SemanticTokenType, u32>>,
    token_modifier_legend: Rc<HashMap<SemanticTokenModifier, u32>>,
    previous_line: u32,
    previous_character: u32,
    pub tokens: Vec<SemanticToken>,
}

impl SemanticTokenizer {
    pub fn new(
        token_type_legend: &Rc<HashMap<SemanticTokenType, u32>>,
        token_modifier_legend: &Rc<HashMap<SemanticTokenModifier, u32>>,
    ) -> Self {
        Self {
            token_type_legend: Rc::clone(token_type_legend),
            token_modifier_legend: Rc::clone(token_modifier_legend),
            ..Self::default()
        }
    }

    fn add_token_modifiers_bitset(&self, bitset: &mut u32, modifier: SemanticTokenModifier) {
        let position = self.token_modifier_legend.get(&modifier);

        if let Some(position) = position {
            *bitset |= 1 << position;
        } else {
            warn!("SemanticTokenModifier ({:?}) not registered", modifier);
        }
    }

    fn token_type_and_modifiers(
        &self,
        tree: &Ast,
        path: &NodePath,
        token: &Token,
    ) -> Option<(SemanticTokenType, u32)> {
        let mut token_modifiers_bitset = 0;

        let token_type = match token.kind {
            TokenKind::If
            | TokenKind::Else
            | TokenKind::End
            | TokenKind::Export
            | TokenKind::Fun
            | TokenKind::Let
            | TokenKind::Struct
            | TokenKind::When
            | TokenKind::Case => SemanticTokenType::KEYWORD,
            TokenKind::Integer(_) => SemanticTokenType::NUMBER,
            TokenKind::Eq
            | TokenKind::Ne
            | TokenKind::Le
            | TokenKind::Ge
            | TokenKind::Char('+')
            | TokenKind::Char('-')
            | TokenKind::Char('*')
            | TokenKind::Char('/')
            | TokenKind::Char('%') => SemanticTokenType::OPERATOR,
            TokenKind::Identifier(_) => self.token_type_and_modifiers_for_identifier(
                tree,
                path,
                &mut token_modifiers_bitset,
            ),
            TokenKind::StringStart | TokenKind::StringEnd | TokenKind::StringContent(_) => {
                SemanticTokenType::STRING
            }
            TokenKind::StringEscapeSequence(_) => {
                self.add_token_modifiers_bitset(
                    &mut token_modifiers_bitset,
                    SemanticTokenModifier::READONLY,
                );
                SemanticTokenType::VARIABLE
            }
            TokenKind::I32 => SemanticTokenType::TYPE,
            _ => return None,
        };

        Some((token_type, token_modifiers_bitset))
    }

    fn token_type_and_modifiers_for_identifier(
        &self,
        tree: &Ast,
        path: &NodePath,
        modifiers: &mut u32,
    ) -> SemanticTokenType {
        let node = path.node(tree);

        // In current AST specification, the corresponding node for an Identifier token is
        // an Identifier node. But in some fragile AST, it may be differ.
        let id = match node.identifier() {
            Some(id) => id,
            None => return SemanticTokenType::VARIABLE,
        };

        let parent = path.expect_parent();
        let parent = parent.borrow();
        let scope = parent.scope();
        let parent = parent.node(tree);

        if parent.is_function_definition() {
            SemanticTokenType::FUNCTION
        } else if parent.is_function_parameter() {
            SemanticTokenType::PARAMETER
        } else if parent.is_struct_definition() || parent.is_struct_literal() {
            SemanticTokenType::STRUCT
        } else if parent.is_struct_field() || parent.is_member_expression() {
            SemanticTokenType::PROPERTY
        } else if parent.is_variable_expression(tree) {
            if let Some(binding) = scope.borrow().get_binding(id.as_str()) {
                let binding = binding.borrow();
                let definition = binding.value();

                if definition.is_function() {
                    if definition.node_id().is_none() {
                        self.add_token_modifiers_bitset(
                            modifiers,
                            SemanticTokenModifier::DEFAULT_LIBRARY,
                        );
                    }
                    return SemanticTokenType::FUNCTION;
                } else if definition.is_function_parameter() {
                    return SemanticTokenType::PARAMETER;
                } else if definition.is_struct() {
                    return SemanticTokenType::STRUCT;
                }
            }

            SemanticTokenType::VARIABLE
        } else {
            SemanticTokenType::VARIABLE
        }
    }

    fn add_token_generic(&mut self, tree: &Ast, path: &NodePath, token: &Token) {
        if let Some((token_type, token_modifiers_bitset)) =
            self.token_type_and_modifiers(tree, path, token)
        {
            self.add_token_with_type(token, token_type, token_modifiers_bitset);
        }
    }

    fn add_token_with_type(
        &mut self,
        token: &Token,
        token_type: SemanticTokenType,
        token_modifiers_bitset: u32,
    ) {
        self.add_semantic_token_absolute(SemanticTokenAbsoluteParams {
            token_type,
            line: token.range.start.line,
            character: token.range.start.character,
            length: token.len(),
            token_modifiers_bitset,
        })
    }

    fn add_semantic_token_absolute(&mut self, abs_sem_token: SemanticTokenAbsoluteParams) {
        let token_type = if let Some(ty) = self.token_type_legend.get(&abs_sem_token.token_type) {
            *ty
        } else {
            return;
        };

        let line = abs_sem_token.line;
        let character = abs_sem_token.character;
        let length = abs_sem_token.length;

        let delta_line = line - self.previous_line;
        let delta_start = if self.previous_line == line {
            character - self.previous_character
        } else {
            character
        };

        self.tokens.push(SemanticToken {
            delta_line,
            delta_start,
            length,
            token_type,
            token_modifiers_bitset: abs_sem_token.token_modifiers_bitset,
        });

        self.previous_line = line;
        self.previous_character = character;
    }
}

impl syntax::Visitor for SemanticTokenizer {
    fn enter_line_comment(
        &mut self,
        _tree: &Ast,
        _path: &mut NodePath,
        _token: &Token,
        trivia: &Trivia,
        _comment: &str,
    ) {
        self.add_semantic_token_absolute(SemanticTokenAbsoluteParams {
            token_type: SemanticTokenType::COMMENT,
            line: trivia.range.start.line,
            character: trivia.range.start.character,
            length: trivia.len(),
            token_modifiers_bitset: 0,
        })
    }

    fn enter_interpreted_token(&mut self, tree: &Ast, path: &mut NodePath, token: &Token) {
        self.add_token_generic(tree, path, token);
    }

    fn enter_skipped_token(
        &mut self,
        tree: &Ast,
        path: &mut NodePath,
        token: &Token,
        _expected: MissingTokenKind,
    ) {
        self.add_token_generic(tree, path, token);
    }
}

#[derive(Debug, Default)]
struct Connection {
    documents: HashMap<Url, Rc<RefCell<Document>>>,
    compiled_results: HashMap<Url, Rc<syntax::Ast>>,
    diagnostics: HashMap<Url, Vec<Diagnostic>>,
    server_options: Option<ServerRegistrationOptions>,
}

/// These options are initialized in `on_initialize()` callback.
#[derive(Debug, Clone)]
struct ServerRegistrationOptions {
    // Semantic tokens
    token_type_legend: Rc<HashMap<SemanticTokenType, u32>>,
    token_modifier_legend: Rc<HashMap<SemanticTokenModifier, u32>>,
}

impl ServerRegistrationOptions {
    pub fn from_semantic_tokens_options(options: &SemanticTokensOptions) -> Self {
        // Register token type legend
        let mut token_type_legend = HashMap::new();
        let mut token_modifier_legend = HashMap::new();

        for (i, token_type) in options.legend.token_types.iter().enumerate() {
            let t = u32::try_from(i).unwrap();
            token_type_legend.insert(token_type.clone(), t);
        }
        for (i, token_modifier) in options.legend.token_modifiers.iter().enumerate() {
            let t = u32::try_from(i).unwrap();
            token_modifier_legend.insert(token_modifier.clone(), t);
        }

        ServerRegistrationOptions {
            token_type_legend: Rc::new(token_type_legend),
            token_modifier_legend: Rc::new(token_modifier_legend),
        }
    }
}

#[derive(Debug)]
struct Document {
    uri: Url,
    text: String,
}

#[allow(clippy::unnecessary_wraps)]
impl Connection {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn send_response<V: Serialize>(&self, id: &Id, value: V) -> Result<(), HandlerError> {
        let value = serde_json::to_value(value)?;
        let response = Response::from_value(id, value);

        self.send_message(&response)
    }

    pub fn send_error(&self, id: &Id, error: ResponseError) -> Result<(), HandlerError> {
        let response = Response::from_error(id, error);
        self.send_message(&response)
    }

    pub fn send_notification<P: Serialize>(
        &self,
        method: &str,
        params: P,
    ) -> Result<(), HandlerError> {
        let params = serde_json::to_value(params)?;
        let notification = Notification {
            jsonrpc: "2.0".to_string(),
            method: method.to_string(),
            params: Some(params),
        };

        self.send_message(&notification)
    }

    fn send_message<S: Serialize>(&self, message: &S) -> Result<(), HandlerError> {
        let mut writer = io::stdout();
        let json = serde_json::to_vec(message)?;

        write!(writer, "Content-Length: {}\r\n\r\n", json.len())?;
        writer.write_all(json.as_slice())?;
        writer.flush()?;

        Ok(())
    }

    fn publish_diagnostics(&self, uri: &Url) -> Result<(), HandlerError> {
        let diagnostic = self.get_diagnostics(uri)?;

        let publish_diagnostics_params = PublishDiagnosticsParams {
            uri: uri.clone(),
            version: None,
            diagnostics: diagnostic.clone(),
        };

        self.send_notification(
            "textDocument/publishDiagnostics",
            publish_diagnostics_params,
        )
    }

    fn server_options(&self) -> Result<&ServerRegistrationOptions, HandlerError> {
        self.server_options.as_ref().ok_or(HandlerError {
            kind: HandlerErrorKind::ServerNotInitialized,
        })
    }

    fn get_document(&self, uri: &Url) -> Result<&Rc<RefCell<Document>>, HandlerError> {
        self.documents.get(uri).ok_or_else(|| HandlerError {
            kind: HandlerErrorKind::DocumentNotFound(uri.clone()),
        })
    }

    fn get_compiled_result(&self, uri: &Url) -> Result<&Rc<Ast>, HandlerError> {
        self.compiled_results.get(uri).ok_or_else(|| HandlerError {
            kind: HandlerErrorKind::DocumentNotFound(uri.clone()),
        })
    }

    fn get_diagnostics(&self, uri: &Url) -> Result<&Vec<Diagnostic>, HandlerError> {
        self.diagnostics.get(uri).ok_or_else(|| HandlerError {
            kind: HandlerErrorKind::DocumentNotFound(uri.clone()),
        })
    }

    fn compile(&mut self, uri: &Url) -> Result<Rc<Ast>, HandlerError> {
        let doc = self.get_document(uri)?;
        let node = Rc::new(Parser::parse_string(&doc.borrow().text));

        // Diagnostics
        let mut diagnostics = DiagnosticsCollector::new();
        syntax::traverse(&mut diagnostics, &node);

        self.compiled_results.insert(uri.clone(), Rc::clone(&node));
        self.diagnostics
            .insert(uri.clone(), diagnostics.diagnostics);

        Ok(node)
    }

    // Request callbacks
    fn on_initialize(
        &mut self,
        params: &InitializeParams,
    ) -> Result<InitializeResult, HandlerError> {
        info!("[initialize] {:?}", params);

        let capabilities = ServerCapabilitiesBuilder::new()
            .initialized(&params)
            .semantic_token_types(&[
                SemanticTokenType::KEYWORD,
                SemanticTokenType::VARIABLE,
                SemanticTokenType::STRING,
                SemanticTokenType::NUMBER,
                SemanticTokenType::OPERATOR,
                SemanticTokenType::COMMENT,
                SemanticTokenType::STRUCT,
                SemanticTokenType::FUNCTION,
                SemanticTokenType::PARAMETER,
                SemanticTokenType::PROPERTY,
            ])
            .semantic_token_modifiers(&[
                SemanticTokenModifier::DECLARATION,
                SemanticTokenModifier::DEFINITION,
                SemanticTokenModifier::READONLY,
                SemanticTokenModifier::STATIC,
                SemanticTokenModifier::DEPRECATED,
                SemanticTokenModifier::ABSTRACT,
                SemanticTokenModifier::ASYNC,
                SemanticTokenModifier::MODIFICATION,
                SemanticTokenModifier::DOCUMENTATION,
                SemanticTokenModifier::DEFAULT_LIBRARY,
            ])
            .build();

        if let Some(ref semantic_tokens_provider) = capabilities.semantic_tokens_provider {
            match semantic_tokens_provider {
                SemanticTokensServerCapabilities::SemanticTokensOptions(options) => {
                    self.server_options = Some(
                        ServerRegistrationOptions::from_semantic_tokens_options(options),
                    );
                }
                SemanticTokensServerCapabilities::SemanticTokensRegistrationOptions(options) => {
                    self.server_options =
                        Some(ServerRegistrationOptions::from_semantic_tokens_options(
                            &options.semantic_tokens_options,
                        ));
                }
            }
        }

        Ok(InitializeResult {
            capabilities,
            server_info: Some(ServerInfo {
                name: "nico-ls".to_string(),
                version: Some("0.0.1".to_string()),
            }),
        })
    }

    fn on_text_document_semantic_tokens_full(
        &self,
        params: &SemanticTokensParams,
    ) -> Result<SemanticTokens, HandlerError> {
        info!("[on_text_document_semantic_tokens_full] {:?}", params);
        let node = self.get_compiled_result(&params.text_document.uri)?;

        let server_options = self.server_options()?;

        let mut tokenizer = SemanticTokenizer::new(
            &server_options.token_type_legend,
            &server_options.token_modifier_legend,
        );

        syntax::traverse(&mut tokenizer, &node);

        Ok(SemanticTokens {
            data: tokenizer.tokens,
            result_id: None,
        })
    }

    fn on_text_document_hover(&self, params: &HoverParams) -> Result<Option<Hover>, HandlerError> {
        info!("[on_text_document_hover] {:?}", params);
        let uri = &params.text_document_position_params.text_document.uri;
        let node = self.get_compiled_result(uri)?;
        let mut hover = ls::Hover::new(syntax_position(
            params.text_document_position_params.position,
        ));

        if let Some((value, range)) = hover.describe(node.as_ref()) {
            return Ok(Some(Hover {
                range: Some(lsp_range(range)),
                contents: HoverContents::Markup(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: value.to_string(),
                }),
            }));
        }

        Ok(None)
    }

    fn on_text_document_prepare_rename(
        &self,
        params: &TextDocumentPositionParams,
    ) -> Result<Option<PrepareRenameResponse>, HandlerError> {
        info!("[on_text_document_prepare_rename] {:?}", params);
        let tree = self.get_compiled_result(&params.text_document.uri)?;
        let mut rename = ls::Rename::new(syntax_position(params.position));

        if let Some(id) = rename.prepare(tree) {
            return Ok(Some(PrepareRenameResponse::RangeWithPlaceholder {
                range: lsp_range(id.range(tree)),
                placeholder: id.to_string(),
            }));
        }

        Ok(None)
    }

    fn on_text_document_rename(
        &mut self,
        params: &RenameParams,
    ) -> Result<Option<WorkspaceEdit>, HandlerError> {
        info!("[on_text_document_prepare_rename] {:?}", params);
        let uri = &params.text_document_position.text_document.uri;
        let tree = self.get_compiled_result(uri)?;
        let mut rename = ls::Rename::new(syntax_position(params.text_document_position.position));

        if rename.prepare(&tree).is_some() {
            if let Some(ranges) = rename.rename(tree) {
                let edits = ranges
                    .iter()
                    .map(|r| TextEdit::new(lsp_range(*r), params.new_name.clone()))
                    .collect();

                return Ok(Some(WorkspaceEdit {
                    changes: Some(vec![(uri.clone(), edits)].into_iter().collect()),
                    document_changes: None,
                    change_annotations: None,
                }));
            }
        }

        Ok(None)
    }

    // Notification callbacks
    fn on_initialized(&self, params: &InitializedParams) -> Result<(), HandlerError> {
        info!("[initialized] {:?}", params);
        Ok(())
    }

    fn on_text_document_did_open(
        &mut self,
        params: &DidOpenTextDocumentParams,
    ) -> Result<(), HandlerError> {
        info!("[on_text_document_did_open] {:?}", params);

        let doc = Document::from(&params.text_document);
        let doc = Rc::new(RefCell::new(doc));

        self.documents
            .insert(doc.borrow().uri.clone(), Rc::clone(&doc));

        self.compile(&doc.borrow().uri)?;
        self.publish_diagnostics(&doc.borrow().uri)?;

        Ok(())
    }

    fn on_text_document_did_change(
        &mut self,
        params: &DidChangeTextDocumentParams,
    ) -> Result<(), HandlerError> {
        info!("[on_text_document_did_change] {:?}", params);
        {
            let doc = self.get_document(&params.text_document.uri)?;

            for change in &params.content_changes {
                let mut doc = doc.borrow_mut();

                if let Some(range) = &change.range {
                    doc.replace_range(range, &change.text);
                }
            }
        }

        self.compile(&params.text_document.uri)?;
        self.publish_diagnostics(&params.text_document.uri)?;

        Ok(())
    }
}

impl From<&TextDocumentItem> for Document {
    fn from(item: &TextDocumentItem) -> Self {
        Self {
            uri: item.uri.clone(),
            text: item.text.clone(),
        }
    }
}

impl Document {
    fn replace_range(&mut self, range: &lsp_types::Range, replace_with: &str) {
        // Since the Range passed in LSP is the editor's row and column,
        // we need to calculate the string range from there.
        let mut text_start = None;
        let mut text_end = None;

        let mut i: usize = 0;
        let mut lineno: u32 = 0;
        let mut columnno: u32 = 0;

        for c in self.text.chars() {
            if range.start.line == lineno && range.start.character == columnno {
                text_start = Some(i);
            }
            if range.end.line == lineno && range.end.character == columnno {
                text_end = Some(i);
            }

            i += 1;
            if c == '\n' {
                lineno += 1;
                columnno = 0;
            } else {
                columnno += 1;
            }
        }

        // The above iteration algorithm can't capture locations at the termination.
        if range.start.line == lineno && range.start.character == columnno {
            text_start = Some(i);
        }
        if range.end.line == lineno && range.end.character == columnno {
            text_end = Some(i);
        }

        if let Some(text_start) = text_start {
            if let Some(text_end) = text_end {
                //info!("text_start:{} text_end:{}", text_start, text_end);
                self.text.replace_range(text_start..text_end, replace_with);
            }
        }
    }
}

// --- Event Loop

fn event_loop_main(conn: &mut Connection) -> Result<(), HandlerError> {
    let mut content_length: Option<usize> = None;

    // Header Part
    // https://microsoft.github.io/language-server-protocol/specifications/specification-current/#headerPart
    //
    // HTTP header field
    // -----------------
    // Each header field consists of a case-insensitive field name followed by a colon (":"), optional leading
    // whitespace, the field value, and optional trailing whitespace.
    // https://tools.ietf.org/html/rfc7230#section-3.2
    loop {
        let mut header = String::new();

        io::stdin().read_line(&mut header)?;

        info!("line: {:?}", header);

        if header == "\r\n" {
            // ‘\r\n’ sequences always immediately precede the content part of a message.
            break;
        }

        let name_value = header.splitn(2, ':').collect::<Vec<_>>();

        if name_value.len() != 2 {
            warn!("Received illegal formatted header: {}", header);
            todo!("Error notification and return");
        }

        let name = name_value[0].trim().to_ascii_lowercase();
        let value = name_value[1].trim().to_ascii_lowercase();

        if name == "content-length" {
            match value.parse::<usize>() {
                Ok(length) => {
                    content_length = Some(length);
                }
                Err(e) => {
                    warn!("Received invalid content-length : {} - {}", value, e);
                    todo!("Error notification and return");
                }
            }
        }
    }

    // Content Part
    let content_length = content_length.expect("Content-Length is mandatory");

    let bytes: Vec<u8> = io::stdin()
        .bytes()
        .take(content_length)
        .map(|r: Result<u8, _>| r.unwrap())
        .collect();

    let string = String::from_utf8(bytes)?;
    let value = serde_json::from_str::<Value>(&string)?;
    let mut request = serde_json::from_value::<Request>(value)?;
    let request_id = request.id.clone();

    match request.method.as_str() {
        // Requests
        "initialize" => {
            let params = request.take_params::<InitializeParams>()?;
            let result = conn.on_initialize(&params)?;

            conn.send_response(&request_id.unwrap(), result)?;
        }
        "textDocument/semanticTokens/full" => {
            let params = request.take_params::<SemanticTokensParams>()?;
            let result = conn.on_text_document_semantic_tokens_full(&params)?;

            conn.send_response(&request_id.unwrap(), result)?;
        }
        "textDocument/hover" => {
            let params = request.take_params::<HoverParams>()?;

            let result = conn.on_text_document_hover(&params)?;
            conn.send_response(&request_id.unwrap(), result)?;
        }
        "textDocument/prepareRename" => {
            let params = request.take_params::<TextDocumentPositionParams>()?;

            let result = conn.on_text_document_prepare_rename(&params)?;
            conn.send_response(&request_id.unwrap(), result)?;
        }
        "textDocument/rename" => {
            let params = request.take_params::<RenameParams>()?;

            let result = conn.on_text_document_rename(&params)?;
            conn.send_response(&request_id.unwrap(), result)?;
        }
        // Notifications
        "initialized" => {
            let params = request.take_params::<InitializedParams>()?;
            conn.on_initialized(&params)?;
        }
        "textDocument/didOpen" => {
            let params = request.take_params::<DidOpenTextDocumentParams>()?;
            conn.on_text_document_did_open(&params)?;
        }
        "textDocument/didChange" => {
            let params = request.take_params::<DidChangeTextDocumentParams>()?;
            conn.on_text_document_did_change(&params)?;
        }
        _ => {
            warn!("[unknown] {:?}", request);
        }
    };

    Ok(())
}

fn main() {
    env_logger::init();
    info!("Launching language server...");

    let mut connection = Connection::new();

    loop {
        if let Err(err) = event_loop_main(&mut connection) {
            if let HandlerErrorKind::GenericError {
                ref id,
                ref message,
            } = err.kind
            {
                connection
                    .send_error(
                        id,
                        ResponseError {
                            code: ResponseErrorCode::InternalError,
                            message: message.clone(),
                            data: None,
                        },
                    )
                    .expect("couldn't send error");
            } else {
                todo!("Handle error or send notification to the client: {:?}", err)
            }
        }
    }
}
