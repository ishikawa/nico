use log::{info, warn};
use lsp_types::{
    DidChangeTextDocumentParams, DidOpenTextDocumentParams, InitializeParams, InitializeResult,
    InitializedParams, SemanticTokenType, SemanticTokensFullOptions, SemanticTokensLegend,
    SemanticTokensOptions, SemanticTokensServerCapabilities, ServerCapabilities, ServerInfo,
    TextDocumentItem, TextDocumentSyncCapability, TextDocumentSyncKind,
};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::cell::RefCell;
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
    code: i32,
    message: String,
    data: Option<Value>,
}

#[derive(Debug)]
struct HandlerError {
    kind: HandlerErrorKind,
}

#[derive(Debug)]
enum HandlerErrorKind {
    // Errors
    Utf8Error(string::FromUtf8Error),
    IoError(io::Error),
    JsonError(serde_json::Error),

    // Warnings
    InvalidParams,
    DocumentNotFound(Url),
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
    fn from_value(request: &Request, value: Value) -> Self {
        Self {
            jsonrpc: request.jsonrpc.clone(),
            id: request.id.clone().unwrap_or_else(|| Id::Int(-1)),
            result: Some(value),
            error: None,
        }
    }

    fn serialize_write<T: Write>(&self, writer: &mut T) -> Result<(), HandlerError> {
        let json = serde_json::to_vec(self)?;

        write!(writer, "Content-Length: {}\r\n\r\n", json.len())?;
        writer.write_all(json.as_slice())?;
        writer.flush()?;

        Ok(())
    }
}

// --- Language Server States

#[derive(Debug, Default)]
struct Connection {
    documents: HashMap<Url, Rc<RefCell<Document>>>,
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

    fn get_document(&self, uri: &Url) -> Result<&Rc<RefCell<Document>>, HandlerError> {
        self.documents.get(uri).ok_or_else(|| HandlerError {
            kind: HandlerErrorKind::DocumentNotFound(uri.clone()),
        })
    }

    // Request callbacks
    fn on_initialize(&self, params: &InitializeParams) -> Result<InitializeResult, HandlerError> {
        info!("[initialize] {:?}", params);

        let legend = SemanticTokensLegend {
            token_types: vec![SemanticTokenType::KEYWORD],
            token_modifiers: vec![],
        };

        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::Incremental,
                )),
                semantic_tokens_provider: Some(
                    SemanticTokensServerCapabilities::SemanticTokensOptions(
                        SemanticTokensOptions {
                            legend,
                            full: Some(SemanticTokensFullOptions::Bool(true)),
                            ..SemanticTokensOptions::default()
                        },
                    ),
                ),
                ..ServerCapabilities::default()
            },
            server_info: Some(ServerInfo {
                name: "nico-ls".to_string(),
                version: Some("0.0.1".to_string()),
            }),
        })
    }

    fn on_initialized(&self, params: &InitializedParams) -> Result<(), HandlerError> {
        info!("[initialized] {:?}", params);
        Ok(())
    }

    // Notification callbacks
    fn on_text_document_did_open(
        &mut self,
        params: &DidOpenTextDocumentParams,
    ) -> Result<(), HandlerError> {
        info!("[on_text_document_did_open] {:?}", params);

        let doc = Document::from(&params.text_document);

        self.documents
            .insert(doc.uri.clone(), Rc::new(RefCell::new(doc)));

        Ok(())
    }

    fn on_text_document_did_change(
        &mut self,
        params: &DidChangeTextDocumentParams,
    ) -> Result<(), HandlerError> {
        info!("[on_text_document_did_change] {:?}", params);

        let doc = self.get_document(&params.text_document.uri)?;

        for change in &params.content_changes {
            let mut doc = doc.borrow_mut();

            if let Some(range) = &change.range {
                doc.replace_range(range, &change.text);
            }
        }

        //info!("  => {}", doc.borrow().text);
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

fn write_response<T: Write, V: Serialize>(
    writer: &mut T,
    request: &Request,
    value: V,
) -> Result<(), HandlerError> {
    let value = serde_json::to_value(value)?;
    let response = Response::from_value(&request, value);

    response.serialize_write(writer)
}

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

    match request.method.as_str() {
        // Requests
        "initialize" => {
            let params = request.take_params::<InitializeParams>()?;
            let result = conn.on_initialize(&params)?;
            write_response(&mut io::stdout(), &request, result)?;
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
            todo!("Handle error or send notification to the client: {:?}", err)
        }
    }
}
