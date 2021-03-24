use log::{info, warn};
use lsp_types::{
    ColorProviderCapability, DidOpenTextDocumentParams, InitializeParams, InitializeResult,
    ServerCapabilities, ServerInfo, TextDocumentSyncCapability, TextDocumentSyncKind,
};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::io::{Read, Write};
use std::{io, string};

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
    UTF8Error(string::FromUtf8Error),
    IOError(io::Error),
    JSONError(serde_json::Error),

    // Warnings
    InvalidParams,
}

impl From<io::Error> for HandlerError {
    fn from(err: io::Error) -> Self {
        Self {
            kind: HandlerErrorKind::IOError(err),
        }
    }
}

impl From<string::FromUtf8Error> for HandlerError {
    fn from(err: string::FromUtf8Error) -> Self {
        Self {
            kind: HandlerErrorKind::UTF8Error(err),
        }
    }
}

impl From<serde_json::Error> for HandlerError {
    fn from(err: serde_json::Error) -> Self {
        Self {
            kind: HandlerErrorKind::JSONError(err),
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
}

fn event_loop_main() -> Result<(), HandlerError> {
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
            info!("[initialize] {:?}", params);

            let result = InitializeResult {
                capabilities: ServerCapabilities {
                    text_document_sync: Some(TextDocumentSyncCapability::Kind(
                        TextDocumentSyncKind::Full,
                    )),

                    color_provider: Some(ColorProviderCapability::Simple(true)),
                    ..ServerCapabilities::default()
                },
                server_info: Some(ServerInfo {
                    name: "nico-ls".to_string(),
                    version: Some("0.0.1".to_string()),
                }),
            };

            let value = serde_json::to_value(result)?;
            let response = Response::from_value(&request, value);
            let json = serde_json::to_vec(&response)?;

            write!(io::stdout(), "Content-Length: {}\r\n\r\n", json.len())?;
            io::stdout().write_all(json.as_slice())?;
            io::stdout().flush()?;
        }
        // Notifications
        "textDocument/didOpen" => {
            let params = request.take_params::<DidOpenTextDocumentParams>()?;
            info!("[textDocument/didOpen] {:?}", params);
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
    loop {
        if let Err(err) = event_loop_main() {
            todo!("Handle error or send notification to the client: {:?}", err)
        }
    }
}
