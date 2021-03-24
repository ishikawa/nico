use log::{info, warn};
use lsp_types::InitializeParams;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::io;
use std::io::Read;

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
    id: Id,
    method: String,
    params: Option<Value>,
}

fn main() {
    env_logger::init();

    info!("Launching language server...");

    loop {
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

            io::stdin()
                .read_line(&mut header)
                .expect("Failed to read line");

            info!("line: {:?}", header);

            if header == "\r\n" {
                // ‘\r\n’ sequences always immediately precede the content part of a message.
                break;
            }

            let name_value = header.splitn(2, ':').collect::<Vec<_>>();

            if name_value.len() != 2 {
                warn!("Received illegal formatted header: {}", header);
                continue;
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
                        continue;
                    }
                }
            }
        }

        // Content Part
        if let Some(content_length) = content_length {
            let bytes: Vec<u8> = io::stdin()
                .bytes()
                .take(content_length)
                .map(|r: Result<u8, _>| r.unwrap())
                .collect();

            let string = match String::from_utf8(bytes) {
                Ok(s) => s,
                Err(e) => {
                    warn!(
                        "Couldn't convert {} bytes into string : {}",
                        content_length, e
                    );
                    continue;
                }
            };

            let value = match serde_json::from_str::<Value>(&string) {
                Ok(value) => value,
                Err(e) => {
                    warn!("JSON parse error : {} - {}", e, &string);
                    continue;
                }
            };

            let request = match serde_json::from_value::<Request>(value) {
                Ok(request) => request,
                Err(e) => {
                    warn!("JSON-RPC parse error : {} - {}", e, &string);
                    continue;
                }
            };

            match request.method.as_str() {
                "initialize" => {
                    match serde_json::from_value::<InitializeParams>(request.params.unwrap()) {
                        Ok(params) => {
                            info!("[initialize] {:?}", params);
                        }
                        Err(e) => {
                            warn!("initialize: parse error : {} - {}", e, &string);
                        }
                    };
                }
                _ => {
                    warn!("[unknown] {:?}", request);
                }
            };
        }
    }
}
