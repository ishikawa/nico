use log::{info, warn};
use serde_json::Value;
use std::io;
use std::io::Read;

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
            let m: Vec<u8> = io::stdin()
                .bytes()
                .take(content_length)
                .map(|r: Result<u8, _>| r.unwrap())
                .collect();

            match serde_json::from_slice::<Value>(m.as_slice()) {
                Ok(v) => {
                    info!("[JSON] {}", v);
                }
                Err(e) => {
                    warn!("Received invalid json-rpc : {}", e);
                }
            }
        }
    }
}
