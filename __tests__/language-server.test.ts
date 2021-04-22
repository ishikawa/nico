import { spawn } from "child_process";

test("Language Server", async done => {
  const server = spawn("./target/debug/nico-ls", [], {
    env: {
      RUST_LOG: "info",
      RUST_BACKTRACE: "full"
    }
  });

  // Initialize - params
  const params = {
    trace: "verbose",
    capabilities: {
      textDocument: {
        publishDiagnostics: {
          relatedInformation: true,
          versionSupport: false,
          tagSupport: {
            valueSet: [1, 2]
          },
          codeDescriptionSupport: true,
          dataSupport: true
        }
      },
      semanticTokens: {
        dynamicRegistration: true,
        tokenTypes: [
          "namespace",
          "type",
          "class",
          "enum",
          "interface",
          "struct",
          "typeParameter",
          "parameter",
          "variable",
          "property",
          "enumMember",
          "event",
          "function",
          "method",
          "macro",
          "keyword",
          "modifier",
          "comment",
          "string",
          "number",
          "regexp",
          "operator"
        ],
        tokenModifiers: [
          "declaration",
          "definition",
          "readonly",
          "static",
          "deprecated",
          "abstract",
          "async",
          "modification",
          "documentation",
          "defaultLibrary"
        ],
        formats: ["relative"],
        requests: {
          range: true,
          full: {
            delta: true
          }
        },
        multilineTokenSupport: false,
        overlappingTokenSupport: false
      },
      linkedEditingRange: {
        dynamicRegistration: true
      }
    }
  };

  const request = {
    jsonrpc: "2.0",
    id: 1,
    method: "initialize",
    params
  };

  const payload = JSON.stringify(request);

  // Write a request

  server.stdin.write(`Content-Length: ${payload.length}\r\n`);
  server.stdin.write("\r\n");
  server.stdin.write(payload);

  server.stdout.on("data", data => {
    const message = parseJsonRpcMessage(data);

    expect(message).toEqual({
      jsonrpc: "2.0",
      id: 1,
      result: {
        capabilities: {
          semanticTokensProvider: {
            full: true,
            legend: {
              tokenModifiers: [
                "declaration",
                "definition",
                "readonly",
                "static",
                "deprecated",
                "abstract",
                "async",
                "modification",
                "documentation",
                "defaultLibrary"
              ],
              tokenTypes: [
                "keyword",
                "variable",
                "string",
                "number",
                "operator",
                "comment",
                "function",
                "struct",
                "function",
                "parameter",
                "property"
              ]
            }
          },
          textDocumentSync: 2
        },
        serverInfo: { name: "nico-ls", version: "0.0.1" }
      },
      error: null
    });
  });

  server.stderr.on("data", data => {
    console.warn(`stderr: ${data}`);
  });

  server.on("close", code => {
    console.log(`child process closed with code ${code}`);
    done();
  });

  setTimeout(() => {
    if (!server.killed) {
      server.kill();
    }
  }, 1000);
});

function parseJsonRpcMessage(data: string | Buffer): any {
  // For simplicity, we assume whole payload arrived at once.
  const payload = data instanceof Buffer ? data.toString("utf-8") : data;

  // Split payload into header and content.
  const parts = payload.split("\r\n", 4);

  // The last element is "Content-Part"
  return JSON.parse(parts[parts.length - 1]);
}
