import { LanguageServer, buildRequest } from "./util/lsp";

test("initialize", async done => {
  const server = LanguageServer.spawn();

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

  const request = buildRequest("initialize", params);
  const response = await server.sendRequest(request);

  expect(response).toEqual({
    jsonrpc: "2.0",
    id: request.id,
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

  server.on("exit", done);
  server.stop();
});
