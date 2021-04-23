import { LanguageServer, buildInitialize, buildInitialized } from "../util/lsp";

test("initialize", async done => {
  const server = LanguageServer.spawn();

  const request = buildInitialize();
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

  // initialized
  {
    const notification = buildInitialized();
    await server.sendNotification(notification);
  }

  expect(server.isStopped()).toBeFalsy();

  server.on("exit", done);
  server.stop();
});
