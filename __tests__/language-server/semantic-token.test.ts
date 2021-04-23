import {
  LanguageServer,
  NotificationMessage,
  buildInitialize,
  buildInitialized,
  buildTextDocumentDidOpen,
  buildTextDocumentSemanticTokenFull
} from "../util/lsp";

let server: LanguageServer | undefined;

beforeAll(async () => {
  server = LanguageServer.spawn();

  // initialize
  {
    const request = buildInitialize();
    await server.sendRequest(request);
  }

  // initialized
  {
    const notification = buildInitialized();
    await server.sendNotification(notification);
  }
});

afterAll(() => {
  if (server) {
    return server.stop();
  }
});

test("open a document", async done => {
  const uri = "file:///home/user/nico/sample.nico";

  // Open document and no compilation errors
  {
    const nextNotification = server!.nextMessage<NotificationMessage>();
    const notification1 = buildTextDocumentDidOpen(uri, "1 + 2");
    await server!.sendNotification(notification1);

    const notification2 = await nextNotification;
    expect(notification2).toEqual({
      jsonrpc: "2.0",
      method: "textDocument/publishDiagnostics",
      // no errors
      params: { diagnostics: [], uri }
    });
  }

  // Semantic coloring
  {
    const request = buildTextDocumentSemanticTokenFull(uri);
    const response = await server?.sendRequest(request);

    expect(response).toEqual({
      id: request.id,
      jsonrpc: "2.0",
      result: {
        data: [0, 0, 1, 3, 0, 0, 2, 1, 4, 0, 0, 2, 1, 3, 0]
      },
      error: null
    });
  }

  done();
});
