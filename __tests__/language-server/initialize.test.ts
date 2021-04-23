import { LanguageServer, RequestBuilder } from "../util/lsp";

test("initialize", async done => {
  const server = LanguageServer.spawn();
  const builder = new RequestBuilder({ id: 4760 });

  const request = builder.initialize();
  const response = await server.sendRequest(request);

  expect(response).toMatchSnapshot();

  // initialized
  {
    const notification = builder.initialized();
    await server.sendNotification(notification);
  }

  expect(server.isStopped()).toBeFalsy();

  server.on("exit", done);
  server.stop();
});
