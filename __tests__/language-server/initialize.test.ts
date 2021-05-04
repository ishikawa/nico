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

describe("rename", () => {
  test("prepare support : on", async done => {
    const server = LanguageServer.spawn();
    const builder = new RequestBuilder({ id: 4760 });

    const request = builder.initialize({ rename: true });
    const response = await server.sendRequest(request);
    expect(response).toMatchSnapshot();

    server.on("exit", done);
    server.stop();
  });

  test("prepare support : off", async done => {
    const server = LanguageServer.spawn();
    const builder = new RequestBuilder({ id: 4761 });

    const request = builder.initialize({
      rename: {
        dynamicRegistration: false,
        prepareSupport: false,
        prepareSupportDefaultBehavior: 1,
        honorsChangeAnnotations: false
      }
    });

    const response = await server.sendRequest(request);
    expect(response).toMatchSnapshot();

    server.on("exit", done);
    server.stop();
  });
});

describe("signatureHelp", () => {
  test("signatureHelp : on", async done => {
    const server = LanguageServer.spawn();
    const builder = new RequestBuilder({ id: 4760 });

    const request = builder.initialize({ signatureHelp: true });
    const response = await server.sendRequest(request);
    expect(response).toMatchSnapshot();

    server.on("exit", done);
    server.stop();
  });
});
