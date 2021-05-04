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

const cases: [string, { name: string; initialize: any }[]][] = [
  [
    "rename",
    [
      {
        name: "prepare support : on",
        initialize: { rename: true }
      },
      {
        name: "prepare support : off",
        initialize: {
          rename: {
            dynamicRegistration: false,
            prepareSupport: false,
            prepareSupportDefaultBehavior: 1,
            honorsChangeAnnotations: false
          }
        }
      }
    ]
  ],
  [
    "signatureHelp",
    [
      {
        name: "signatureHelp : on",
        initialize: {
          signatureHelp: true
        }
      }
    ]
  ],
  [
    "hover",
    [
      {
        name: "hover : on",
        initialize: {
          hover: true
        }
      }
    ]
  ]
];

cases.forEach(([description, tests], i) => {
  describe(description, () => {
    tests.forEach(({ name, initialize }, j) => {
      test(name, async done => {
        const server = LanguageServer.spawn();
        const builder = new RequestBuilder({ id: (i + 1) * 1000 + j });

        const request = builder.initialize(initialize);
        const response = await server.sendRequest(request);
        expect(response).toMatchSnapshot();

        server.on("exit", done);
        server.stop();
      });
    });
  });
});
