import { LanguageServer, NotificationMessage, RequestBuilder } from "../util/lsp";
import fs from "fs";
import glob from "glob";

interface TestCase {
  input?: string;
  file?: string;
}

let server: LanguageServer | undefined;

beforeAll(async () => {
  const builder = new RequestBuilder({ id: 1 });
  server = LanguageServer.spawn();

  // initialize
  {
    const request = builder.initialize();
    await server.sendRequest(request);
  }

  // initialized
  {
    const notification = builder.initialized();
    await server.sendNotification(notification);
  }
});

afterAll(() => {
  if (server) {
    return server.stop();
  }
});

let cases: TestCase[] = [
  {
    input: ""
  },
  {
    input: "# comment"
  },
  {
    input: "1"
  },
  {
    input: "1 + 2"
  },
  {
    input: "struct Rectangle { width: i32, height: i32 }"
  },
  {
    input: "Rectangle { width: 100, height: 200 }"
  },
  {
    input: "a.b"
  }
];

// Add samples files
cases = cases.concat(
  glob.sync("./samples/**/*.nico").map(path => ({
    file: path
  }))
);

cases.forEach((testCase, i) => {
  let src = "";
  let name = "-";

  if (testCase.input) {
    src = testCase.input;
    name = src;
  } else if (testCase.file) {
    const srcBuffer = fs.readFileSync(testCase.file);
    src = srcBuffer.toString("utf-8");
    name = testCase.file;
  }

  // No compilation errors and semantic tokens
  test(`${i}: open a document at \`${name}\``, async done => {
    const builder = new RequestBuilder({ id: 1000 + 1 });
    const uri = `file:///home/user/nico/sample${i}.nico`;

    // Open document and no compilation errors
    {
      const nextNotification = server!.nextMessage<NotificationMessage>();
      const notification1 = builder.textDocumentDidOpen(uri, src);
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
      const request = builder.textDocumentSemanticTokenFull(uri);
      const response = await server?.sendRequest(request);

      expect(response).toMatchSnapshot();
    }

    done();
  });
});
