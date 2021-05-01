import { LanguageServer, NotificationMessage, RequestBuilder, spawn_server } from "../util/lsp";
import fs from "fs";
import glob from "glob";
import { filterTestCases, TestCaseBase, readTestFileSync, getTestName, getDocumentUri } from "../util/testcase";

let server: LanguageServer | undefined;

beforeAll(async () => {
  server = await spawn_server();
});

afterAll(() => {
  if (server) {
    return server.stop();
  }
});

let cases: TestCaseBase[] = [
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
    input: ["struct A { b: i32 }", "let a = A { b: 123 }", "a.b"].join("\n")
  }
];

// Add samples files
cases = cases.concat(
  glob.sync("./samples/**/*.nico").map(path => ({
    file: path
  }))
);

filterTestCases(cases).forEach((testCase, i) => {
  let src = readTestFileSync(testCase);
  let name = getTestName(testCase);

  // No compilation errors and semantic tokens
  test(`${i}: open a document at \`${name}\``, async done => {
    const builder = new RequestBuilder({ id: 1000 + i });
    const uri = getDocumentUri(i);

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
