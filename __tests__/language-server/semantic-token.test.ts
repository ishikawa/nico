import { LanguageServer, LanguageServerAgent, spawn_server } from "../util/lsp";
import fs from "fs";
import glob from "glob";
import { filterTestCases, TestCaseBase, readTestFileSync, getTestName } from "../util/testcase";

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
    // prettier-ignore
    input: [
      "struct Rectangle { width: i32, height: i32 }",
      "Rectangle { width: 100, height: 200 }"
    ].join("\n")
  },
  {
    // prettier-ignore
    input: [
      "struct A { b: i32 }",
      "let a = A { b: 123 }",
      "a.b"
    ].join("\n")
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
    const agent = new LanguageServerAgent(server!, { sequence: i });

    // Open document and no compilation errors
    const diagnostics = await agent.openDocument(name, src);
    expect(diagnostics).toHaveLength(0);

    const response = await agent.textDocumentSemanticTokenFull(name);
    expect(response).toMatchSnapshot();

    done();
  });
});
