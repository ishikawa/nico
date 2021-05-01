import { LanguageServer, LanguageServerAgent, spawn_server } from "../util/lsp";
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
  // Undefined variable
  {
    input: "a"
  },
  // Defined variable
  {
    // prettier-ignore
    input: [
      "let a = 1",
      "a"
    ].join("\n")
  },
  // Block scope
  {
    // prettier-ignore
    input: [
      "if 3 > 0",
      "    let a = 1",
      "    println_i32(a)",
      "end",
      "a" // `a` should not be visible in this scope.
    ].join("\n")
  },
  {
    // prettier-ignore
    input: [
      "case 3",
      "when x if x == 3",
      "    println_i32(x)",
      "else",
      "    println_i32(10)",
      "end",
      "x" // `x` should not be visible in this scope.
    ].join("\n")
  }
];

filterTestCases(cases).forEach((testCase, i) => {
  let src = readTestFileSync(testCase);
  let name = getTestName(testCase);

  // No compilation errors and semantic tokens
  test(`${i}: publishDiagnostics at \`${name}\``, async done => {
    const agent = new LanguageServerAgent(server!, { sequence: i });

    const diagnostics = await agent.openDocument(name, src);
    expect(diagnostics).toMatchSnapshot();

    done();
  });
});
