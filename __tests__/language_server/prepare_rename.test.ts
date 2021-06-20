import { LanguageServer, spawn_server, LanguageServerAgent, Position } from "../util/lsp";
import { filterTestCases, TestCaseBase, readTestFileSync, getTestName } from "../util/testcase";

interface TestCase extends TestCaseBase {
  position: Position[];
}

let server: LanguageServer | undefined;

beforeAll(async () => {
  server = await spawn_server({ rename: true });
});

afterAll(() => {
  if (server) {
    return server.stop();
  }
});

let cases: TestCase[] = [
  {
    // prettier-ignore
    input: [
      "struct A { b: i32 }",
      "",
      "let a = A { b: 123 }",
      "a.b"
    ].join("\n"),
    position: [
      // a
      {
        line: 3,
        character: 0
      },
      {
        line: 3,
        character: 1
      },
      // b
      {
        line: 3,
        character: 3
      }
    ]
  },
  // function name
  {
    // prettier-ignore
    input: [
      "fun bar()",
      "    100",
      "end",
      "",
      "bar()"
    ].join("\n"),
    position: [
      // bar
      {
        line: 4,
        character: 3
      }
    ]
  },
  // function parameter
  {
    // prettier-ignore
    input: [
      "fun foo(x: Int)",
      "    x",
      "end",
    ].join("\n"),
    position: [
      // x
      {
        line: 0,
        character: 8
      }
    ]
  }
];

filterTestCases(cases).forEach((testCase, i) => {
  let src = readTestFileSync(testCase);
  let name = getTestName(testCase);

  testCase.position.forEach((position, j) => {
    test(`${i}: prepare rename - \`${name}\` at ${position}`, async done => {
      const agent = new LanguageServerAgent(server!, { sequence: [i, j] });

      // Open document and no compilation errors
      const diagnostics = await agent.openDocument(name, src);
      expect(diagnostics).toHaveLength(0);

      const response = await agent.prepareRename(name, position);
      expect(response).toMatchSnapshot();

      done();
    });
  });
});
