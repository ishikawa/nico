import { LanguageServer, spawn_server, LanguageServerAgent, Position } from "../util/lsp";
import { filterTestCases, TestCaseBase, readTestFileSync, getTestName } from "../util/testcase";

interface TestCase extends TestCaseBase {
  requests: Array<{ position: Position; newName: string }>;
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
    requests: [
      {
        position: {
          line: 4,
          character: 3
        },
        newName: "bar"
      }
    ]
  },
  // struct name
  {
    // prettier-ignore
    input: [
      "struct A { b: i32 }",
      "",
      "let a = A { b: 123 }",
      "a.b",
    ].join("\n"),
    requests: [
      {
        position: {
          line: 0,
          character: 7
        },
        newName: "B"
      }
    ]
  },
  // function parameter
  {
    // prettier-ignore
    input: [
      "fun foo(x)",
      "    x",
      "end",
    ].join("\n"),
    requests: [
      // param: x
      {
        position: {
          line: 0,
          character: 8
        },
        newName: "bar"
      },
      // variable: x
      {
        position: {
          line: 1,
          character: 4
        },
        newName: "foo"
      }
    ]
  }
];

filterTestCases(cases).forEach((testCase, i) => {
  let src = readTestFileSync(testCase);
  let name = getTestName(testCase);

  testCase.requests.forEach(({ position, newName }, j) => {
    test(`${i}: prepare rename - \`${name}\` at ${position}`, async done => {
      const agent = new LanguageServerAgent(server!, { sequence: i * 100 + j });

      // Open document and no compilation errors
      const diagnostics = await agent.openDocument(name, src);
      expect(diagnostics).toHaveLength(0);

      const response = await agent.rename(name, position, newName);
      expect(response).toMatchSnapshot();

      done();
    });
  });
});
