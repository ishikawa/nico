import { LanguageServer, spawn_server, LanguageServerAgent, Position } from "../util/lsp";
import { filterTestCases, TestCaseBase, readTestFileSync, getTestName } from "../util/testcase";

interface TestCase extends TestCaseBase {
  requests: Array<{ position: Position }>;
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
  // struct field
  {
    // prettier-ignore
    input: [
      "struct A { a: i32 }",
      "let a = A { a: 100 }",
      "a.a"
    ].join("\n"),
    requests: [
      // struct A { a: i32 }
      //                ^
      {
        position: {
          line: 0,
          character: 15
        }
      },
      // let a = A { a: 100 }
      //             ^
      {
        position: {
          line: 1,
          character: 12
        }
      }
    ]
  }
];

filterTestCases(cases).forEach((testCase, i) => {
  let src = readTestFileSync(testCase);
  let name = getTestName(testCase);

  testCase.requests.forEach(({ position }, j) => {
    test(`${i}: hover - \`${name}\` at ${position}`, async done => {
      const agent = new LanguageServerAgent(server!, { sequence: (i + 1) * 100 + j });

      // Open document and no compilation errors
      const diagnostics = await agent.openDocument(name, src);
      expect(diagnostics).toHaveLength(0);

      const response = await agent.hover(name, position);
      expect(response).toMatchSnapshot();

      done();
    });
  });
});
