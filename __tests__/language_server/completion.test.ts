import { LanguageServer, spawn_server, LanguageServerAgent, Position } from "../util/lsp";
import { filterTestCases, TestCaseBase, readTestFileSync, getTestName } from "../util/testcase";

interface TestCase extends TestCaseBase {
  requests: Array<{ position: Position }>;
}

let server: LanguageServer | undefined;

beforeAll(async () => {
  server = await spawn_server({ completion: true });
});

afterAll(() => {
  if (server) {
    return server.stop();
  }
});

let cases: TestCase[] = [
  // suggests built-in functions
  {
    input: ["p"].join("\n"),
    requests: [
      // p|
      //  ^
      {
        position: {
          line: 0,
          character: 1
        }
      }
    ]
  },
  // suggests struct or variable (case-insensitive)
  {
    // prettier-ignore
    input: [
      "struct Rectangle {",
      "  width: i32",
      "  height: i32",
      "}",
      "let rect = Rectangle { width: 30, height: 50 }",
      "",
      "rc",
    ].join("\n"),
    requests: [
      // rc|
      //   ^
      {
        position: {
          line: 6,
          character: 2
        }
      }
    ]
  }
];

filterTestCases(cases).forEach((testCase, i) => {
  let src = readTestFileSync(testCase);
  let name = getTestName(testCase);

  testCase.requests.forEach(({ position }, j) => {
    test(`${i}: completion - \`${name}\` at ${position}`, async done => {
      const agent = new LanguageServerAgent(server!, { sequence: [i, j] });

      // Allow compilation errors
      const _ = await agent.openDocument(name, src);

      const response = await agent.completion(name, position);
      expect(response).toMatchSnapshot();

      done();
    });
  });
});
