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
