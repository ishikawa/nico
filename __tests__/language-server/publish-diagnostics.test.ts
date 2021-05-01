import { LanguageServer, NotificationMessage, RequestBuilder, spawn_server } from "../util/lsp";
import fs from "fs";
import { filterTestCases, TestCaseBase } from "../util/testcase";

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
  test(`${i}: publishDiagnostics at \`${name}\``, async done => {
    const builder = new RequestBuilder({ id: 1000 + 1 });
    const uri = `file:///home/user/nico/sample${i}.nico`;

    const nextNotification = server!.nextMessage<NotificationMessage>();
    await server!.sendNotification(builder.textDocumentDidOpen(uri, src));

    const diagnostics = await nextNotification;
    expect(diagnostics).toMatchSnapshot();

    done();
  });
});
