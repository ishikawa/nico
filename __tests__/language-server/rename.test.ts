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
  },
  // let variables
  {
    // prettier-ignore
    input: [
      "let foo = 100",
      "println_i32(foo)",
    ].join("\n"),
    requests: [
      // let foo = 100
      {
        position: {
          line: 0,
          character: 4
        },
        newName: "foo"
      },
      // println_i32(foo)
      {
        position: {
          line: 1,
          character: 12
        },
        newName: "foo"
      }
    ]
  },
  // variable name
  {
    // prettier-ignore
    input: [
      "struct A { b: i32 }",
      "",
      "let a = A { b: 123 }",
      "a.b"
    ].join("\n"),
    requests: [
      // let a
      {
        position: {
          line: 2,
          character: 4
        },
        newName: "c"
      },
      // a.b
      {
        position: {
          line: 3,
          character: 0
        },
        newName: "foo"
      }
    ]
  },
  // array pattern
  {
    // prettier-ignore
    input: [
      "let x = [1, 2, 3]",

      "case x",
      "when [x, y, z]",
      "    x + y + z",
      "else",
      "    100",
      "end",
    ].join("\n"),
    requests: [
      // when [x, y, z]
      //       ^
      {
        position: {
          line: 3,
          character: 6
        },
        newName: "a"
      },
      // when [a, y, z]
      //          ^
      {
        position: {
          line: 3,
          character: 9
        },
        newName: "b"
      },
      // when [a, b, z]
      //             ^
      {
        position: {
          line: 3,
          character: 12
        },
        newName: "c"
      },
      //     a + b + c
      //     ^
      {
        position: {
          line: 4,
          character: 4
        },
        newName: "x"
      },
      //     a + b + c
      //         ^
      {
        position: {
          line: 4,
          character: 8
        },
        newName: "y"
      },
      //     a + b + c
      //             ^
      {
        position: {
          line: 4,
          character: 13
        },
        newName: "z"
      }
    ]
  },
  // struct field
  {
    // prettier-ignore
    input: [
      "struct A { b: i32 }",
      "",
      "let a = A { b: 123 }",
      "a.b"
    ].join("\n"),
    requests: [
      // struct A { b: i32 }
      //            ^
      {
        position: {
          line: 0,
          character: 11
        },
        newName: "c"
      },
      // let a = A { b: 123 }
      //             ^
      {
        position: {
          line: 2,
          character: 12
        },
        newName: "c"
      },
      // a.b
      //   ^
      {
        position: {
          line: 3,
          character: 2
        },
        newName: "c"
      }
    ]
  }
];

filterTestCases(cases).forEach((testCase, i) => {
  let src = readTestFileSync(testCase);
  let name = getTestName(testCase);

  testCase.requests.forEach(({ position, newName }, j) => {
    test(`${i}: rename - \`${name}\` at ${position}`, async done => {
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
