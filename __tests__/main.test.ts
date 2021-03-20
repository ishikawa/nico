import fs from "fs";
import os from "os";
import path from "path";
import { StringDecoder } from "string_decoder";
import { compileFile } from "./util/compiler";
import { BufferedPrinter, buildImportObject, ConsolePrinter, StringView } from "../runner/runtime";

type Exports = Record<string, any>;

interface TestCase {
  input?: string;
  file?: string;
  expected?: any;
  exec?: (exports: Exports) => any[];
  captureOutput?: boolean;
  compileError?: RegExp;

  // filters
  // - **focus** - Include these tests only.
  // - **skip** - Exclude these tests.
  // - **todo** - Under development. It's ok if the compiler halted with "not yet implemented"
  focus?: boolean;
  skip?: boolean;
  todo?: boolean;
}

const temporaryCodePath = path.join(os.tmpdir(), "nico_test_main.nico");

const cases: TestCase[] = [
  // an integer
  {
    input: "42",
    expected: 42
  },
  {
    input: "-34",
    expected: -34
  },
  {
    input: "let x = 100\n-+-(20+-5)+x",
    expected: 115
  },
  {
    input: "102030",
    expected: 102030
  },
  // add
  {
    input: "1 + 2",
    expected: 3
  },
  // sub
  {
    input: "103 - 5",
    expected: 98
  },
  // mul
  {
    input: "3 * 11",
    expected: 33
  },
  // div
  {
    input: "50 / 2",
    expected: 25
  },
  // rem
  {
    input: "10 % 3",
    expected: 1
  },
  // grouping and priority
  {
    input: "1 + 2 * 3",
    expected: 7
  },
  {
    input: "1 + 2 * 3 + 4",
    expected: 11
  },
  {
    input: "100 + 8 / 4",
    expected: 102
  },
  {
    input: "(1 + 2) * 3",
    expected: 9
  },
  {
    input: "(((1) + (20 -(1 *3))) * 3)",
    expected: 54
  },
  // comparisons
  {
    input: "3 < 5",
    expected: 1
  },
  {
    input: "3 > 5",
    expected: 0
  },
  {
    input: "30 >= 5",
    expected: 1
  },
  {
    input: "30 <= 5",
    expected: 0
  },
  {
    input: "5 == 5",
    expected: 1
  },
  {
    input: "5 != 5",
    expected: 0
  },
  // If
  {
    input: "if 10 > 5\n3 end",
    expected: undefined
  },
  {
    input: "if 10 < 5\n3 end",
    expected: undefined
  },
  {
    // prettier-ignore
    input: [
      "if 10 <= 5",
      "    3",
      "else",
      "    40",
      "end"
    ].join("\n"),
    expected: 40
  },

  // Case
  {
    file: "input/case_0.nico",
    exec: exports => [exports.foo(4), exports.foo(5), exports.foo(6)],
    expected: [4, 10, 20]
  },
  {
    // prettier-ignore
    input: [
      "export fun foo(n)",
      "    case n + 1",
      "    when x if x > 0",
      "        x",
      "    else",
      "        n",
      "    end",
      "end"
    ].join("\n"),
    exec: exports => exports.foo(100),
    expected: 101
  },
  {
    // prettier-ignore
    input: [
      "case 1",
      "when x",
      "    x",
      "when n",
      "    n",
      "end",
    ].join("\n"),
    compileError: /unreachable pattern/i
  },
  {
    // prettier-ignore
    input: [
      "case 1",
      "when x",
      "    x",
      "else",
      "    2",
      "end",
    ].join("\n"),
    compileError: /unreachable `else` clause/i
  },
  {
    // prettier-ignore
    input: [
      "export fun foo(n)",
      "    case n",
      "    when 1",
      "        10",
      "    when 2",
      "        20",
      "    when x",
      "        x",
      "    end",
      "end"
    ].join("\n"),
    exec: exports => [exports.foo(1), exports.foo(2), exports.foo(3)],
    expected: [10, 20, 3]
  },
  {
    // prettier-ignore
    input: [
      "export fun foo(n)",
      "    case n",
      "    when 1",
      "        10",
      "    when 2",
      "        20",
      "    end",
      "end"
    ].join("\n"),
    compileError: /Missing match arm. non-exhaustive patterns/i
  },
  {
    // prettier-ignore
    input: [
      "case 10",
      "when [a]",
      "    a",
      "else",
      "    3",
      "end",
    ].join("\n"),
    compileError: /mismatched type: expected T\[\], found i32/i
  },
  {
    // prettier-ignore
    input: [
      "",
      "let [x] = [100]",
      "x",
    ].join("\n"),
    compileError: /refutable pattern in local binding/i
  },
  {
    // prettier-ignore
    input: [
      "",
      "case [1, 2, 3]",
      "when [a, b, c]",
      "    a + b + c",
      "else",
      "    123",
      "end",
    ].join("\n"),
    expected: 6
  },
  {
    // prettier-ignore
    input: [
      "export fun foo(a)",
      "    case a",
      "    when []",
      "        10",
      "    when [1]",
      "        20",
      "    when [x]",
      "        x",
      "    when x",
      "        x[1]",
      "    end",
      "end",
      "println_i32(foo([]))",
      "println_i32(foo([1]))",
      "println_i32(foo([2]))",
      "println_i32(foo([3, 4]))",
    ].join("\n"),
    captureOutput: true,
    expected: ["10", "20", "2", "4"].join("\n") + "\n"
  },
  // Nested array pattern
  {
    // prettier-ignore
    input: [
      "case [[1, 2], [3, 4, 5]]",
      "when [[a, b], [c, d, e]]",
      "    a + b + c + d + e",
      "when [a, b]",
      "    10",
      "else",
      "    20",
      "end"
    ].join("\n"),
    expected: 15
  },
  {
    // prettier-ignore
    input: [
      "export fun foo(a)",
      "    case a",
      "    when []",
      "        10",
      "    when [1]",
      "        20",
      "    when [x]",
      "        x",
      "    end",
      "end"
    ].join("\n"),
    compileError: /Missing match arm. non-exhaustive patterns/i
  },
  // Function
  {
    file: "input/fun_55.nico",
    exec: exports => exports.foo(),
    expected: 55
  },
  {
    file: "input/fun_square.nico",
    exec: exports => exports.square(3),
    expected: 9
  },
  {
    file: "../samples/fib.nico",
    exec: exports => exports.fib(9),
    expected: 34
  },
  // string literal
  {
    input: '"Hello, World!\\n"',
    expected: "Hello, World!\n"
  },
  {
    // prettier-ignore
    input: "\"main\"",
    expected: "main"
  },
  {
    file: "input/fun_string.nico",
    exec: exports => exports.foo(),
    expected: "foo"
  },
  // Passing various parameters
  {
    file: "input/fun_if.nico",
    expected: 10
  },
  // Println
  {
    input: "println_i32(1)",
    captureOutput: true,
    expected: "1\n"
  },
  {
    input: 'println_str("hello")',
    captureOutput: true,
    expected: "hello\n"
  },
  // Multiple expressions
  {
    file: "input/more_than_one_expr.nico",
    captureOutput: true,
    expected: "Hello\n,\n \nWorld!\n\n"
  },
  // Multiple functions
  {
    file: "input/more_than_one_fun.nico",
    expected: 16
  },
  // Sample - FizzBuzz
  {
    file: "../samples/fizzbuzz.nico",
    exec: exports => exports.fizzbuzz(15),
    captureOutput: true,
    expected: [
      "1",
      "2",
      "Fizz",
      "4",
      "Buzz",
      "Fizz",
      "7",
      "8",
      "Fizz",
      "Buzz",
      "11",
      "Fizz",
      "13",
      "14",
      "Fizz Buzz",
      ""
    ].join("\n")
  },
  // Sample - Max
  {
    file: "../samples/max.nico",
    captureOutput: true,
    expected: ["-1", "48", "76", "76", "99", "98", ""].join("\n")
  },
  // Variable declaration
  {
    file: "input/let_0.nico",
    expected: 6580
  },
  {
    file: "input/let_scoping.nico",
    captureOutput: true,
    expected: ["15", "10", ""].join("\n")
  },
  // Array
  {
    input: "[1][0]",
    expected: 1
  },
  {
    input: "[[3]][0][0]",
    expected: 3
  },
  {
    input: ["let x = [5]", "x[0]"].join("\n"),
    expected: 5
  },
  {
    // prettier-ignore
    input: [
      "fun foo(x)",
      "    x * 5",
      "end",
      "[foo(11)][0]",
    ].join("\n"),
    expected: 55
  },
  {
    // prettier-ignore
    input: [
      "fun get(ar, i)",
      "    ar[i]",
      "end",
      "get([5, 4, 3], 1)",
    ].join("\n"),
    expected: 4
  },
  {
    // prettier-ignore
    input: [
      "fun foo(x)",
      "    x * 5",
      "end",
      "fun bar()",
      "    1",
      "end",
      "[foo(1), foo(2)][bar()]",
    ].join("\n"),
    expected: 10
  },
  {
    // prettier-ignore
    input: [
      "fun foo(x)",
      "    x * 5",
      "end",
      "fun bar()",
      "    1",
      "end",
      "let x = [1, 21 + 33, foo(10)]",
      "x[(2 - 2)] + x[bar()] + x[2]"
    ].join("\n"),
    expected: 105
  },
  // array - the length of array a to be calculated as a[1].
  {
    // prettier-ignore
    input: [
      "let a = [1, 0, 3]",
      "let b = [4, 0, 6]",
      "a[2] + b[2]",
    ].join("\n"),
    expected: 9
  },
  // empty array pattern
  {
    // prettier-ignore
    input: [
      "let x = []",
      "case x",
      "when []",
      "    111",
      "else",
      "    222",
      "end"].join("\n"),
    expected: 111
  },
  {
    input: "let ...x = []",
    compileError: /Syntax error: Rest pattern must be in `\[\.\.\.\]`/
  },
  {
    input: "let [...x, y] = []",
    compileError: /Syntax error: Rest element \(#0\) must be last element/
  },
  {
    input: "let [...x] = 1",
    compileError: /mismatched type: expected T\[\], found i32/
  },
  {
    // prettier-ignore
    input: [
      "let [...x] = []",
      "case x",
      "when [_, 1]",
      "    222",
      "when []",
      "    111",
      "else",
      "    333",
      "end"].join("\n"),
    expected: 111
  },
  {
    input: "let [head, ...tail] = []",
    compileError: /refutable pattern/
  },
  {
    // prettier-ignore
    input: [
      "case [45, 66, 56]",
      "when [x, ...y]",
      "    x + y[0]",
      "end"].join("\n"),
    compileError: /non-exhaustive patterns/
  },
  {
    // prettier-ignore
    input: [
      "case [45, 66, 56]",
      "when []",
      "    10",
      "when [x, y, ..._]",
      "    x + y",
      "end"].join("\n"),
    compileError: /non-exhaustive patterns/
  },
  {
    // prettier-ignore
    input: [
      "case [45, 67, 56]",
      "when [x, ...rest]",
      "    x + rest[0]",
      "else",
      "    222",
      "end"].join("\n"),
    expected: 112
  },
  {
    // prettier-ignore
    input: [
      "case [45, 66, 56]",
      "when [...rest]",
      "    rest[0]",
      "end"].join("\n"),
    expected: 45
  },
  {
    // prettier-ignore
    input: [
      "case [45, 66, 56]",
      "when []",
      "    10",
      "when [x, ...rest]",
      "    x + rest[0]",
      "end"].join("\n"),
    expected: 111
  },
  {
    // prettier-ignore
    input: [
      "case [45, 66, 56]",
      "when []",
      "    10",
      "when [x]",
      "    20",
      "when [x, y, ...]",
      "    x + y",
      "end"].join("\n"),
    expected: 111
  },
  {
    // prettier-ignore
    input: [
      "case [[45, 66, 56], [34, 21, 10]]",
      "when []",
      "    10",
      "when [x]",
      "    20",
      "when [[a, ...b], [c, ...d]]",
      "    a + b[0] + c + d[1]",
      "else",
      "    30",
      "end"].join("\n"),
    expected: 155
  },
  // newline seen
  {
    // prettier-ignore
    input: [
      "case 5",
      "when 5",
      "    -10",
      "else",
      "    10",
      "end"].join("\n"),
    expected: -10
  },
  {
    // prettier-ignore
    input: [
      "case 5",
      "when x if x == 5",
      "    -10",
      "else",
      "    10",
      "end"].join("\n"),
    expected: -10
  },
  {
    // prettier-ignore
    input: [
      "let not_a_function = 476",
      "not_a_function",
      "(-945)"].join("\n"),
    expected: -945
  },
  {
    // prettier-ignore
    input: [
      "let not_an_array = 476",
      "not_an_array",
      "[854][0]"].join("\n"),
    expected: 854
  },
  // Structs
  {
    todo: true,
    // prettier-ignore
    input: [
      "struct Rectangle {",
      "    width: i32,",
      "    height: i32",
      "}",
      "let height = 40",
      "let rect = Rectangle {",
      "    width: 50,",
      "    height,",
      "}",
      "rect.width + rect.height"
    ].join("\n"),
    expected: 90
  },
  {
    todo: true,
    // prettier-ignore
    input: [
      "struct Rectangle {",
      "    width: i32,",
      "    height: i32",
      "}",
      "fun foo(rect)",
      "    rect.width + rect.height",
      "end",
      "let rect = Rectangle {",
      "    width: 50,",
      "    height: 60",
      "}",
      "foo(rect)"
    ].join("\n"),
    expected: 110
  },
  {
    todo: true,
    // prettier-ignore
    input: [
      "struct Rectangle {",
      "    width: i32,",
      "    height: i32",
      "}",
      "fun bar(rect)",
      "    rect.width + rect.height",
      "end",
      "fun foo()",
      "    bar(Rectangle {",
      "        width: 50,",
      "        height: 60",
      "    })",
      "end",
      "foo()"
    ].join("\n"),
    expected: 110
  },
  {
    todo: true,
    // prettier-ignore
    input: [
      "struct Point {",
      "    x: i32,",
      "    y: i32",
      "}",
      "let p = Point { x: 3, y: 7 }",
      "let Point { x: a, y: b } = p",
      "a + b",
    ].join("\n"),
    expected: 21
  }
];

// filter
let focused = cases.filter(x => x.focus);
focused = focused.length === 0 ? cases : focused;
focused = focused.filter(x => !x.skip);

focused.forEach(({ input, file, expected, compileError, exec, captureOutput, todo }) => {
  test(`given '${input || file}'`, async () => {
    let src = temporaryCodePath;

    if (input) {
      fs.writeFileSync(src, input);
    } else if (file) {
      src = `${__dirname}/${file}`;
    }

    const memory = new WebAssembly.Memory({ initial: 1 });
    const printer = captureOutput ? new BufferedPrinter(memory) : new ConsolePrinter(memory);
    const imports = buildImportObject({ memory, printer });

    let buffer;

    try {
      buffer = await compileFile(src);
    } catch (e) {
      if (compileError) {
        expect(e.toString()).toMatch(compileError);
        return;
      }
      // Allow "not yet implemented"?
      else if (todo) {
        expect(e.toString()).toMatch(/panicked at 'not yet implemented'/);
        return;
      } else {
        throw e;
      }
    }
    if (compileError) {
      throw "compile error expected";
    }

    const module = await WebAssembly.compile(buffer);

    const instance = await WebAssembly.instantiate(module, imports);

    if (!exec && !instance.exports.main) {
      // no executable. mark succeeded.
      expect(instance).toBeDefined();
      return;
    }

    // @ts-ignore
    let values = exec ? exec(instance.exports) : instance.exports.main();
    let expected_values = expected;

    if (Array.isArray(values)) {
      expect(Array.isArray(expected_values)).toBeTruthy();
    } else {
      values = [values];
      expected_values = [expected];
    }

    for (let i = 0; i < values.length; i++) {
      let value = values[i];
      let expected = expected_values[i];

      if (Number.isInteger(expected)) {
        expect(value).toEqual(expected);
      } else if (captureOutput && typeof expected === "string") {
        if (printer instanceof BufferedPrinter) {
          expect(printer.buffer).toEqual(expected);
        }
      } else if (typeof expected === "string") {
        const offset = value;
        expect(Number.isInteger(offset)).toBeTruthy();

        const viewer = new StringView(memory);
        const string = viewer.getString(offset);

        expect(string).toEqual(expected);
      } else if (typeof expected === "undefined") {
        expect(value).toBeUndefined();
      } else {
        fail(`This expectation value is not implemented yet! ${expected}`);
      }
    }
  });
});
