import fs from "fs";
import { StringDecoder } from "string_decoder";
import { compileFile } from "./util/compiler";
import { BufferedPrinter } from "./util/runtime";

type Exports = Record<string, any>;

interface TestCase {
  input: string;
  expected: any;
  exec?: (exports: Exports) => any;
  captureOutput?: boolean;
}

const cases: TestCase[] = [
  // an integer
  {
    input: "42",
    expected: 42
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
    expected: 3
  },
  {
    input: "if 10 < 5\n3 end",
    expected: 0
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
  // Function
  {
    // prettier-ignore
    input: [
      "fun foo()",
      "    55",
      "end"
    ].join("\n"),
    exec: exports => exports.foo(),
    expected: 55
  },
  {
    // prettier-ignore
    input: [
      "fun square(x)",
      "    x * x",
      "end"
    ].join("\n"),
    exec: exports => exports.square(3),
    expected: 9
  },
  {
    // prettier-ignore
    input: [
      "fun fib(n)",
      "    if n <= 1",
      "        n",
      "    else",
      "        fib(n - 1) + fib(n - 2)",
      "    end",
      "end"
    ].join("\n"),
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
    input: [
      "fun foo()",
      "    \"foo\"",
      "end",
      "\"main\"",
    ].join("\n"),
    expected: "main"
  },
  {
    // prettier-ignore
    input: [
      "fun foo()",
      "    \"foo\"",
      "end",
      "\"main\"",
    ].join("\n"),
    exec: exports => exports.foo(),
    expected: "foo"
  },
  {
    // prettier-ignore
    input: [
      "println_int(1)",
    ].join("\n"),
    captureOutput: true,
    expected: "1\n"
  },
  {
    // prettier-ignore
    input: [
      "println(\"hello\")",
    ].join("\n"),
    captureOutput: true,
    expected: "hello\n"
  }
];

cases.forEach(({ input, expected, exec, captureOutput }) => {
  test(`given '${input}'`, async () => {
    const memory = new WebAssembly.Memory({ initial: 1 });
    const printer = new BufferedPrinter(memory);

    const src = "/tmp/nico_test.nico";
    fs.writeFileSync(src, input);

    const buffer = await compileFile(src);
    const module = await WebAssembly.compile(buffer);

    const instance = await WebAssembly.instantiate(module, {
      js: { mem: memory },
      printer: {
        println_i32: printer.printlnNumber.bind(printer),
        println_str: printer.printlnString.bind(printer)
      }
    });

    // @ts-ignore
    const value = exec ? exec(instance.exports) : instance.exports.main();

    if (Number.isInteger(expected)) {
      expect(value).toEqual(expected);
    } else if (captureOutput && typeof expected === "string") {
      expect(printer.buffer).toEqual(expected);
    } else if (typeof expected === "string") {
      const offset = value;
      expect(Number.isInteger(offset)).toBeTruthy();

      const viewer = new DataView(memory.buffer, 0);
      const length = viewer.getInt32(offset, true);

      const bytes = new Uint8Array(memory.buffer, offset + 4, length);
      const decoder = new StringDecoder("utf-8");
      const string = decoder.end(Buffer.from(bytes));

      expect(string).toEqual(expected);
    } else {
      fail(`This expectation value is not implemented yet! ${expected}`);
    }
  });
});
