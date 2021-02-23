import fs from "fs";
import { StringDecoder } from "string_decoder";
import { compileFile } from "./util/compiler";
import { BufferedPrinter } from "./util/runtime";

type Exports = Record<string, any>;

interface TestCase {
  input?: string;
  file?: string;
  expected: any;
  exec?: (exports: Exports) => any[];
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
    file: "input/fib_rec.nico",
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
  // FizzBuzz
  {
    file: "input/fizzbuzz.nico",
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
  }
];

cases.forEach(({ input, file, expected, exec, captureOutput }) => {
  test(`given '${input || file}'`, async () => {
    const memory = new WebAssembly.Memory({ initial: 1 });
    const printer = new BufferedPrinter(memory);

    let src = "/tmp/nico_test.nico";

    if (input) {
      fs.writeFileSync(src, input);
    } else if (file) {
      src = `${__dirname}/${file}`;
    }

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
      } else if (typeof expected === "undefined") {
        expect(value).toBeUndefined();
      } else {
        fail(`This expectation value is not implemented yet! ${expected}`);
      }
    }
  });
});
