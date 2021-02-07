import fs from "fs";
import { compileFile } from "./util/compiler";

type Exports = Record<string, any>;

interface TestCase {
  input: string;
  expected: any;
  exec?: (exports: Exports) => any;
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
  }
];

cases.forEach(({ input, expected, exec }) => {
  test(`given '${input}'`, async () => {
    const src = "/tmp/nico_test.nico";
    fs.writeFileSync(src, input);

    const buffer = await compileFile(src);
    const module = await WebAssembly.compile(buffer);
    const instance = await WebAssembly.instantiate(module);

    // @ts-ignore
    const value = exec ? exec(instance.exports) : instance.exports.main();

    expect(value).toEqual(expected);
  });
});
