import os from "os";
import path from "path";
import { main } from "../runner/cli";
import { compileFileToWATFile } from "./util/compiler";

test("given empty input", async () => {
  const consoleSpy = jest.spyOn(console, "log").mockImplementation(() => {});

  let code = await main([]);

  expect(code).toEqual(1);
  expect(consoleSpy.mock.calls).toHaveLength(1);
  expect(consoleSpy.mock.calls[0][0]).toMatch(/Usage:/);

  consoleSpy.mockReset();
});

interface TestCase {
  file: string;
  consoleResult: string[][];
}

const cases: TestCase[] = [
  {
    file: "./samples/fib.nico",
    consoleResult: [
      ["0"],
      ["1"],
      ["1"],
      ["2"],
      ["3"],
      ["5"],
      ["8"],
      ["13"],
      ["21"],
      ["34"],
      ["55"],
      ["89"],
      ["144"],
      ["233"],
      ["377"],
      ["610"],
      ["987"],
      ["1597"],
      ["2584"],
      ["4181"],
      ["6765"]
    ]
  },
  {
    file: "./samples/fizzbuzz.nico",
    consoleResult: [
      ["1"],
      ["2"],
      ["Fizz"],
      ["4"],
      ["Buzz"],
      ["Fizz"],
      ["7"],
      ["8"],
      ["Fizz"],
      ["Buzz"],
      ["11"],
      ["Fizz"],
      ["13"],
      ["14"],
      ["Fizz Buzz"]
    ]
  }
];

cases.forEach(({ file, consoleResult }) => {
  test(file, async () => {
    const consoleSpy = jest.spyOn(console, "log").mockImplementation(() => {});
    const outputFilepath = path.join(os.tmpdir(), path.basename(file));

    await compileFileToWATFile(file, outputFilepath);

    let code = await main(["node", "nico", outputFilepath]);

    expect(code).toEqual(0);
    expect(consoleSpy.mock.calls).toEqual(consoleResult);

    consoleSpy.mockReset();
  });
});
