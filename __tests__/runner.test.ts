import os from "os";
import fs from "fs";
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

test("fizzbuzz", async () => {
  const consoleSpy = jest.spyOn(console, "log").mockImplementation(() => {});
  const outputFilepath = path.join(os.tmpdir(), "fizzbuzz.wat");

  await compileFileToWATFile("./samples/fizzbuzz.nico", outputFilepath);

  let code = await main(["node", "nico", outputFilepath]);

  expect(code).toEqual(0);
  expect(consoleSpy.mock.calls).toEqual([
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
  ]);

  consoleSpy.mockReset();
});
