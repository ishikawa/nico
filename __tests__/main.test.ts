import fs from "fs";
import { compileFile } from "./util/compiler";

[
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
  }
].forEach(({ input, expected }) => {
  test(`given '${input}'`, async () => {
    const src = "/tmp/nico_test.nico";
    fs.writeFileSync(src, input);

    const buffer = await compileFile(src);
    const module = await WebAssembly.compile(buffer);
    const instance = await WebAssembly.instantiate(module);

    // @ts-ignore
    const value = instance.exports.main();

    expect(value).toEqual(expected);
  });
});
