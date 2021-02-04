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
  // addi
  {
    input: "1 + 2",
    expected: 3
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
