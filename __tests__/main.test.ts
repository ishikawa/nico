import fs from "fs";
import { execFile } from "child_process";
import loadWabt from "wabt";

async function compileFile(filepath: string): Promise<Uint8Array> {
  const inputWat = "/tmp/nico_test.wat";
  const wabt = await loadWabt();

  return new Promise((resolve, reject) => {
    execFile("./target/debug/nico", [filepath], (error, stdout) => {
      if (error) {
        reject(error);
        return;
      }

      fs.writeFileSync(inputWat, stdout);

      const wasmModule = wabt.parseWat(inputWat, fs.readFileSync(inputWat, "utf8"));
      const { buffer } = wasmModule.toBinary({});
      resolve(buffer);
    });
  });
}

[
  // an integer
  {
    input: "42",
    expected: 42
  },
  {
    input: "102030",
    expected: 102030
  }
].forEach(({ input, expected }) => {
  test(`given '${input}'`, async () => {
    const wabt = await loadWabt();
    const src = "/tmp/nico_test.nico";
    const inputWat = "/tmp/nico_test.wat";

    fs.writeFileSync(src, input);

    const buffer = await compileFile(src);
    const module = await WebAssembly.compile(buffer);
    const instance = await WebAssembly.instantiate(module);

    // @ts-ignore
    const value = instance.exports.main();

    expect(value).toEqual(expected);
  });
});
