import os from "os";
import path from "path";
import fs from "fs";
import { execFile } from "child_process";
import { StringDecoder } from "string_decoder";
import loadWabt from "wabt";

const DEBUG = false;

export type CompileFileOptions = {
  backend?: "2021-spring" | "2021-summer";
};

export async function compileFileToWATFile(
  filepath: string,
  outputFilepath: string,
  options: CompileFileOptions = {}
): Promise<void> {
  const args = [filepath];

  if (options.backend) {
    args.unshift("--backend", options.backend);
  }

  return new Promise((resolve, reject) => {
    execFile("./target/debug/nico", [filepath], (error, stdout, stderr) => {
      if (error) {
        reject(error);
        return;
      }

      if (DEBUG) {
        const srcBuffer = fs.readFileSync(filepath);
        const decoder = new StringDecoder("utf-8");
        const src = decoder.end(srcBuffer);

        console.log(src);
        console.log(stdout);

        if (stderr) {
          console.warn(stderr);
        }
      }

      fs.writeFileSync(outputFilepath, stdout);

      // In DEBUG mode, wait some time for console flush.
      setTimeout(() => resolve(), DEBUG ? 100 : 0);
    });
  });
}

export async function compileFile(filepath: string): Promise<Uint8Array> {
  const inputWat = path.join(os.tmpdir(), "nico_test.wat");
  const wabt = await loadWabt();

  await compileFileToWATFile(filepath, inputWat);

  const wasmModule = wabt.parseWat(inputWat, fs.readFileSync(inputWat, "utf8"));
  const { buffer } = wasmModule.toBinary({});

  return buffer;
}
