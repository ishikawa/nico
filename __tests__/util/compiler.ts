import fs from "fs";
import { execFile } from "child_process";
import { StringDecoder } from "string_decoder";
import loadWabt from "wabt";

const DEBUG = true;

export async function compileFile(filepath: string): Promise<Uint8Array> {
  const inputWat = "/tmp/nico_test.wat";
  const wabt = await loadWabt();

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

      fs.writeFileSync(inputWat, stdout);

      const wasmModule = wabt.parseWat(inputWat, fs.readFileSync(inputWat, "utf8"));
      const { buffer } = wasmModule.toBinary({});
      resolve(buffer);
    });
  });
}
