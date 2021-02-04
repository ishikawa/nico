import fs from "fs";
import { execFile } from "child_process";
import loadWabt from "wabt";

export async function compileFile(filepath: string): Promise<Uint8Array> {
  const inputWat = "/tmp/nico_test.wat";
  const wabt = await loadWabt();

  return new Promise((resolve, reject) => {
    execFile("./target/debug/nico", [filepath], (error, stdout) => {
      if (error) {
        reject(error);
        return;
      }

      //console.log(stdout);
      fs.writeFileSync(inputWat, stdout);

      const wasmModule = wabt.parseWat(inputWat, fs.readFileSync(inputWat, "utf8"));
      const { buffer } = wasmModule.toBinary({});
      resolve(buffer);
    });
  });
}
