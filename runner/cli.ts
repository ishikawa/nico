import fs from "fs";
import loadWabt from "wabt";
import { ConsolePrinter } from "./runtime";

function printUsage() {
  const usage = `
  Usage: npx ts-node cli program.wat
  `.trim();
  console.log(usage);
}

async function parseWat(filepath: string): Promise<Uint8Array> {
  const wabt = await loadWabt();

  return new Promise((resolve, _reject) => {
    const wasmModule = wabt.parseWat(filepath, fs.readFileSync(filepath, "utf8"));
    const { buffer } = wasmModule.toBinary({});
    resolve(buffer);
  });
}

export async function main(argv: string[]): Promise<number> {
  if (argv.length < 3) {
    printUsage();
    return 1;
  }

  const filepath = argv[2];
  const wasm = await parseWat(filepath);
  const module = await WebAssembly.compile(wasm);

  const memory = new WebAssembly.Memory({ initial: 1 });
  const printer = new ConsolePrinter(memory);

  const instance = await WebAssembly.instantiate(module, {
    js: { mem: memory },
    printer: {
      println_i32: printer.printlnNumber.bind(printer),
      println_str: printer.printlnString.bind(printer)
    }
  });

  const entryPoint = instance.exports.main;

  if (typeof entryPoint == "function") {
    entryPoint();
  }

  return 0;
}
