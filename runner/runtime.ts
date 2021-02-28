import { StringDecoder } from "string_decoder";

export interface Printer {
  printlnNumber(n: number): number;
  printlnString(offset: number): number;
}

/**
 * Required `import` objects to run Nico compilation module.
 */
export interface WasmImportObject extends Record<string, Record<string, WebAssembly.ImportValue>> {
  "nico.runtime": { mem: WebAssembly.Memory };
  printer: {
    println_i32: Printer["printlnNumber"];
    println_str: Printer["printlnString"];
  };
}

export function buildImportObject(props: { memory: WebAssembly.Memory; printer: Printer }): WasmImportObject {
  const { memory, printer } = props;

  return {
    "nico.runtime": { mem: memory },
    printer: {
      println_i32: printer.printlnNumber.bind(printer),
      println_str: printer.printlnString.bind(printer)
    }
  };
}

export class ConsolePrinter implements Printer {
  stringView: StringView;

  constructor(memory: WebAssembly.Memory) {
    this.stringView = new StringView(memory);
  }

  printlnNumber(n: number): number {
    const string = n.toString();
    console.log(string);
    return string.length;
  }

  printlnString(offset: number): number {
    const string = this.stringView.getString(offset);
    console.log(string);
    return string.length;
  }
}

export class BufferedPrinter {
  stringView: StringView;
  buffer: string;

  constructor(memory: WebAssembly.Memory) {
    this.buffer = "";
    this.stringView = new StringView(memory);
  }

  printlnNumber(n: number): number {
    const string = n.toString();

    this.buffer += string;
    this.buffer += "\n";

    return string.length;
  }

  printlnString(offset: number): number {
    const string = this.stringView.getString(offset);

    this.buffer += string;
    this.buffer += "\n";

    return string.length;
  }
}

export class StringView {
  memory: WebAssembly.Memory;

  constructor(memory: WebAssembly.Memory) {
    this.memory = memory;
  }

  getString(base: number): string {
    const viewer = new DataView(this.memory.buffer, 0);
    const offset = viewer.getInt32(base, true);
    const length = viewer.getInt32(base + 4, true);

    const bytes = new Uint8Array(this.memory.buffer, offset, length);
    const decoder = new StringDecoder("utf-8");
    return decoder.end(Buffer.from(bytes));
  }
}
