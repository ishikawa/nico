import { StringDecoder } from "string_decoder";

export interface Printer {
  printlnNumber(n: number): number;
  printlnString(offset: number): number;
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

  getString(offset: number): string {
    const viewer = new DataView(this.memory.buffer, 0);
    const length = viewer.getInt32(offset, true);

    const bytes = new Uint8Array(this.memory.buffer, offset + 4, length);
    const decoder = new StringDecoder("utf-8");
    return decoder.end(Buffer.from(bytes));
  }
}
