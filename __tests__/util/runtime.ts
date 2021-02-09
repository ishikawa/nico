import { StringDecoder } from "string_decoder";

export class BufferedPrinter {
  memory: WebAssembly.Memory;
  buffer: string;

  constructor(memory: WebAssembly.Memory) {
    this.buffer = "";
    this.memory = memory;
  }

  printlnNumber(n: number): number {
    const string = n.toString();

    this.buffer += string;
    this.buffer += "\n";

    return string.length;
  }

  printlnString(offset: number): number {
    const viewer = new DataView(this.memory.buffer, 0);
    const length = viewer.getInt32(offset, true);

    const bytes = new Uint8Array(this.memory.buffer, offset + 4, length);
    const decoder = new StringDecoder("utf-8");
    const string = decoder.end(Buffer.from(bytes));

    this.buffer += string;
    this.buffer += "\n";

    return string.length;
  }
}
