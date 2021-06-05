import { spawn, ChildProcessWithoutNullStreams } from "child_process";
import { EventEmitter } from "events";

const DEBUG = true;

// https://microsoft.github.io/language-server-protocol/specifications/specification-current/#baseProtocol
export interface Message {
  jsonrpc: string;
}

export interface RequestMessage extends Message {
  /**
   * The request id.
   */
  id: number | string;

  /**
   * The method to be invoked.
   */
  method: string;

  /**
   * The method's params.
   */
  params?: any;
}

export interface ResponseMessage extends Message {
  /**
   * The request id.
   */
  id: number | string | null;

  /**
   * The result of a request. This member is REQUIRED on success.
   * This member MUST NOT exist if there was an error invoking the method.
   */
  result?: any;

  /**
   * The error object in case a request fails.
   */
  error?: ResponseError;
}

interface ResponseError {
  /**
   * A number indicating the error type that occurred.
   */
  code: number;

  /**
   * A string providing a short description of the error.
   */
  message: string;

  /**
   * A primitive or structured value that contains additional
   * information about the error. Can be omitted.
   */
  data?: any;
}

export namespace ErrorCodes {
  // Defined by JSON RPC
  export const ParseError = -32700;
  export const InvalidRequest = -32600;
  export const MethodNotFound = -32601;
  export const InvalidParams = -32602;
  export const InternalError = -32603;

  /**
   * This is the start range of JSON RPC reserved error codes.
   * It doesn't denote a real error code. No LSP error codes should
   * be defined between the start and end range. For backwards
   * compatibility the `ServerNotInitialized` and the `UnknownErrorCode`
   * are left in the range.
   *
   * @since 3.16.0
   */
  export const jsonrpcReservedErrorRangeStart = -32099;
  /** @deprecated use jsonrpcReservedErrorRangeStart */
  export const serverErrorStart = jsonrpcReservedErrorRangeStart;

  /**
   * Error code indicating that a server received a notification or
   * request before the server has received the `initialize` request.
   */
  export const ServerNotInitialized = -32002;
  export const UnknownErrorCode = -32001;

  /**
   * This is the start range of JSON RPC reserved error codes.
   * It doesn't denote a real error code.
   *
   * @since 3.16.0
   */
  export const jsonrpcReservedErrorRangeEnd = -32000;
  /** @deprecated use jsonrpcReservedErrorRangeEnd */
  export const serverErrorEnd = jsonrpcReservedErrorRangeEnd;

  /**
   * This is the start range of LSP reserved error codes.
   * It doesn't denote a real error code.
   *
   * @since 3.16.0
   */
  export const lspReservedErrorRangeStart = -32899;

  export const ContentModified = -32801;
  export const RequestCancelled = -32800;

  /**
   * This is the end range of LSP reserved error codes.
   * It doesn't denote a real error code.
   *
   * @since 3.16.0
   */
  export const lspReservedErrorRangeEnd = -32800;
}

export interface NotificationMessage extends Message {
  /**
   * The method to be invoked.
   */
  method: string;

  /**
   * The notification's params.
   */
  params?: Record<string, any>;
}

// LSP
export type Position = {
  line: number;
  character: number;
};

// server
type InitializeOptions = {
  completion?: boolean | Record<string, any>;
  hover?: boolean | Record<string, any>;
  signatureHelp?: boolean | Record<string, any>;
  rename?: boolean | Record<string, any>;
};

export class LanguageServer extends EventEmitter {
  process: ChildProcessWithoutNullStreams;

  payload: string;

  static spawn(): LanguageServer {
    const process = spawn("./target/debug/nico-ls", [], {
      env: {
        RUST_LOG: "info",
        RUST_BACKTRACE: "full"
      }
    });

    return new LanguageServer(process);
  }

  constructor(process: ChildProcessWithoutNullStreams) {
    super();

    this.process = process;
    this.process.stdout.on("data", this.onReceive.bind(this));

    if (DEBUG) {
      this.process.stderr.on("data", data => {
        console.warn(`stderr: ${data}`);
      });
    }

    this.process.on("close", code => this.emit("close", code));
    this.process.on("exit", code => this.emit("exit", code));

    this.payload = "";
  }

  onReceive(data: Buffer | string) {
    // For simplicity, we assume whole payload arrived at once.
    const payload = data instanceof Buffer ? data.toString("utf-8") : data;

    this.payload += payload;

    // Splits payload into header and contents.
    // If the received contents is valid JSON-RPC message, the number of
    // elements is greater than 3 and the last element is not empty.
    //
    // Currently, we assume the structure of payload is as follow:
    //
    //     Content-Length: xxx\r\n
    //     \r\n
    //     ...
    //
    const lines = this.payload.split("\r\n", 4);

    if (lines.length < 3) {
      // not completed
      return;
    }

    if (lines.length !== 3) {
      throw new Error(`invalid JSON-RPC message: ${payload}`);
    }

    const header = lines[0].trimEnd().split(/:\s*/);

    if (header[0] !== "Content-Length") {
      throw new Error(`invalid header, expected "Content-Length" but was ${header}`);
    }

    const content = lines[2];

    if (content.length > 0) {
      const message = JSON.parse(content);

      this.payload = "";
      this.emit("message", message);
    }
  }

  nextMessage<T extends Message>(): Promise<T> {
    return new Promise(resolve => {
      this.once("message", resolve);
    });
  }

  sendRequest(message: RequestMessage): Promise<ResponseMessage> {
    const promise = this.nextMessage<ResponseMessage>();
    const payload = JSON.stringify(message);

    this.process.stdin.write(`Content-Length: ${payload.length}\r\n`);
    this.process.stdin.write("\r\n");
    this.process.stdin.write(payload);

    return promise;
  }

  sendNotification(notification: NotificationMessage): Promise<void> {
    const payload = JSON.stringify(notification);

    this.process.stdin.write(`Content-Length: ${payload.length}\r\n`);
    this.process.stdin.write("\r\n");
    this.process.stdin.write(payload);

    return Promise.resolve();
  }

  isStopped(): boolean {
    return this.process.killed;
  }

  stop(): Promise<void> {
    return new Promise(resolve => {
      // Delay sending the signal so that we can see the output of the `console.log()` while testing.
      setTimeout(() => {
        this.process.kill();
        resolve();
      }, 100);
    });
  }
}

// Requests and notifications
export function buildRequest(method: string, params: any): RequestMessage {
  return {
    jsonrpc: "2.0",
    id: Math.floor(Math.random() * 10000),
    method,
    params
  };
}

export function buildNotification(method: string, params: any): NotificationMessage {
  return {
    jsonrpc: "2.0",
    method,
    params
  };
}

export class RequestBuilder {
  id: number;

  constructor({ id }: { id: number }) {
    this.id = id;
  }

  buildRequest(method: string, params: any): RequestMessage {
    return {
      jsonrpc: "2.0",
      id: this.id++,
      method,
      params
    };
  }

  buildNotification(method: string, params: any): NotificationMessage {
    return {
      jsonrpc: "2.0",
      method,
      params
    };
  }

  initialize({ completion, rename, hover, signatureHelp }: InitializeOptions = {}): RequestMessage {
    const expand = (
      name: string,
      param: boolean | undefined | null | Record<string, any>,
      defaultValue: Record<string, any>
    ): Record<string, any> => {
      if (!param) {
        return {};
      } else if (param === true) {
        return { [name]: defaultValue };
      } else {
        return { [name]: param };
      }
    };

    const params = {
      trace: "verbose",
      capabilities: {
        textDocument: {
          ...expand("completion", completion, {
            dynamicRegistration: true,
            contextSupport: true,
            completionItem: {
              snippetSupport: true,
              commitCharactersSupport: true,
              documentationFormat: ["markdown", "plaintext"],
              deprecatedSupport: true,
              preselectSupport: true,
              tagSupport: {
                valueSet: [1]
              },
              insertReplaceSupport: true,
              resolveSupport: {
                properties: ["documentation", "detail", "additionalTextEdits"]
              },
              insertTextModeSupport: {
                valueSet: [1, 2]
              }
            },
            completionItemKind: {
              valueSet: [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
            }
          }),
          ...expand("rename", rename, {
            dynamicRegistration: true,
            prepareSupport: true,
            prepareSupportDefaultBehavior: 1,
            honorsChangeAnnotations: true
          }),
          ...expand("hover", hover, {
            dynamicRegistration: true,
            contentFormat: ["markdown", "plaintext"]
          }),
          ...expand("signatureHelp", signatureHelp, {
            dynamicRegistration: true,
            signatureInformation: {
              documentationFormat: ["markdown", "plaintext"],
              parameterInformation: {
                labelOffsetSupport: true
              },
              activeParameterSupport: true
            },
            contextSupport: true
          }),
          publishDiagnostics: {
            relatedInformation: true,
            versionSupport: false,
            tagSupport: {
              valueSet: [1, 2]
            },
            codeDescriptionSupport: true,
            dataSupport: true
          },
          semanticTokens: {
            dynamicRegistration: true,
            tokenTypes: [
              "namespace",
              "type",
              "class",
              "enum",
              "interface",
              "struct",
              "typeParameter",
              "parameter",
              "variable",
              "property",
              "enumMember",
              "event",
              "function",
              "method",
              "macro",
              "keyword",
              "modifier",
              "comment",
              "string",
              "number",
              "regexp",
              "operator"
            ],
            tokenModifiers: [
              "declaration",
              "definition",
              "readonly",
              "static",
              "deprecated",
              "abstract",
              "async",
              "modification",
              "documentation",
              "defaultLibrary"
            ],
            formats: ["relative"],
            requests: {
              range: true,
              full: {
                delta: true
              }
            },
            multilineTokenSupport: false,
            overlappingTokenSupport: false
          },
          linkedEditingRange: {
            dynamicRegistration: true
          }
        }
      }
    };

    return this.buildRequest("initialize", params);
  }

  textDocumentSemanticTokenFull(uri: string): RequestMessage {
    return this.buildRequest("textDocument/semanticTokens/full", {
      textDocument: {
        uri
      }
    });
  }

  prepareRename(uri: string, position: Position): RequestMessage {
    return this.buildRequest("textDocument/prepareRename", {
      textDocument: {
        uri
      },
      position
    });
  }

  rename(uri: string, position: Position, newName: string): RequestMessage {
    return this.buildRequest("textDocument/rename", {
      textDocument: {
        uri
      },
      position,
      newName
    });
  }

  hover(uri: string, position: Position): RequestMessage {
    return this.buildRequest("textDocument/hover", {
      textDocument: {
        uri
      },
      position
    });
  }

  completion(uri: string, position: Position): RequestMessage {
    return this.buildRequest("textDocument/completion", {
      textDocument: {
        uri
      },
      position,
      context: {
        triggerKind: 1
      }
    });
  }

  initialized(): NotificationMessage {
    return this.buildNotification("initialized", {});
  }

  textDocumentDidOpen(uri: string, text: string): NotificationMessage {
    return this.buildNotification("textDocument/didOpen", {
      textDocument: {
        languageId: "nico",
        version: 1,
        uri,
        text
      }
    });
  }
}

export type LanguageServerAgentOptions = {
  // The sequence base number for RPC requests.
  // If you specify an array of number, the base number will be
  // calculated from its elements.
  sequence?: number | number[];
};

const calculateSequenceFromArray = (seeds: number[]): number => {
  //(i + 1) * 100 + j
  let sequence = 0;
  let multiplier = 1;

  for (let i = seeds.length - 1; i >= 0; i--) {
    sequence += seeds[i] * multiplier;
    multiplier *= 10;
  }

  return sequence;
};

const calculateSequence = (sequence: LanguageServerAgentOptions["sequence"]) => {
  const seq = sequence == null ? 0 : Array.isArray(sequence) ? calculateSequenceFromArray(sequence) : sequence;
  return 1000 + seq;
};

export class LanguageServerAgent {
  server: LanguageServer;
  builder: RequestBuilder;

  constructor(server: LanguageServer, options: LanguageServerAgentOptions) {
    const { sequence } = options;

    this.server = server;
    this.builder = new RequestBuilder({ id: calculateSequence(sequence) });
  }

  async openDocument(filename: string, src: string): Promise<any[]> {
    const uri = getDocumentUri(filename);

    const nextNotification = this.server.nextMessage<NotificationMessage>();
    const notification1 = this.builder.textDocumentDidOpen(uri, src);
    await this.server.sendNotification(notification1);

    const diagnostics = await nextNotification;

    expect(diagnostics.method).toEqual("textDocument/publishDiagnostics");
    expect(diagnostics.params).toBeDefined();
    expect(diagnostics.params!.uri).toEqual(uri);

    return diagnostics.params!.diagnostics;
  }

  async textDocumentSemanticTokenFull(filename: string): Promise<ResponseMessage> {
    const uri = getDocumentUri(filename);

    const request = this.builder.textDocumentSemanticTokenFull(uri);
    return this.server.sendRequest(request);
  }

  async prepareRename(filename: string, position: Position) {
    const uri = getDocumentUri(filename);

    const request = this.builder.prepareRename(uri, position);
    return this.server.sendRequest(request);
  }

  async rename(filename: string, position: Position, newName: string) {
    const uri = getDocumentUri(filename);

    const request = this.builder.rename(uri, position, newName);
    return this.server.sendRequest(request);
  }

  async hover(filename: string, position: Position) {
    const uri = getDocumentUri(filename);

    const request = this.builder.hover(uri, position);
    return this.server.sendRequest(request);
  }

  async completion(filename: string, position: Position) {
    const uri = getDocumentUri(filename);

    const request = this.builder.completion(uri, position);
    return this.server.sendRequest(request);
  }
}

// helpers
export async function spawn_server(options: InitializeOptions = {}): Promise<LanguageServer> {
  const builder = new RequestBuilder({ id: 1 });
  const server = LanguageServer.spawn();

  // initialize
  {
    const request = builder.initialize(options);
    await server.sendRequest(request);
  }

  // initialized
  {
    const notification = builder.initialized();
    await server.sendNotification(notification);
  }

  return server;
}

export function getDocumentUri(name?: string | number): string {
  const filename = encodeURIComponent(name == null ? "sample" : name.toString());
  return `file:///home/user/nico/sample${filename.substring(0, 64)}.nico`;
}
