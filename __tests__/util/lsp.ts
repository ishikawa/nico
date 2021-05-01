import { spawn, ChildProcessWithoutNullStreams } from "child_process";
import { EventEmitter } from "events";

const DEBUG = false;

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
  params?: any;
}

type InitializeOptions = { rename?: boolean };

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

  initialize({ rename }: InitializeOptions = {}): RequestMessage {
    const params = {
      trace: "verbose",
      capabilities: {
        textDocument: {
          ...(rename
            ? {
                rename: {
                  dynamicRegistration: true,
                  prepareSupport: true,
                  prepareSupportDefaultBehavior: 1,
                  honorsChangeAnnotations: true
                }
              }
            : {}),
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
