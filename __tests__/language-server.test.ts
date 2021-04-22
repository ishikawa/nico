import { spawn, ChildProcessWithoutNullStreams } from "child_process";
import { EventEmitter } from "events";

// https://microsoft.github.io/language-server-protocol/specifications/specification-current/#baseProtocol
interface Message {
  jsonrpc: string;
}

interface RequestMessage extends Message {
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

interface ResponseMessage extends Message {
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

class LanguageServer extends EventEmitter {
  process: ChildProcessWithoutNullStreams;

  payload: string;

  constructor(process: ChildProcessWithoutNullStreams) {
    super();

    this.process = process;
    this.process.stdout.on("data", this.onReceive.bind(this));

    this.payload = "";
  }

  onReceive(data: Buffer) {
    // For simplicity, we assume whole payload arrived at once.
    const payload = data instanceof Buffer ? data.toString("utf-8") : data;

    this.payload += payload;

    // Split payload into header and content.
    // If the received contents is valid JSON-RPC message, the number of
    // elements is greater than 3.
    const parts = this.payload.split("\r\n", 4);

    if (parts.length >= 3) {
      const content = parts[parts.length - 1];

      if (content.length > 0) {
        const message = JSON.parse(content);

        this.payload = "";
        this.emit("message", message);
      }
    }
  }

  sendRequest(message: RequestMessage): Promise<ResponseMessage> {
    const promise = new Promise<ResponseMessage>((resolve, _reject) => {
      this.once("message", resolve);
    });

    const payload = JSON.stringify(message);

    // Write a request

    this.process.stdin.write(`Content-Length: ${payload.length}\r\n`);
    this.process.stdin.write("\r\n");
    this.process.stdin.write(payload);

    return promise;
  }
}

test("Language Server", async done => {
  const process = spawn("./target/debug/nico-ls", [], {
    env: {
      RUST_LOG: "info",
      RUST_BACKTRACE: "full"
    }
  });

  const server = new LanguageServer(process);

  // Initialize - params
  const params = {
    trace: "verbose",
    capabilities: {
      textDocument: {
        publishDiagnostics: {
          relatedInformation: true,
          versionSupport: false,
          tagSupport: {
            valueSet: [1, 2]
          },
          codeDescriptionSupport: true,
          dataSupport: true
        }
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
  };

  const request = {
    jsonrpc: "2.0",
    id: 1,
    method: "initialize",
    params
  };

  const response = await server.sendRequest(request);

  expect(response).toEqual({
    jsonrpc: "2.0",
    id: 1,
    result: {
      capabilities: {
        semanticTokensProvider: {
          full: true,
          legend: {
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
            tokenTypes: [
              "keyword",
              "variable",
              "string",
              "number",
              "operator",
              "comment",
              "function",
              "struct",
              "function",
              "parameter",
              "property"
            ]
          }
        },
        textDocumentSync: 2
      },
      serverInfo: { name: "nico-ls", version: "0.0.1" }
    },
    error: null
  });

  process.stdout.on("data", data => {
    const message = parseJsonRpcMessage(data);
    console.log(`received`, ServiceWorkerMessageEvent);
  });

  process.stderr.on("data", data => {
    console.warn(`stderr: ${data}`);
  });

  process.on("close", code => {
    console.log(`child process closed with code ${code}`);
    done();
  });

  setTimeout(() => {
    if (!process.killed) {
      process.kill();
    }
  }, 1000);
});

function parseJsonRpcMessage(data: string | Buffer): any {
  // For simplicity, we assume whole payload arrived at once.
  const payload = data instanceof Buffer ? data.toString("utf-8") : data;
  console.log("parse", payload);

  // Split payload into header and content.
  const parts = payload.split("\r\n", 4);

  // The last element is "Content-Part"
  return JSON.parse(parts[parts.length - 1]);
}
