import { spawn } from "child_process";

test("Language Server", async done => {
  const server = spawn("./target/debug/nico-ls", [], {
    env: {
      RUST_LOG: "info",
      RUST_BACKTRACE: "full"
    }
  });

  server.stdout.on("data", data => {
    console.log(`stdout: ${data}`);
  });

  server.stderr.on("data", data => {
    console.warn(`stderr: ${data}`);
  });

  server.on("close", code => {
    console.log(`child process closed with code ${code}`);
    done();
  });

  setTimeout(() => {
    server.kill();
  }, 1000);
});
