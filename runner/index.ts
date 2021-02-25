import { main } from "./cli";

main(process.argv).then(exitCode => {
  process.exitCode = exitCode;
});
