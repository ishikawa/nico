import os from "os";
import path from "path";
import { main } from "../runner/cli";
import { compileFileToWATFile } from "./util/compiler";
import glob from "glob";

test("given empty input", async () => {
  const consoleSpy = jest.spyOn(console, "log").mockImplementation(() => {});

  let code = await main([]);

  expect(code).toEqual(1);
  expect(consoleSpy.mock.calls).toHaveLength(1);
  expect(consoleSpy.mock.calls[0][0]).toMatch(/Usage:/);

  consoleSpy.mockReset();
});

glob.sync("./samples/**/*.nico").forEach(file => {
  test(file, async () => {
    const consoleSpy = jest.spyOn(console, "log").mockImplementation(() => {});
    const outputFilepath = path.join(os.tmpdir(), path.basename(file));

    await compileFileToWATFile(file, outputFilepath);

    let code = await main(["node", "nico", outputFilepath]);

    expect(code).toEqual(0);
    expect(consoleSpy.mock.calls).toMatchSnapshot();

    consoleSpy.mockReset();
  });
});
