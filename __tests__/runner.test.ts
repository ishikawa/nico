import { main } from "../runner/cli";

test("given empty input", async () => {
  const consoleSpy = jest.spyOn(console, "log").mockImplementation(() => {});

  let code = await main([]);

  expect(code).toEqual(1);
  expect(consoleSpy.mock.calls).toHaveLength(1);
  expect(consoleSpy.mock.calls[0][0]).toMatch(/Usage:/);
});
