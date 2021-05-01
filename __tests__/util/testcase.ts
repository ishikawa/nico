export interface TestCaseBase {
  input?: string;
  file?: string;

  // filters
  // - **focus** - Include these tests only.
  // - **skip** - Exclude these tests.
  focus?: boolean;
  skip?: boolean;
}

export function filterTestCases<T extends TestCaseBase>(cases: T[]): T[] {
  let focused = cases.filter(x => x.focus);
  focused = focused.length === 0 ? cases : focused;
  focused = focused.filter(x => !x.skip);

  return focused;
}
