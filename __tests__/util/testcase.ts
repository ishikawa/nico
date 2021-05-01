import fs from "fs";

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

export function readTestFileSync(testCase: TestCaseBase): string {
  if (testCase.input) {
    return testCase.input;
  } else if (testCase.file) {
    const srcBuffer = fs.readFileSync(testCase.file);
    return srcBuffer.toString("utf-8");
  }

  return "";
}

export function getTestName(testCase: TestCaseBase): string {
  if (testCase.input) {
    return testCase.input;
  } else if (testCase.file) {
    return testCase.file;
  }

  return "-";
}

export function getDocumentUri(name?: string | number): string {
  const filename = encodeURIComponent(name == null ? "sample" : name.toString());
  return `file:///home/user/nico/sample${filename}.nico`;
}
