#!/usr/bin/env python3
"""Run the vacuity gate's test on the theorems in tools/VacuityGateTests.lean.

Usage (from the repository root):  python3 -I tools/run_vacuity_tests.py [--gate FILE] [--report-only]

The gate file (default tools/VacuityGate.lean) cannot be imported, and the test file is not in the
library, so this script joins them: it copies the test file, then the gate's code (from its
`open Lean` line to `end VacuityGate`), then a command that prints `FLAG <name>` or `PASS <name>`
for every theorem in the namespace `VacuityGateTests`, into a scratch file, and runs
`lake env lean` on it. The per-theorem heartbeat budget is read from the gate file.

The first word of each test's name is its expectation: `vac_` must be flagged; `real_` and `lim_`
must pass. Exit 0 when every test meets its expectation (or with --report-only, when every test
got a verdict), 1 otherwise. `--gate FILE` tests another version of the gate, e.g. one written out
by `git show <commit>:tools/VacuityGate.lean`.
"""
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.getcwd()
TESTS = os.path.join(ROOT, "tools", "VacuityGateTests.lean")


def gate_section(text):
    lines = text.splitlines()
    start = next(i for i, l in enumerate(lines) if l.startswith("open Lean"))
    end = next(i for i, l in enumerate(lines) if l.strip() == "end VacuityGate")
    return "\n".join(lines[start:end + 1])


def heartbeats(text):
    m = re.search(r"set_option maxHeartbeats (\d+) in\s*\nrun_cmd", text)
    return m.group(1) if m else "200000"


REPORT = """
set_option maxHeartbeats {hb} in
run_cmd do
  let env ← Lean.getEnv
  let mut names : Array Lean.Name := #[]
  for (n, ci) in env.constants.toList do
    if let .thmInfo _ := ci then
      if (`VacuityGateTests).isPrefixOf n && !n.hasMacroScopes then names := names.push n
  for n in names.qsort (·.toString < ·.toString) do
    let ty := (← Lean.getConstInfo n).type
    try
      let v ← Lean.Elab.Command.liftTermElabM (VacuityGate.isVacuousType ty)
      Lean.logInfo s!"{{if v then "FLAG" else "PASS"}} {{n}}"
    catch e =>
      Lean.logInfo m!"ERROR {{n}}: {{e.toMessageData}}"
"""


def main(argv):
    gate = os.path.join(ROOT, "tools", "VacuityGate.lean")
    report_only = False
    args = list(argv)
    while args:
        a = args.pop(0)
        if a == "--gate":
            gate = args.pop(0)
        elif a == "--report-only":
            report_only = True
        else:
            print("unknown argument", a)
            return 2
    gtext = open(gate, encoding="utf-8").read()
    body = open(TESTS, encoding="utf-8").read()
    src = body + "\n\n" + gate_section(gtext) + "\n" + REPORT.format(hb=heartbeats(gtext))
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "VacuityGateTestRun.lean")
        with open(path, "w", encoding="utf-8") as f:
            f.write(src)
        p = subprocess.run(["lake", "env", "lean", path], cwd=ROOT,
                           capture_output=True, text=True)
    out = p.stdout + p.stderr
    verdicts = {}
    for m in re.finditer(r"\b(FLAG|PASS|ERROR) (VacuityGateTests\.\S+?):?(?=\s|$)", out):
        verdicts[m.group(2)] = m.group(1)
    if p.returncode != 0 or not verdicts:
        print(out)
        print(f"lean rc {p.returncode}, {len(verdicts)} verdicts")
        return 1
    bad = 0
    for n, v in sorted(verdicts.items()):
        short = n.split(".")[-1]
        want = "FLAG" if short.startswith("vac_") else "PASS"
        ok = v == want
        bad += (not ok) if not report_only else (v == "ERROR")
        print(f"{v:5} {short:36} expected {want:5} {'ok' if ok else 'MISMATCH'}")
    print(f"{len(verdicts)} tests, {sum(v == 'FLAG' for v in verdicts.values())} flagged, "
          f"{bad} {'errors' if report_only else 'mismatches'}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
