#!/usr/bin/env python3
"""Run the vacuity gate's test on the theorems in tools/VacuityGateTests.lean.

Usage (from the repository root):
  python3 -I tools/run_vacuity_tests.py [--gate FILE] [--tests FILE] [--list FILE] [--report-only]

The gate file (default tools/VacuityGate.lean) cannot be imported, and the test file is not in the
library, so this script joins them: it copies the test file, then the gate's code (from its
`open Lean` line to `end VacuityGate`), then a command that prints `FLAG <name>` or `PASS <name>`
for every theorem in the namespace `VacuityGateTests`, into a scratch file, and runs
`lake env lean` on it. The per-theorem heartbeat budget is read from the gate file.

Names are printed with the private prefix dropped and macro scopes erased (a theorem written by a
hygienic macro), and the expectation is read from that name. The first word of each test's name is
its expectation: `vac_` must be flagged, `vac_unchecked_` must come out UNCHECKED (fail closed)
with the message `UNCONFIRMED_MSG` below, the gate's `unconfirmedMsg` (a different message is a
MISMATCH, order VACUITY-3); `real_` and `lim_` must pass. Exit 0 when every test meets its expectation (or with --report-only, when every test
got a verdict), 1 otherwise. `--gate FILE` tests another version of the gate, e.g. one written out
by `git show <commit>:tools/VacuityGate.lean`; `--tests` and `--list` replace the test file and
its reviewed list (theorems in another file must also sit in the namespace `VacuityGateTests`).
"""
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.getcwd()
TESTS = os.path.join(ROOT, "tools", "VacuityGateTests.lean")
LIST = os.path.join(ROOT, "tools", "vacuity_reviewed_tests.txt")
# The message a `vac_unchecked_` test must carry on its UNCHECKED line: the gate's `unconfirmedMsg`
# (order LEAN-27, job 0), kept here as a literal so that a change to the gate's message is caught
# (order VACUITY-3).
UNCONFIRMED_MSG = "every case is True; kernel could not confirm the proof"
# Width of the verdict columns: the longest verdict, KERNEL-REJECTED.
W = max(len(v) for v in ("FLAG", "PASS", "LISTED", "PENDING", "STALE", "SKIP", "ERROR",
                         "KERNEL-REJECTED", "UNCHECKED"))


def gate_section(text):
    lines = text.splitlines()
    start = next(i for i, l in enumerate(lines) if l.startswith("open Lean"))
    end = next(i for i, l in enumerate(lines) if l.strip() == "end VacuityGate")
    return "\n".join(lines[start:end + 1])


def heartbeats(text):
    m = re.search(r"set_option maxHeartbeats (\d+) in\s*\nrun_cmd", text)
    return m.group(1) if m else "200000"


REPORT_OLD = """
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

# For a gate with a reviewed list (VACUITY-1 on): the verdict after the list, read from LIST.
REPORT = """
set_option maxHeartbeats {hb} in
run_cmd do
  let list ← VacuityGate.loadList "{lst}"
  let env ← Lean.getEnv
  let mut names : Array Lean.Name := #[]
  for (n, ci) in env.constants.toList do
    if let .thmInfo _ := ci then
      if (`VacuityGateTests).isPrefixOf (Lean.privateToUserName n) then
        names := names.push n
  {used_line}
  -- names the gate flagged or listed: an entry that matches none of them is stale, as in the gate
  let mut hit : Array Lean.Name := #[]
  for n in names.qsort (·.toString < ·.toString) do
    let ty := (← Lean.getConstInfo n).type
    let u := (Lean.privateToUserName n).eraseMacroScopes
    if {macro_skip} && n.hasMacroScopes then
      Lean.logInfo s!"SKIP {{u}}"
      continue
    if ← {helper_test} then
      Lean.logInfo s!"SKIP {{u}}"
      continue
    try
      {judge_match}
      | .pass => Lean.logInfo s!"PASS {{u}}"
      | .flag h _ w =>
        hit := hit.push u
        Lean.logInfo s!"FLAG {{u}} {{h}} [{{w}}]"
      | .listed e w =>
        hit := hit.push u
        Lean.logInfo s!"{{if e.pending then "PENDING" else "LISTED"}} {{u}} [{{w}}]"
      | .unchecked m => Lean.logInfo s!"UNCHECKED {{u}}: {{m}}"  -- every path: see VacuityGate.Verdict.unchecked
      {kernel_case}
    catch e =>
      Lean.logInfo m!"ERROR {{u}}: {{e.toMessageData}}"
  for e in list do
    unless hit.contains e.name do Lean.logInfo s!"STALE {{e.name}}"
"""


def main(argv):
    gate = os.path.join(ROOT, "tools", "VacuityGate.lean")
    tests, lst = TESTS, LIST
    report_only = False
    args = list(argv)
    while args:
        a = args.pop(0)
        if a == "--gate":
            gate = args.pop(0)
        elif a == "--tests":
            tests = os.path.abspath(args.pop(0))
        elif a == "--list":
            lst = os.path.abspath(args.pop(0))
        elif a == "--report-only":
            report_only = True
        else:
            print("unknown argument", a)
            return 2
    gtext = open(gate, encoding="utf-8").read()
    body = open(tests, encoding="utf-8").read()
    report = REPORT if "def judge" in gtext else REPORT_OLD
    # a gate whose scan skips names with macro scopes: the runner skips them too, and says SKIP
    macro_skip = "true" if "if n.hasMacroScopes then continue" in gtext else "false"
    # a gate that skips only the `_proof_` helpers some declaration uses (VACUITY-2 on)
    if "def usedHelpers" in gtext:
        used_line = "let used ← Lean.Elab.Command.liftCoreM VacuityGate.usedHelpers"
        helper_test = "VacuityGate.isTacticHelper used n"
    else:
        used_line, helper_test = "", "VacuityGate.isTacticHelper n"
    # a gate whose flags are checked by the kernel (VACUITY-2 on) has a verdict for a rejection
    kernel_case = ('| .kernelRejected w m => Lean.logInfo s!"KERNEL-REJECTED {u} [{w}]: {m}"'
                   if "kernelRejected" in gtext else "")
    # a gate with rule 5 (VACUITY-2 on): judge also returns rule 5 running out, printed apart
    if "def rule5" in gtext:
        judge_match = ('let (v, ro) ← VacuityGate.judge list n ty\n'
                       '      if let some m := ro then Lean.logInfo s!"RULE5-RANOUT {u}: {m}"\n'
                       '      match v with')
    else:
        judge_match = "match ← VacuityGate.judge list n ty with"
    src = (body + "\n\n" + gate_section(gtext) + "\n"
           + report.format(hb=heartbeats(gtext), lst=lst, macro_skip=macro_skip,
                           used_line=used_line, helper_test=helper_test, kernel_case=kernel_case,
                           judge_match=judge_match))
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "VacuityGateTestRun.lean")
        with open(path, "w", encoding="utf-8") as f:
            f.write(src)
        p = subprocess.run(["lake", "env", "lean", path], cwd=ROOT,
                           capture_output=True, text=True)
    out = p.stdout + p.stderr
    verdicts, hashes = {}, {}
    for m in re.finditer(r"\b(FLAG|PASS|LISTED|PENDING|STALE|SKIP|ERROR|KERNEL-REJECTED|UNCHECKED) (VacuityGateTests\.\S+?):?(?=\s|$)( [0-9a-f]{64})?( \[[^\]]*\])?", out):
        verdicts[m.group(2)] = m.group(1)
        hashes[m.group(2)] = ((m.group(4) or "") + " " + (m.group(3) or "")).strip()
    if p.returncode != 0 or not verdicts:
        print(out)
        print(f"lean rc {p.returncode}, {len(verdicts)} verdicts")
        return 1
    # a real_ test, or a generated declaration, whose name is on the test list must come out
    # LISTED (flagged, then passed
    # through its entry); run with `--list /dev/null` to see the flag itself
    listed = set()
    if os.path.exists(lst):
        for l in open(lst, encoding="utf-8"):
            if l.strip() and not l.startswith("#"):
                listed.add(l.split()[0])
    # the message on each UNCHECKED line, as the runner's own report prints it
    messages = {m.group(1): m.group(2).strip()
                for m in re.finditer(r"UNCHECKED (VacuityGateTests\.\S+?): (.*)", out)}
    bad = 0
    for n, v in sorted(verdicts.items()):
        # the test's own name: the component after `VacuityGateTests`
        short = n.split(".", 1)[1]
        want = {"vac": "FLAG", "listed": "LISTED", "pending": "PENDING",
                "stale": "STALE"}.get(short.split("_")[0], "PASS")
        # `vac_unchecked_`: empty, and the gate cannot confirm its proof, so it must fail closed
        # as UNCHECKED (Dustin's ruling of 2026-10-13, order LEAN-27 job 0)
        if short.startswith("vac_unchecked_"):
            want = "UNCHECKED"
        # any name on the test list that is not a `vac_` test, also one Lean generates (VACUITY-2)
        if want == "PASS" and n in listed:
            want = "LISTED"
        # a generated `_proof_` helper of a theorem that must pass may be skipped
        if want == "PASS" and v == "SKIP" and "._proof_" in short:
            want = "SKIP"
        ok = v == want
        # an expected UNCHECKED must also carry the gate's message (order VACUITY-3)
        if ok and want == "UNCHECKED" and short.startswith("vac_unchecked_"):
            ok = messages.get(n) == UNCONFIRMED_MSG
        bad += (not ok) if not report_only else (v == "ERROR")
        print(f"{v:{W}} {short:36} expected {want:{W}} {'ok' if ok else 'MISMATCH'} {hashes[n]}")
    for m in re.finditer(r"KERNEL-REJECTED (VacuityGateTests\.\S+) \[([^\]]*)\]: (.*)", out):
        print(f"kernel rejected {m.group(1).split('.', 1)[1]} [{m.group(2)}]: {m.group(3)}")
    for n, msg in sorted(messages.items()):
        short = n.split('.', 1)[1]
        check = ""
        if short.startswith("vac_unchecked_"):
            check = (" (message as expected)" if msg == UNCONFIRMED_MSG
                     else f" (WRONG MESSAGE: expected {UNCONFIRMED_MSG!r})")
        print(f"unchecked {short}: {msg}{check}")
    ranout = re.findall(r"RULE5-RANOUT (VacuityGateTests\.\S+?):", out)
    for n in sorted(ranout):
        print(f"rule 5 ran out: {n.split('.', 1)[1]}")
    print(f"{len(verdicts)} tests, {sum(v == 'FLAG' for v in verdicts.values())} flagged, "
          f"{len(ranout)} rule-5 run-outs, {bad} {'errors' if report_only else 'mismatches'}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
