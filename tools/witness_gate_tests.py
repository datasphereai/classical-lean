#!/usr/bin/env python3
"""The witness gate's tests (order VACUITY-4).

Usage, from the repository root:  python3 -I tools/witness_gate_tests.py [CASE ...]

Each case is a fixture root `tools/witness-fixtures/<case>/` holding one module
`ClassicalLean/Fixture.lean` (and, for a listing case, `tools/witness_reviewed.txt`), so each case's
rc is seen on its own. `tools/witness-fixtures/expected.tsv` gives, per case, the gate's expected rc
and its expected verdict tokens: `VERDICT@line` for each verdict line (`OK`, `PARTIAL`, `WRONG-NAME`,
`BROKEN`, `NO-DOCSTRING`, `TYPED-CLAIM`, `TYPED`, `NOT-A-BLOCK`, `UNREAD`, `LISTED`, `LISTED-FAULT`),
`RANGE-MISMATCH@line` and `DOC-MISMATCH@line`, and `COPY-ERROR` and `STALE-LISTING` without a
line. A case folder may also hold `gate-args` (arguments added to the gate's command, such as
`--driver-timeout 2`) and `expect-text` (lines each of which must occur in the gate's output, to
check a reason as well as a verdict: ruling 4, item 8).
The runner runs `python3 -I tools/witness_gate.py --root tools/witness-fixtures/<case>` for each
case, reads the tokens from its output, and prints `ok` or `MISMATCH` (with both token lists) per
case and a summary line. Exit 0 when every case matches, 1 otherwise. NOTE lines (Lean's warnings)
are not compared.

A case whose expected tokens are `SIGNAL` is the signal test (ruling 2, section 3 item 5): the
gate is started on it twice, and when a `lean` process is running in the session the gate names on
its standard error (`LEAN-SESSION <id>`), the gate is sent SIGINT, then on the second start SIGTERM;
the case matches when the gate exits and no process is left in that session (read with
`ps -s <id>`, by session id).

The fixtures are outside every other gate: `check_sorry.py` skips `tools/`, `banned_vocab_scan.py`
is run on `ClassicalLean`, `compile_rules.py` opens only the rule registry, its base copy and
`HANDOFF.md`, `check_records.py` walks only `ClassicalLean/`, and the library `ClassicalLean` does
not contain them.
"""
import os
import re
import signal
import subprocess
import sys
import time

VERDICTS = ("OK", "PARTIAL", "WRONG-NAME", "BROKEN", "NO-DOCSTRING", "TYPED-CLAIM", "TYPED",
            "NOT-A-BLOCK", "UNREAD", "LISTED", "LISTED-FAULT")
FIX = os.path.join("tools", "witness-fixtures")


def tokens(out):
    toks = []
    for ln in out.split("\n"):
        m = re.match(r"^(\S+) ClassicalLean/Fixture\.lean:(\d+)", ln)
        if m and m.group(1) in VERDICTS + ("RANGE-MISMATCH", "DOC-MISMATCH"):
            toks.append(f"{m.group(1)}@{m.group(2)}")
        elif ln.startswith("COPY-ERROR "):
            toks.append("COPY-ERROR")
        elif ln.startswith("STALE-LISTING "):
            toks.append("STALE-LISTING")
    return sorted(toks)


def session(sid):
    p = subprocess.run(["ps", "-o", "pid=,comm=", "-s", str(sid)], capture_output=True, text=True)
    return [ln.split() for ln in p.stdout.split("\n") if ln.strip()]


def signal_case(name):
    """Returns (ok, text) for the signal test on fixture `name`."""
    parts = []
    ok = True
    for sig in (signal.SIGINT, signal.SIGTERM):
        p = subprocess.Popen([sys.executable, "-I", os.path.join("tools", "witness_gate.py"), "--root",
                              os.path.join(FIX, name)], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             text=True)
        first = p.stderr.readline()
        m = re.match(r"LEAN-SESSION (\d+)", first)
        if not m:
            p.kill()
            p.wait()
            return False, f"no LEAN-SESSION line ({first.strip()[:80]})"
        sid = int(m.group(1))
        saw = False
        for _ in range(240):
            if any(c == "lean" for _, c in session(sid)):
                saw = True
                break
            time.sleep(0.5)
        p.send_signal(sig)
        try:
            p.wait(timeout=60)
        except subprocess.TimeoutExpired:
            p.kill()
            p.wait()
            ok = False
        time.sleep(1)
        left = session(sid)
        ok = ok and saw and not left
        parts.append(f"{signal.Signals(sig).name}: lean seen {saw}, gate rc {p.returncode}, "
                     f"left in session {sid}: {len(left)}")
    return ok, "; ".join(parts)


def main(argv):
    rows = []
    with open(os.path.join(FIX, "expected.tsv"), encoding="utf-8") as f:
        for ln in f:
            if ln.startswith("#") or not ln.strip():
                continue
            name, rc, toks = (ln.rstrip("\n").split("\t") + [""])[:3]
            rows.append((name, int(rc), sorted(toks.split())))
    if argv:
        rows = [r for r in rows if r[0] in argv]
    bad = 0
    for name, rc, want in rows:
        if want == ["SIGNAL"]:
            ok, text = signal_case(name)
            bad += not ok
            print(f"{'ok      ' if ok else 'MISMATCH'} {name:28} {text}")
            continue
        extra, texts = [], []
        ga = os.path.join(FIX, name, "gate-args")
        if os.path.exists(ga):
            with open(ga, encoding="utf-8") as f:
                extra = f.read().split()
        et = os.path.join(FIX, name, "expect-text")
        if os.path.exists(et):
            with open(et, encoding="utf-8") as f:
                texts = [ln.rstrip("\n") for ln in f if ln.strip()]
        p = subprocess.run([sys.executable, "-I", os.path.join("tools", "witness_gate.py"), "--root",
                            os.path.join(FIX, name)] + extra, capture_output=True, text=True)
        got = tokens(p.stdout)
        summary = [ln for ln in p.stdout.split("\n") if ln.startswith("WITNESSGATE ")]
        missing = [t for t in texts if t not in p.stdout]
        ok = got == want and p.returncode == rc and len(summary) == 1 and not missing
        bad += not ok
        print(f"{'ok      ' if ok else 'MISMATCH'} {name:28} rc {p.returncode} (expected {rc}) "
              f"{' '.join(got)}" + ("" if ok else f"  expected: {' '.join(want)}")
              + (f"  missing text: {missing}" if missing else ""))
        if not ok:
            for ln in (p.stdout + p.stderr).split("\n"):
                if ln and not ln.startswith(("NOTE ", "OPTIONS ")):
                    print(f"    | {ln[:240]}")
    print(f"WITNESSGATE-TESTS {len(rows)} cases, {bad} mismatch(es)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
