#!/usr/bin/env python3
"""BREAK-IT-2 regression cases for compile_rules.py check (v2.1). Runs itself: python3 test_breakit2_rules.py

From the reviewer's /home/dustin/claude-ai-witness/from-break-it-2/rules/edits.py (finding N9: a verified rule
could swap its tool, and a brand-new rule could enter, with no store row). Expected results, written before the
first run of v2.1:
  N1 a verified rule's tool changed from el.sh to trust-me.sh, note "renamed the tool"      -> FAIL (needs a row)
  N2 the same with a note naming a store row                                                 -> PASS
  N3 a new rule 5, verified, with no change_note                                             -> FAIL
  N4 a new rule 5 with a change_note naming a store row (and the budget it fits)             -> PASS
  N5 the tool of a rule that is only proposed changed, with a new plain note                 -> PASS (no row needed)
  N6 unchanged registry                                                                      -> PASS
Not changed on purpose, and still PASS: a body rewritten with a new note that names no row (a reviewer can read
the diff), and a retire that cites a row the compiler cannot look up (no store access, by design).
No temp folder is left behind.
"""
import atexit
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
B = os.path.join(HERE, "build_registry.py")
C = os.path.join(HERE, "compile_rules.py")
TMP = tempfile.mkdtemp(prefix="rules-bi2-")
atexit.register(shutil.rmtree, TMP, True)
results = []
HANDOFF = r"""# HANDOFF

## 6. Working agreement

- **Rules learned in the runs.** Lead-in.
  1. *Check the invariant, not a proxy* — a gate example.
  2. *Read a Mathlib definition before stating anything about it.* The bridge was written from the name.
  3. *Junk cells need random trials.* Two spaces stay.
  4. *Stage every commit by path*, branch commits included.
- **Standing answers** (dated):
  - An answer, not a rule.
"""


def run(*args):
    p = subprocess.run([sys.executable, "-I"] + list(args), capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr


def check(name, cond, detail=""):
    results.append((name, bool(cond), detail))


h = os.path.join(TMP, "HANDOFF.md")
open(h, "w").write(HANDOFF)
raw = os.path.join(TMP, "raw.toml")
rc, out = run(B, h, raw, "4")
assert rc == 0, out
text = open(raw).read()
# the base: rule 1 enforced by a verified tool; rule 2 by a proposed one
rule1 = text.split("[[rule]]\nn = 1\n", 1)[1].split("[[rule]]", 1)[0]
rule2 = text.split("[[rule]]\nn = 2\n", 1)[1].split("[[rule]]", 1)[0]
v1 = (rule1.replace("enforced_by = ''''''", "enforced_by = '''el.sh'''")
      .replace('enforcement = ""', 'enforcement = "verified"')
      .replace('verified_by = ""', 'verified_by = "planted fault, store row 20261018-030"'))
p2 = rule2.replace("enforced_by = ''''''", "enforced_by = '''lint.sh'''").replace('enforcement = ""', 'enforcement = "proposed"')
base_text = text.replace(rule1, v1, 1).replace(rule2, p2, 1)
base = os.path.join(TMP, "base.toml")
open(base, "w").write(base_text)


def variant(name, new_text):
    p = os.path.join(TMP, name + ".toml")
    open(p, "w").write(new_text)
    return run(C, "check", p, "--base", base)


rc, out = variant("same", base_text)
check("N6 an unchanged registry passes", rc == 0 and "PASS" in out, out)
swap = base_text.replace(v1, v1.replace("'''el.sh'''", "'''trust-me.sh'''") + 'change_note = "renamed the tool"\n', 1)
rc, out = variant("swap", swap)
check("N1 a verified rule's tool swapped with a plain note fails", rc == 1 and "rule 1" in out, out)
swap_row = base_text.replace(v1, v1.replace("'''el.sh'''", "'''trust-me.sh'''")
                             + 'change_note = "tool renamed; planted fault re-run, store row 20261019-099"\n', 1)
rc, out = variant("swaprow", swap_row)
check("N2 the same with a note naming a store row passes", rc == 0 and "PASS" in out, out)
new_rule = ('\n[[rule]]\nn = 5\ntitle = \'\'\'A fifth rule\'\'\'\nbody = \'\'\'It says something new.\'\'\'\n'
            'subject = "new"\nstatus = "active"\nmerged_into = 0\nenforced_by = \'\'\'el.sh\'\'\'\n'
            'enforcement = "verified"\nverified_by = "planted fault, store row 20261018-031"\nlast_caught = ""\n')
rc, out = variant("new", base_text + new_rule)
check("N3 a new rule with no change_note fails", rc == 1 and "rule 5 is new" in out, out)
rc, out = variant("newrow", base_text + new_rule + 'change_note = "added by Dustin, store row 20261019-098"\n')
check("N4 a new rule whose change_note names a store row passes", rc == 0 and "PASS" in out, out)
prop = base_text.replace(p2, p2.replace("'''lint.sh'''", "'''lint2.sh'''") + 'change_note = "the lint tool moved"\n', 1)
rc, out = variant("prop", prop)
check("N5 a proposed tool changed with a plain new note passes", rc == 0 and "PASS" in out, out)
failed = [r for r in results if not r[1]]
for name, ok, d in results:
    print(("ok   " if ok else "FAIL ") + name + ("" if ok else "  :: " + d.replace("\n", " | ")[:600]))
print("test_breakit2_rules: %d passed, %d failed" % (len(results) - len(failed), len(failed)))
sys.exit(1 if failed else 0)
