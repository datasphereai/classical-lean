#!/usr/bin/env python3
"""Tests for build_registry.py and compile_rules.py. Runs itself: python3 test_compile_rules.py

Predictions, written before the first run (claude-ai, 2026-10-18):
  C1  build_registry reads a made-up section 6 of 4 rules             -> 4 rules, budget 4
  C2  check on that registry                                          -> PASS
  C3  render, pasted between the markers, then drift                  -> PASS no drift
  C4  one word of the pasted block changed by hand, then drift        -> FAIL drift
  C5  a fifth active self-applied rule added (budget 4)               -> FAIL budget
  C6  that fifth rule given a tool, enforcement "proposed"            -> still FAIL budget
  C7  the same, enforcement "verified" with verified_by               -> PASS
  C8  verified with no verified_by                                    -> FAIL
  C9  rule 2 merged into rule 1: render says "absorbs rule 2", count drops by one -> yes
  C10 merged_into a rule that does not exist                          -> FAIL
  C11 two rules with the same number                                  -> FAIL
  C12 report lists a subject holding two self-applied rules           -> yes
  C13 build_registry refuses to overwrite its output                  -> exit 1
  C14 a rule body holding a regex with backslashes survives the round trip -> identical text
  C15 a numbering gap in section 6 stops build_registry               -> nonzero exit
"""
import atexit
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
TMP = tempfile.mkdtemp(prefix="rules-test-")
atexit.register(shutil.rmtree, TMP, True)  # v2.1: no temp folder left behind (BREAK-IT-2 N13)
PASS = FAIL = 0

HANDOFF = r"""# HANDOFF

## 5. Naming

text

## 6. Working agreement

- **Local commits only.** Some history that is not a rule.
- **Rules learned in the runs.** Lead-in.
  1. *Check the invariant, not a proxy* — a gate example
     that runs over two lines.
  2. *Read a Mathlib definition before stating anything about it.* The bridge was written from
     the name.
  3. *Junk cells need random trials.* The builder refuses a line matched by `(?<![\d:])\d{1,2}:\d{2}(?!\d)`
     with no date `\d{4}-\d{2}-\d{2}`, and  two  spaces stay.
  4. *Stage every commit by path*, branch commits included.
- **Standing answers** (dated):
  - An answer, not a rule.
"""
SUBJECTS = {1: "gates", 2: "names", 3: "time", 4: "commits"}


def check(name, cond, detail=""):
    global PASS, FAIL
    PASS, FAIL = (PASS + 1, FAIL) if cond else (PASS, FAIL + 1)
    print(("ok   " if cond else "FAIL ") + name + ("" if cond else " :: " + detail))


def run(*args):
    p = subprocess.run([sys.executable] + list(args), capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr


def write(name, text):
    p = os.path.join(TMP, name)
    with open(p, "w") as fh:
        fh.write(text)
    return p


B = os.path.join(HERE, "build_registry.py")
C = os.path.join(HERE, "compile_rules.py")
h = write("HANDOFF.md", HANDOFF)
reg = os.path.join(TMP, "rules.toml")
rc, out = run(B, h, reg, "4")
check("C1 four rules, budget 4", rc == 0 and "4 rules" in out
      and "budget_self_applied = 4" in open(reg).read(), out)
rc, out = run(C, "check", reg, "--first")
check("C2 check passes", rc == 0 and "PASS" in out, out)
rc, block = run(C, "render", reg)
doc = os.path.join(TMP, "doc.md")
rc, out = run(C, "splice", reg, h, doc)   # v2: drift needs a real section 6, made by splice
rc, out = run(C, "drift", reg, doc)
check("C3 no drift after pasting the render", rc == 0 and "PASS" in out, out)
doc2 = write("doc2.md", open(doc).read().replace("invariant", "invariants", 1))
rc, out = run(C, "drift", reg, doc2)
check("C4 a hand edit is drift", rc == 1 and "FAIL drift" in out, out)

base = open(reg).read()
extra = """
[[rule]]
n = 5
title = '''A fifth rule.'''
body = '''Its body.'''
subject = "gates"
status = "active"
merged_into = 0
enforced_by = '''%s'''
enforcement = "%s"
verified_by = '''%s'''
last_caught = ""
"""
r5 = write("r5.toml", base + extra % ("", "", ""))
rc, out = run(C, "check", r5, "--first")
check("C5 over budget fails", rc == 1 and "budget" in out, out)
r6 = write("r6.toml", base + extra % ("tool.sh", "proposed", ""))
rc, out = run(C, "check", r6, "--first")
check("C6 a proposed tool still counts against the budget", rc == 1 and "budget" in out, out)
r7 = write("r7.toml", base + extra % ("tool.sh", "verified", "planted fault refused, row 20261018-099"))
rc, out = run(C, "check", r7, "--first")
check("C7 a verified tool frees the budget", rc == 0, out)
r8 = write("r8.toml", base + extra % ("tool.sh", "verified", ""))
rc, out = run(C, "check", r8, "--first")
check("C8 verified without verified_by fails", rc == 1 and "verified_by" in out, out)

merged = base.replace('n = 2\n', 'n = 2\n', 1)
i = merged.find("n = 2\n")
j = merged.find('status = "active"', i)
merged = merged[:j] + 'status = "merged"' + merged[j + len('status = "active"'):]
k = merged.find("merged_into = 0", i)
merged = merged[:k] + "merged_into = 1" + merged[k + len("merged_into = 0"):]
r9 = write("r9.toml", merged)
rc, out = run(C, "render", r9)
check("C9 merge folds rule 2 into rule 1", rc == 0 and "absorbs rule 2" in out
      and "(3 of a budget of 4" in out, out)
r10 = write("r10.toml", merged.replace("merged_into = 1", "merged_into = 99"))
rc, out = run(C, "check", r10, "--first")
check("C10 merged_into a missing rule fails", rc == 1 and "names no rule" in out, out)
r11 = write("r11.toml", base.replace("n = 4\n", "n = 3\n"))
rc, out = run(C, "check", r11, "--first")
check("C11 a number used twice fails", rc == 1 and "used twice" in out, out)
r12 = write("r12.toml", base.replace('subject = "names"', 'subject = "gates"'))
rc, out = run(C, "report", r12)
check("C12 report names the shared subject", rc == 0 and "gates" in out and "rules 1, 2" in out, out)
rc, out = run(B, h, reg, "4")
check("C13 build refuses to overwrite", rc == 1 and "refusing" in out, out)
import tomllib  # noqa: E402
with open(reg, "rb") as fh:
    body3 = [r for r in tomllib.load(fh)["rule"] if r["n"] == 3][0]["body"]
check("C14 backslashes survive", r"(?<![\d:])\d{1,2}:\d{2}(?!\d)" in body3 and r"\d{4}-\d{2}-\d{2}" in body3,
      body3)
gap = write("gap.md", HANDOFF.replace("  3. *Junk", "  5. *Junk"))
rc, out = run(B, gap, os.path.join(TMP, "gap.toml"), "4")
check("C15 a numbering gap stops the build", rc != 0, out)

# --- cases from the cold review of 2026-10-18 (findings C1 to C4, B1, B2); expected results first ---
# C1r: a rule added by hand after END -> FAIL; a second copy of the block -> FAIL
rc, block = run(C, "render", reg)
d1 = write("d1.md", "## 6. Working agreement\n\n" + block + "  5. *A rule added by hand.* Body.\n\n## 7. Next\n")
rc, out = run(C, "drift", reg, d1)
check("C1r-a a hand-written rule outside the block is drift", rc == 1 and "by hand" in out, out)
d2 = write("d2.md", "## 6. W\n\n" + block + "\n" + block.replace("Body", "Edited") + "\n")
rc, out = run(C, "drift", reg, d2)
check("C1r-b two copies of the block fail", rc == 1 and "exactly one" in out, out)
# C2r: budget raised in the registry -> FAIL against --base; with a new row id -> PASS
up = write("up.toml", open(r5).read().replace("budget_self_applied = 4", "budget_self_applied = 5"))
rc, out = run(C, "check", up, "--base", reg)
check("C2r-a a raised budget fails against the base", rc == 1 and "budget rose" in out, out)
# v2.1 (BREAK-IT-2 N9): the new rule 5 also needs its own change_note naming a store row, so the case gives it one
up2 = write("up2.toml", open(up).read().replace("[meta]\n", '[meta]\nbudget_raise_row = "20261019-001"\n', 1)
            + 'change_note = "added with the budget raise, store row 20261019-001"\n')
rc, out = run(C, "check", up2, "--base", reg)
check("C2r-b a raise with Dustin's row passes", rc == 0, out)
# C3r: typo [[rules]], n = true, an unknown key -> FAIL each
t1 = write("t1.toml", base.replace("[[rule]]", "[[rules]]"))
rc, out = run(C, "check", t1, "--first")
check("C3r-a [[rules]] typo fails", rc == 1 and ("unknown table" in out or "no [[rule]]" in out), out)
t2 = write("t2.toml", base.replace("n = 1\n", "n = true\n", 1))
rc, out = run(C, "check", t2, "--first")
check("C3r-b n = true fails", rc == 1, out)
t3 = write("t3.toml", base.replace('enforcement = ""', 'enforcment = ""', 1))
rc, out = run(C, "check", t3, "--first")
check("C3r-c an unknown key fails", rc == 1 and "unknown key" in out, out)
# C4r: double spaces inside a body survive render
rc, out = run(C, "render", reg)
check("C4r double spaces survive", "and  two  spaces stay" in out, out)
# B1: a column-0 bullet after rule 2 -> refused (count); a paragraph after the last rule is not merged
b1 = write("b1.md", HANDOFF.replace("  3. *Junk", "- a bullet\n  3. *Junk"))
rc, out = run(B, b1, os.path.join(TMP, "b1.toml"), "4")
check("B1a a bullet inside the rules stops the build", rc != 0, out)
b2 = write("b2.md", HANDOFF.replace("- **Standing answers** (dated):",
                                    "\nSee section 7 for the history of these.\n- **Standing answers** (dated):"))
rc, out = run(B, b2, os.path.join(TMP, "b2.toml"), "4")
body4 = open(os.path.join(TMP, "b2.toml")).read() if rc == 0 else ""
check("B1b a paragraph after the last rule is not merged into it", rc == 0 and "section 7" not in body4, out)
b3 = write("b3.md", HANDOFF.replace("\n  1. *", "\n1. *").replace("\n  2. *", "\n2. *")
           .replace("\n  3. *", "\n3. *").replace("\n  4. *", "\n4. *").replace("1. *", "        1. *"))
rc, out = run(B, b3, os.path.join(TMP, "b3.toml"), "4")
check("B1c rules at an unexpected indent give no silent empty registry", rc != 0, out)
rc, out = run(B, h, os.path.join(TMP, "b4.toml"), "5")
check("B1d a count other than expected is refused", rc == 1 and "expected 5" in out, out)
b5 = write("b5.md", HANDOFF.replace("  4. *Stage every commit by path*, branch commits included.",
                                    "  4. Stage every commit by path, branch commits included."))
rc, out = run(B, b5, os.path.join(TMP, "b5.toml"), "4")
check("B2a a rule with no italic title is refused", rc != 0 and "italic" in out, out)
b6 = write("b6.md", HANDOFF.replace("*Stage every commit by path*", "*Commit by path*"))
rc, out = run(B, b6, os.path.join(TMP, "b6.toml"), "4")
check("B2b a rule whose title moved is refused", rc != 0 and "numbers moved" in out, out)

rc, out = run(C, "render", reg)
check("R1 a body that starts with a comma joins the title without a space",
      "4. *Stage every commit by path*, branch commits included." in out, out)
# mkbrief.py's reader (LEAN-31 scripts): rule N runs from "  N. " to the next "  M. " or "- **" line
def mk_numbered(lines, num):
    for i, l in enumerate(lines):
        if _re0.match(r"^  {n}\. ".format(n=num), l):
            j = i + 1
            while j < len(lines) and not _re0.match(r"^  \d+\. ", lines[j]) and \
                    not _re0.match(r"^- \*\*|^---|^## ", lines[j]):
                j += 1
            return "\n".join(lines[i:j]).rstrip()
    return None


import re as _re0  # noqa: E402
rc, out = run(C, "render", r7)
lines = out.split("\n")
q = [mk_numbered(lines, n) for n in (1, 2, 3, 4, 5)]
check("MK each rule is quoted alone by mkbrief's reader, the enforced one included",
      all(x is not None and x.count("\n") == 0 and x.lstrip().startswith("%d. *" % n) for n, x in
          zip((1, 2, 3, 4, 5), q)), repr(q))
# --- RULES-1 order review (B1, M2, m2), expected results written first ---------------------------------
hb = os.path.join(TMP, "HANDOFF-copy.md")
open(hb, "w").write(HANDOFF)
rc, out = run(B, hb, os.path.join(TMP, "copy.toml"), "4")
check("O-B1 the registry does not depend on the source file's name",
      rc == 0 and open(os.path.join(TMP, "copy.toml")).read() == open(reg).read(), out)
import re as _re  # noqa: E402
gone = _re.sub(r"\[\[rule\]\]\nn = 2\n(?:.*\n)*?(?=\[\[rule\]\])", "", base, count=1)
g = write("gone.toml", gone.replace("budget_self_applied = 4", "budget_self_applied = 3"))
rc, out = run(C, "check", g, "--base", reg)
check("O-M2a a deleted rule fails against the base", rc == 1 and "missing now" in out, out)
ch = write("ch.toml", base.replace("two  spaces stay", "two  spaces go"))
rc, out = run(C, "check", ch, "--base", reg)
check("O-M2b a changed body without a change_note fails", rc == 1 and "change_note" in out, out)
ch2 = write("ch2.toml", base.replace("two  spaces stay", "two  spaces go").replace(
    "n = 3\n", 'n = 3\nchange_note = "RULES-1 merge, review 0123abcd"\n', 1))
rc, out = run(C, "check", ch2, "--base", reg)
check("O-M2c a changed body with a new change_note passes", rc == 0 and open(ch2).read() != base, out)
fold = write("fold.md", HANDOFF.replace("  4. *Stage every commit by path*, branch commits included.\n",
                                        "  4. *Stage every commit by path*, branch commits included.\n\n"
                                        "     An indented paragraph after a blank line.\n"))
rc, out = run(B, fold, os.path.join(TMP, "fold.toml"), "4")
check("O-m2a an indented paragraph after a blank line stops the build", rc != 0 and "blank line" in out, out)
tick = write("tick.md", HANDOFF.replace("*Stage every commit by path*", "*Stage `tools/*.py` by path*"))
rc, out = run(B, tick, os.path.join(TMP, "tick.toml"), "4")
check("O-m2b a title cut inside backticks stops the build", rc != 0, out)
# --- pass 2 of the cold review (C1, C2), expected results written first -------------------------------
rc, block = run(C, "render", reg)
for name, extra in (("unitalic numbered", "5. Never push on a Friday.\n"),
                    ("indent 4", "    5. *Indented rule.* Body.\n"),
                    ("bullet rule", "- *Rule 5.* Body.\n"),
                    ("new 6b heading", "## 6b. More rules\n\n5. *X.* Y.\n")):
    d = write("d-%s.md" % name.replace(" ", "-"),
              "## 6. Working agreement\n\n- **Local commits only.** History.\n- **Rules learned in the runs.**\n"
              + block + extra + "\n## 7. Next\n")
    rc, out = run(C, "drift", reg, d)
    check("C1p2 %s outside the block is drift" % name, rc == 1, out)
dok = os.path.join(TMP, "d-ok.md")
run(C, "splice", reg, h, dok)   # v2: section 6's text outside the block must be what the registry recorded
rc, out = run(C, "drift", reg, dok)
check("C1p2 the allowed bullets pass", rc == 0, out)
rc, out = run(C, "check", reg)
check("C2p2 check without --base is refused", rc == 2 and "--base" in out, out)

print("%d passed, %d failed" % (PASS, FAIL))
sys.exit(1 if FAIL else 0)
