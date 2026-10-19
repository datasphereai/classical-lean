#!/usr/bin/env python3
"""build_registry: make the first rule registry from HANDOFF.md section 6 (run once).

Reads the numbered rules of section 6 ("Working agreement") and writes a TOML
registry for compile_rules.py, with claude-ai's proposals of 2026-10-18 for
each rule's subject and for the tool that may already enforce it. Every tool
is written as enforcement = "proposed": nothing counts as enforced until a
session shows the tool refusing a planted fault and sets "verified". The
budget starts at the number of rules (39 on 2026-10-18), which is Dustin's one
in, one out of 2026-10-18 (store row 20261018-010).

Usage: build_registry.py <HANDOFF.md> <out.toml> <expected number of rules>
It refuses to overwrite <out.toml>, and stops on anything it cannot place: a gap or
repeat in the numbering, a count other than the expected one, a rule-shaped line
after the rules end, a rule with no *italic title*, or a proposal whose rule's
title does not start as recorded below (the numbers moved).
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import compile_rules  # noqa: E402  (the same section and anchor rules as splice and drift)

CONTROL_RE = re.compile(r"[\x00-\x08\x0b-\x1f\x7f]")
RULE_SHAPE_RE = re.compile(r"^\s*\(?\d{1,3}[.)]\s+\*")   # any numbered line with an italic title

# claude-ai's proposals, 2026-10-18, from reading each rule's text (not yet checked against
# the tools themselves). subject: which rules say the same kind of thing.
SUBJECT = {
    1: "gates", 14: "gates", 25: "gates",
    2: "names", 35: "names", 37: "names",
    3: "tests", 10: "tests", 15: "tests", 27: "tests", 28: "tests",
    4: "commits", 6: "commits", 7: "commits", 39: "commits",
    5: "evidence-log", 8: "evidence-log", 23: "evidence-log", 30: "evidence-log", 32: "evidence-log",
    9: "time", 36: "time",
    11: "build", 20: "build", 38: "build",
    12: "reviewers", 24: "reviewers",
    13: "review-order", 16: "review-order", 21: "review-order", 29: "review-order", 31: "review-order",
    17: "saved-outputs", 33: "saved-outputs",
    18: "records", 19: "records",
    22: "quotes", 26: "quotes", 34: "quotes",
}
# The tool a rule's own text says enforces it (to be verified by a planted fault).
TOOL = {
    22: "quotecheck.py",
    23: "ev.sh (refuses to run without a prediction)",
    26: "close-brief-make (builds briefs by script)",
    32: "ev.sh / land.sh (evidence writes run through the helper)",
    34: "inlinecheck.py",
    36: "the brief builder (refuses a time with no date)",
    37: "el.sh (refuses an unprobed name)",
    38: "rootrun.sh (refuses unless a fresh root build passed)",
    39: "evcite.py and citecheck.py",
}

# The start of each rule's title on 2026-10-18 (order LEAN-32's HANDOFF.md, a6d5c0f). A proposal is
# applied only when the rule with that number still starts this way.
TITLE_START = {
    1: "Check the invariant", 2: "Read a Mathlib definition", 3: "Junk cells need", 4: "Stage every commit",
    5: "Every evidence-log line", 6: "Any linter or option", 7: "Write a commit message only",
    8: "An evidence log records", 9: "Time windows use", 10: "Test harnesses match", 11: "`lake env lean`",
    12: "Reviewers work in", 13: "Every new declaration", 14: "Before-and-after evidence",
    15: "A pattern written for", 16: "A statement review's verdict", 17: "Every reviewer and checker",
    18: "Records follow the clock", 19: "Research notes name", 20: "Scratch proofs are elaborated",
    21: "A statement drafted in a plan", 22: "Every quote in a fragment", 23: "Evidence commands run",
    24: "Every reader, research", 25: "Type-dump Done-means", 26: "Every brief is built",
    27: "A count that Lean generates", 28: "A workflow or script that consumes", 29: "A review fix that touches",
    30: "A refused call is logged", 31: "No statement of a job", 32: "Every write, hash and edit",
    33: "A workflow returns each", 34: "Every inline quote", 35: "A commit message says only",
    36: "Every clock time carries", 37: "A name is probed", 38: "A tool that imports", 39: "Run citations in commit",
}

RULE_START = re.compile(r"^ {1,3}(\d{1,3})\.\s+(.*)$")  # a rule starts at an indent of 1 to 3
SECTION_START = re.compile(r"^## 6\.")
STANDING = re.compile(r"^- \*\*Standing answers\*\*")


def rules_of(text):
    lines = text.splitlines()
    start = next((i for i, l in enumerate(lines) if SECTION_START.match(l)), None)
    if start is None:
        raise SystemExit("no '## 6.' heading")
    rules, cur, ended, blank = [], None, False, False
    bullets = []
    body = lines[start + 1:]
    sec_lines = body
    for idx, l in enumerate(body):
        if l.startswith("## "):
            break
        if cur is not None and not ended and not l.strip():
            nxt = next((x for x in body[idx + 1:] if x.strip()), "")
            if nxt[:1].isspace():
                raise SystemExit("section 6: a blank line inside rule %d, followed by indented text: %r"
                                 % (cur[0], nxt[:80]))
        if l.startswith("- "):
            lead = l[2:].lstrip("*").strip()
            m2 = re.match(r"(.{1,40}?[.:])(?:\*\*|\s|$)", lead)
            bullets.append((m2.group(1) if m2 else lead[:30]).strip())
        m = RULE_START.match(l)
        if ended:
            if m:
                raise SystemExit("section 6: a rule-shaped line after the rules ended: %r" % l[:80])
            continue
        if STANDING.match(l) or (cur is not None and (l.startswith("- ") or (blank and l and not l[0].isspace()))):
            ended = cur is not None
            if ended:
                rules.append(cur)
                cur = None
            continue
        blank = not l.strip()
        if m:
            want = cur[0] + 1 if cur else 1
            if int(m.group(1)) != want:
                raise SystemExit("section 6: expected rule %d, found rule %s: %r"
                                 % (want, m.group(1), l[:80]))
            if cur:
                rules.append(cur)
            cur = [int(m.group(1)), [m.group(2).strip()]]
        elif cur is not None and l.strip():
            if not re.match(r"^ {4,}\S", l):
                raise SystemExit("section 6: a line inside rule %d that is neither a rule start nor an "
                                 "indented continuation: %r" % (cur[0], l[:80]))
            cur[1].append(l.strip())
    if cur:
        rules.append(cur)
    if not rules:
        raise SystemExit("section 6: no numbered rule found (a rule starts with 1 to 3 spaces, "
                         "a number and a full stop)")
    out = []
    for n, parts in rules:
        text = " ".join(p for p in parts if p)
        if CONTROL_RE.search(text):
            raise SystemExit("section 6: rule %d holds a control character" % n)
        m = re.match(r"\*(.+?)\*\s*(.*)$", text)
        if not m:
            raise SystemExit("section 6: rule %d has no *italic title*: %r" % (n, text[:80]))
        title, body = m.group(1).strip(), m.group(2).strip()
        if title.count("`") % 2:
            raise SystemExit("section 6: rule %d's title has an odd number of backticks (cut short?): %r"
                             % (n, title[:80]))
        if n in TITLE_START and not title.startswith(TITLE_START[n]):
            raise SystemExit("section 6: rule %d starts %r, not %r: the numbers moved since the "
                             "proposals were written; update TITLE_START, SUBJECT and TOOL first"
                             % (n, title[:40], TITLE_START[n]))
        out.append((n, title, body))
    # v2 (BREAK-IT-1 C6): every rule-shaped line before the Standing answers must have been parsed as a
    # rule; a rule at column 0 after a blank line, or at a 4-space indent, would otherwise vanish.
    end = next((k for k, l in enumerate(sec_lines) if STANDING.match(l) or l.startswith("## ")), len(sec_lines))
    shaped = [l for l in sec_lines[:end] if RULE_SHAPE_RE.match(l)]
    if len(shaped) != len(out):
        raise SystemExit("section 6: %d lines look like rules but %d were parsed as rules; fix the "
                         "indentation first (first: %r)" % (len(shaped), len(out), shaped[0][:80] if shaped else ""))
    nums = [n for n, _, _ in out]
    if nums != list(range(1, len(nums) + 1)):
        raise SystemExit("section 6's rule numbers are not 1..N without gaps: %s" % nums)
    return out, bullets


def toml_str(s):
    if "'''" not in s:
        return "'''" + s + "'''"
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def main(argv):
    if len(argv) != 4 or not argv[3].isdigit():
        sys.stderr.write(__doc__)
        return 2
    src, dst, expected = argv[1], argv[2], int(argv[3])
    if os.path.exists(dst):
        sys.stderr.write("refusing to overwrite %s\n" % dst)
        return 1
    with open(src, encoding="utf-8", newline="") as fh:
        raw = fh.read()
    if "\r" in raw:
        sys.stderr.write("refusing: %s has carriage returns (CRLF line ends)\n" % src)
        return 1
    rules, bullets = rules_of(raw)
    lines = raw.split("\n")
    span, why = compile_rules.find_rule_list(lines)
    if why:
        sys.stderr.write("refusing: %s\n" % why)
        return 1
    s6, e6 = compile_rules.section6_bounds(lines)[0]
    outside = compile_rules.outside_sha(lines, s6, e6, span[0], span[1])
    if len(rules) != expected:
        sys.stderr.write("found %d rules, expected %d: refusing\n" % (len(rules), expected))
        return 1
    out = ["# Rule registry for HANDOFF.md, section 6. Generated once by build_registry.py;",
           "# from now on edit this file and regenerate the section with compile_rules.py render.",
           "# Subjects and tools are claude-ai's proposals; a tool counts only once verified.",
           "",
           "[meta]",
           'section = "HANDOFF.md section 6"',
           "budget_self_applied = %d" % len(rules),
           'budget_set_by = "Dustin 2026-10-18: one in, one out (store row 20261018-010)"',
           "allowed_bullets = [%s]" % ", ".join(toml_str(b) for b in bullets),
           'outside_sha256 = "%s"' % outside,
           ""]
    for n, title, body in rules:
        out += ["[[rule]]",
                "n = %d" % n,
                "title = %s" % toml_str(title),
                "body = %s" % toml_str(body),
                'subject = "%s"' % SUBJECT.get(n, "unsorted"),
                'status = "active"',
                "merged_into = 0",
                "enforced_by = %s" % toml_str(TOOL.get(n, "")),
                'enforcement = "%s"' % ("proposed" if n in TOOL else ""),
                'verified_by = ""',
                'last_caught = ""',
                ""]
    with open(dst, "x", encoding="utf-8") as fh:
        fh.write("\n".join(out))
    print("wrote %s: %d rules, %d with a proposed tool" % (dst, len(rules), len([n for n, _, _ in rules if n in TOOL])))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
