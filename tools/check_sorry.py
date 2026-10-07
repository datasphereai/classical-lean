#!/usr/bin/env python3
"""Static check on proof hygiene across the shipped library.

Complements the two Lean gates rather than duplicating them:

  tools/AxiomGate.lean    what the KERNEL says a theorem rests on
  tools/VacuityGate.lean  whether a statement asserts anything
  tools/check_sorry.py    what the SOURCE TEXT contains  <- this file

The Lean gates only see declarations that actually elaborate and get imported by
the aggregator. This one sees every `.lean` file on disk, including a module
someone forgot to wire in, so a hole cannot hide by being unimported.

Policy (from the library layout note, §5):

  * `sorry` / `admit`            banned in ClassicalLean/, allowed in Open/
                                 (where an honest open problem is the point)
  * `native_decide`             banned in ClassicalLean/, allowed in Examples/
                                 and in Open/ verification blocks
  * `axiom` declarations        banned everywhere in ClassicalLean/ except with
                                 an explicit `-- AXIOM-OK: <reason>` comment on
                                 the preceding line, so every axiom is a record

Scope: `ClassicalLean/` and its subdirectories. `.lake/` (vendored Mathlib) and
`tools/` (this gate and its siblings) are skipped — see SKIP_DIRS for why, including
the one real limitation behind it. A PASS means the shipped library is clean, not the
repository.

The permitted-directory test matches a PATH COMPONENT (`Open`, `Examples`) of the
file's own resolved path, so the verdict does not depend on which directory the
scanner was pointed at.

Exit 0 clean, 1 on any violation, 2 on a usage error.

Usage:  python3 tools/check_sorry.py [root]        (default: ClassicalLean)
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

# `sorry` and `admit` as whole tokens, not as substrings of an identifier and not
# inside a word like "sorryAx" appearing in a docstring about the gate.
PATTERNS = {
    "sorry": re.compile(r"(?<![A-Za-z0-9_.])sorry(?![A-Za-z0-9_])"),
    "admit": re.compile(r"(?<![A-Za-z0-9_.])admit(?![A-Za-z0-9_])"),
    "native_decide": re.compile(r"(?<![A-Za-z0-9_.])native_decide(?![A-Za-z0-9_])"),
    "axiom": re.compile(r"^\s*axiom\s+[A-Za-z_]"),
}

# Directories in which a pattern is permitted, matched as a PATH COMPONENT of the
# file's own path rather than as a prefix of its path relative to the scan root.
#
# The root-relative version of this was a bug: scanning `ClassicalLean` exempted
# `Open/Example.lean`, but scanning `ClassicalLean/Open` did not, because the
# relative path was then just `Example.lean`. The same file passed or failed
# depending on where the scanner was pointed, which makes the gate's answer depend on
# how it is invoked — exactly the property a gate must not have.
EXEMPT = {
    "sorry": ("Open",),
    "admit": (),
    "native_decide": ("Examples", "Open"),
    "axiom": (),
}

AXIOM_OK = re.compile(r"--\s*AXIOM-OK:")

# Vendored or generated trees: never our source, so never in scope. Without this,
# pointing the scanner at the repository root walks the whole of Mathlib, which
# contains `sorry` in its own test and deprecation material.
SKIP_DIRS = {".lake", ".git", "__pycache__", "node_modules", ".venv", "tools"}

# Two notes on that `tools` entry, because a skipped directory is a hole unless the
# reason is written down.
#
# 1. `tools/` is gate infrastructure, not shipped mathematics. The argument for scanning
#    text rather than the elaborated environment — that a module someone forgot to wire
#    into the aggregator could hide a hole — applies to `ClassicalLean/`, not here.
# 2. It is also a genuine limitation of this checker. `tools/AxiomGate.lean` and
#    `tools/VacuityGate.lean` contain the literal words `native_decide` and `sorry`
#    inside Lean STRING LITERALS, in the error messages they print when they catch
#    exactly those things. This scanner strips `--` comments and `/- -/` blocks but does
#    not parse string literals, so it reported both as violations. Rather than pretend
#    the limitation does not exist, it is stated here: if a `.lean` file outside
#    `ClassicalLean/` ever needs scanning, teach this function about string literals
#    first.


def strip_line_comment(line: str) -> str:
    """Drop a trailing `--` comment. Crude but adequate: it does not understand
    `--` inside a string literal, which the library does not contain. Block
    comments `/- -/` are handled by the caller."""
    idx = line.find("--")
    return line if idx < 0 else line[:idx]


def is_exempt(path: Path, name: str) -> bool:
    """Is `name` permitted for this file, by virtue of one of its path components?"""
    parts = set(path.resolve().parts)
    return any(d in parts for d in EXEMPT[name])


def scan_file(path: Path, rel: str) -> list[tuple[int, str, str]]:
    hits: list[tuple[int, str, str]] = []
    in_block = False
    prev_raw = ""
    for lineno, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        line = raw
        # Block comments and docstrings: text inside them is prose, not proof.
        if in_block:
            if "-/" in line:
                in_block = False
                line = line.split("-/", 1)[1]
            else:
                prev_raw = raw
                continue
        while "/-" in line:
            before, _, after = line.partition("/-")
            if "-/" in after:
                line = before + after.split("-/", 1)[1]
            else:
                line = before
                in_block = True
                break
        line = strip_line_comment(line)
        if not line.strip():
            prev_raw = raw
            continue
        for name, pat in PATTERNS.items():
            if not pat.search(line):
                continue
            if is_exempt(path, name):
                continue
            if name == "axiom" and AXIOM_OK.search(prev_raw):
                continue
            hits.append((lineno, name, raw.strip()))
        prev_raw = raw
    return hits


def main(argv: list[str]) -> int:
    root = Path(argv[1]) if len(argv) > 1 else Path("ClassicalLean")
    if not root.exists():
        print(f"check_sorry: no such directory: {root}", file=sys.stderr)
        return 2

    files = sorted(
        p for p in root.rglob("*.lean")
        if not any(part in SKIP_DIRS for part in p.parts)
    )
    if not files:
        print(f"check_sorry: no .lean files under {root}", file=sys.stderr)
        return 2

    violations = 0
    for path in files:
        rel = str(path.relative_to(root))
        for lineno, name, text in scan_file(path, rel):
            print(f"{path}:{lineno}: {name}: {text}")
            violations += 1

    if violations:
        print(
            f"\ncheck_sorry FAIL — {violations} violation(s) across {len(files)} file(s).\n"
            "`sorry`/`admit` are allowed only under Open/; `native_decide` only under "
            "Examples/ and Open/; an `axiom` needs an `-- AXIOM-OK: <reason>` line above it.",
            file=sys.stderr,
        )
        return 1

    print(f"check_sorry PASS — {len(files)} file(s) under {root}, no holes and no "
          "compiler-trusted proofs outside their permitted directories.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
