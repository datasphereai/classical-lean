#!/usr/bin/env python3
"""Vocabulary gate.

The mathematics in this library was harvested out of an earlier research corpus whose framing has
been retired. The theorems survived; the vocabulary did not. This checker enforces that separation
mechanically, so a retired word cannot drift back in through a docstring, a section header, or a
copied comment. It scans **comments and docstrings too**: a theorem named cleanly but documented
in retired vocabulary is exactly the failure this catches, and a Lean build never will.

## The term list lives outside the repository

Since 2026-10-07 (order LEAN-5) the terms are not in this file or anywhere in the repository. They
are read from

    ~/.config/classical-lean/banned-terms

a JSON object with three keys:

  retired      case-insensitive regexes for retired project nouns and framing language
  provenance   case-insensitive regexes for status or manuscript chatter
  exceptions   [term, context] pairs: a hit of `term` is forgiven only when it lies inside a match
               of `context` on the same line (for example the two licence-header lines)

If the file is missing or malformed the scanner stops with exit code 2 and one line saying so; it
never passes without its list. Keep the file at mode 0600.

## Scope — read this before reading a PASS

This gate is scoped to `ClassicalLean/`, the shipped library, to the library's root file
`ClassicalLean.lean` beside it, and to `.lean` files. `.lake/` (the vendored toolchain and Mathlib)
is never scanned. So a PASS here means "the shipped Lean sources are clean", never "the repository
is clean". Say which one you mean when quoting it.

Exit 0 clean, 1 on any hit, 2 on a usage error or a missing or malformed term list.

Usage:  python3 tools/banned_vocab_scan.py [root]     (default: ClassicalLean; the
                                                      file <root>.lean beside it too)
        python3 tools/banned_vocab_scan.py --list     print the terms and exit
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

import json

TERMS_FILE = Path.home() / ".config" / "classical-lean" / "banned-terms"

# Vendored or generated trees: never our source, so never in scope. Without this,
# pointing the scanner at the repository root walks the whole of Mathlib.
SKIP_DIRS = {".lake", ".git", "__pycache__", "node_modules", ".venv"}


def load_terms() -> tuple[list[str], list[str], list[tuple[str, str]]]:
    """Read (retired, provenance, exceptions) from TERMS_FILE; exit 2 with one line if it is
    missing or malformed, so the gate can never pass without its list."""
    try:
        data = json.loads(TERMS_FILE.read_text(encoding="utf-8"))
        retired = [str(t) for t in data["retired"]]
        provenance = [str(t) for t in data["provenance"]]
        exceptions = [(str(t), str(c)) for t, c in data["exceptions"]]
    except FileNotFoundError:
        print(f"banned_vocab_scan ERROR — term list missing: {TERMS_FILE} "
              "(it is kept outside the repository; see the docstring)", file=sys.stderr)
        raise SystemExit(2)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(f"banned_vocab_scan ERROR — term list unreadable: {TERMS_FILE}: {exc}",
              file=sys.stderr)
        raise SystemExit(2)
    if not retired:
        print(f"banned_vocab_scan ERROR — term list has no retired terms: {TERMS_FILE}",
              file=sys.stderr)
        raise SystemExit(2)
    return retired, provenance, exceptions


def compile_terms(terms: list[str]) -> list[tuple[str, re.Pattern[str]]]:
    return [(t, re.compile(t, re.IGNORECASE)) for t in terms]


def main(argv: list[str]) -> int:
    RETIRED, PROVENANCE, EXCEPTIONS = load_terms()
    if len(argv) > 1 and argv[1] == "--list":
        print("RETIRED:")
        for t in RETIRED:
            print(f"  {t}")
        print("PROVENANCE:")
        for t in PROVENANCE:
            print(f"  {t}")
        return 0

    root = Path(argv[1]) if len(argv) > 1 else Path("ClassicalLean")
    if not root.exists():
        print(f"banned_vocab_scan: no such directory: {root}", file=sys.stderr)
        return 2

    files = sorted(
        p for p in root.rglob("*.lean")
        if not any(part in SKIP_DIRS for part in p.parts)
    )
    # The library's root file sits beside its directory (`ClassicalLean.lean` next to
    # `ClassicalLean/`), outside the walk above; scan it too.
    beside = root.parent / (root.name + ".lean") if root.name else None
    extra = [beside] if beside is not None and root.is_dir() and beside.is_file() else []
    if not files:
        print(f"banned_vocab_scan: no .lean files under {root}", file=sys.stderr)
        return 2
    files = extra + files

    retired = compile_terms(RETIRED)
    provenance = compile_terms(PROVENANCE)
    exceptions = [(t, re.compile(c, re.I)) for t, c in EXCEPTIONS]

    hits = 0
    for path in files:
        for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            for kind, terms in (("RETIRED", retired), ("PROVENANCE", provenance)):
                for term, pat in terms:
                    for m in pat.finditer(line):  # every match, not only the first
                        if any(t == term and any(c.start() <= m.start() and m.end() <= c.end()
                                                 for c in cp.finditer(line))
                               for t, cp in exceptions):
                            continue  # this hit lies inside its own exception's context
                        print(f"{path}:{lineno}: {kind} /{term}/: {line.strip()}")
                        hits += 1

    if hits:
        print(
            f"\nbanned_vocab_scan FAIL — {hits} hit(s) across {len(files)} file(s).\n"
            "A RETIRED hit means a project noun survived the port: rewrite the "
            "declaration or docstring in ordinary mathematical language.\n"
            "A PROVENANCE hit means status or manuscript chatter is in a source "
            "file: move it to the records under records/, which is where that belongs.",
            file=sys.stderr,
        )
        return 1

    where = f"{root}" + "".join(f" + {p}" for p in extra)
    print(f"banned_vocab_scan PASS — {len(files) - len(extra)} file(s) under {where}, "
          f"0 hits across {len(RETIRED)} retired and {len(PROVENANCE)} provenance terms.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
