#!/usr/bin/env python3
"""Gate 6 — every shipped module is named somewhere in the records.

    python3 tools/check_records.py

Exit 0 when every `.lean` module under `ClassicalLean/` is named, by its path relative to
`ClassicalLean/` or by its bare filename, in at least one records file; nonzero otherwise,
naming each module that is not.

Records files searched, in this order:

    PROVENANCE.md          the archive of rounds 1-14 and 10a, read if present (removed from the
                           tree on 2026-10-07, order LEAN-5; no module depended on it alone)
    records/rounds/*.md    one fragment per round, per session (the current mechanism)
    records/orders/*.md    orders, which name the modules they commission

## Why this gate exists

On 2026-09-07/08 two sessions committed into this tree concurrently. Each declined to edit
`PROVENANCE.md` while the other held it -- individually the right call -- and
`Simplex/Symmetry.lean` (b525cef) and `Simplex/Temperature.lean` (ed5b176) shipped with no round
entry. The five existing gates all passed: they check axioms, vacuity, holes and vocabulary, and
none of them can see a records gap. This one can. See `records/README.md`.

## Why coverage of the tree, and not an audit of `git log`

A history audit cannot be run by the commit that needs it: a commit cannot cite its own hash. A
tree audit can, because module paths are known before the commit is made. So this gate is
checkable at the moment of writing, which is the only moment at which anyone will act on it.

## The exemption list

`EXEMPT` names modules that are inherited rather than round work. Each entry carries the evidence
for the exemption. Adding to it is a deliberate, reviewable act; the list is short on purpose.
"""

import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "ClassicalLean"

# Module path relative to ClassicalLean/ -> the evidence for exempting it.
EXEMPT = {
    "Simplex/Hessian.lean": (
        "inherited salvage, not round work: `git log --oneline -- "
        "ClassicalLean/Simplex/Hessian.lean` returns only 4820f72 "
        '"Initial commit: classical-lean, rounds 1 and 2", and the retirement record (removed '
        '2026-10-07) listed it as not ported. Delete this entry when its provenance is written.'
    ),
}


def records_text() -> tuple[str, list[str]]:
    """Concatenate every records file. Returns (text, list of files read)."""
    paths: list[pathlib.Path] = []
    prov = ROOT / "PROVENANCE.md"
    if prov.exists():
        paths.append(prov)
    for sub in ("records/rounds", "records/orders"):
        d = ROOT / sub
        if d.is_dir():
            paths.extend(sorted(p for p in d.glob("*.md")))
    chunks = []
    for p in paths:
        try:
            chunks.append(p.read_text(encoding="utf-8"))
        except OSError as exc:  # surface it; never swallow
            print(f"check_records ERROR — cannot read {p}: {exc}", file=sys.stderr)
            raise SystemExit(2)
    return "\n".join(chunks), [str(p.relative_to(ROOT)) for p in paths]


def main() -> int:
    if not SRC.is_dir():
        print(f"check_records ERROR — no such directory: {SRC}", file=sys.stderr)
        return 2

    modules = sorted(p.relative_to(SRC).as_posix() for p in SRC.rglob("*.lean"))
    if not modules:
        print(f"check_records ERROR — no .lean modules under {SRC}", file=sys.stderr)
        return 2

    text, files = records_text()
    if not files:
        print("check_records ERROR — no records files found", file=sys.stderr)
        return 2

    missing: list[str] = []
    exempted: list[str] = []
    for rel in modules:
        if rel in EXEMPT:
            exempted.append(rel)
            continue
        base = rel.rsplit("/", 1)[-1]
        # Match the full relative path, or the bare filename as a whole word.
        if rel in text or re.search(r"(?<![\w/])" + re.escape(base), text):
            continue
        missing.append(rel)

    # A stale exemption is also a failure: it means the list outlived the file.
    stale = sorted(k for k in EXEMPT if k not in modules)

    if missing or stale:
        print(
            f"check_records FAIL — {len(modules)} module(s) under ClassicalLean, "
            f"{len(missing)} with no records entry, {len(stale)} stale exemption(s)."
        )
        for rel in missing:
            print(f"  UNRECORDED  ClassicalLean/{rel}")
        for rel in stale:
            print(f"  STALE EXEMPTION  {rel} — no longer in the tree; remove it from EXEMPT")
        if missing:
            print(
                "\nWrite a fragment under records/rounds/ naming each module in full. "
                "See records/README.md."
            )
        return 1

    print(
        f"check_records PASS — {len(modules)} module(s) under ClassicalLean, "
        f"every one named in the records ({len(files)} file(s) searched), "
        f"{len(exempted)} named exemption(s)."
    )
    for rel in exempted:
        print(f"  exempt: {rel}")
    return 0


if __name__ == "__main__":
    try:
        subprocess.run(["git", "-C", str(ROOT), "rev-parse", "--git-dir"],
                       check=True, capture_output=True)
    except (OSError, subprocess.CalledProcessError):
        print("check_records NOTE — not a git repository; running the tree check anyway.")
    raise SystemExit(main())
