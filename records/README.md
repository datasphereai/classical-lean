# records/ — the concurrency protocol

## The failure this directory exists to prevent

On 2026-09-07/08 two sessions worked this tree at the same time. Neither did anything wrong
individually. Both reached the same correct local decision — *"`PROVENANCE.md` is being edited by
the other session, so I will not touch it mid-write"* — and the collective result was that two
shipped modules, `Simplex/Symmetry.lean` (`b525cef`) and `Simplex/Temperature.lean` (`ed5b176`),
landed with **no round entry at all**. Nothing detected the gap. It was found by hand a day later,
and only because the two transcripts were read side by side.

Three separate things went wrong, and each gets a mechanism below.

| What went wrong | Mechanism |
|---|---|
| One shared records file is a lock that two sessions contend for | `records/rounds/` — one fragment per round, per session; no two sessions write the same path |
| A missing round entry was silent | `tools/check_records.py` — gate 6; every module under `ClassicalLean/` must be named in the records |
| Orders G-2, G-3 and G-4 existed only in chat transcripts | `records/orders/` — an order is a file before it is work |

## Rule 1 — a round writes a fragment, not `PROVENANCE.md`

Write `records/rounds/<UTC timestamp>__<round label>.md`. Timestamps make collision impossible
between concurrent sessions. Do **not** edit `PROVENANCE.md` for a new round; it is now an archive
of rounds 1–14 plus 10a, and the fragments carry everything after that.

A fragment must name, in its body:

* every `ClassicalLean/…` module path it added or changed, spelled in full (gate 6 greps for these);
* the commit hash, added in a follow-up edit once the commit exists — never predicted;
* its own per-module theorem-constant count, measured with `env.getModuleFor?` under the axiom
  gate's `.thmInfo` predicate, not with a raw-name census (see `HANDOFF.md` §2 for why);
* whether the whole-library gate numbers it quotes were taken on a **clean** tree or a **mixed**
  one. A mixed-tree aggregate is context, never evidence for the commit.

## Rule 2 — an order is a file before it is work

Write `records/orders/<UTC timestamp>__<source>__order-<id>-<slug>.md` before executing it, with
**Goal / Scope / Done-means** headings. An order given only in chat is not an order; if a session
is handed one inline, its first act is to write the file.

`records/orders/INDEX.md` lists every order and its state. A row records the state when it was written, and the next order's records commit appends the push of the order before it to that order's INDEX row and CLAIMS row (dated 2026-10-16, order LEAN-31).

## Rule 3 — claim before you write

Append a line to `records/CLAIMS.md` naming the session, the modules it intends to touch, and the
records path it will write. Read the file first. If another live claim names a module you were
about to take, take something else — do not negotiate through the tree.

A claim is advisory, not a lock. It exists so that the *second* session knows the first exists,
which is the fact both sessions lacked.

## Rule 4 — the records debt is the landing commit's, not the next session's

Both commits in the incident deferred their round entry to "whoever lands second". Nobody was
appointed second. If a records file is genuinely contended, write the fragment under
`records/rounds/` — which is never contended — and say so. Deferring is no longer an available
move.

## Known debt, carried deliberately

`ClassicalLean/Simplex/Hessian.lean` has no round entry. Measured: `git log --oneline --` on that
path returns only `4820f72 Initial commit: classical-lean, rounds 1 and 2`, so it is inherited
salvage rather than round work, and `RETIRED.md` records it under *"Not ported from the source"*.
It is listed in `tools/check_records.py` as a named exemption rather than papered over with a
fabricated round entry. Anyone who writes its provenance should delete it from that list.

**Dated 2026-10-07 (order LEAN-5):** `PROVENANCE.md` (the archive of rounds 1–14 and 10a) and
`RETIRED.md` (the record of what was retired) are removed from the tree, and retired words quoted in
the records are replaced by the placeholders `[surname]`, `[retired term]` and `[retired name]`; a
quoted line or regex in an older record is therefore a paraphrase. The full earlier history,
including both files, is kept outside the library in a git bundle on DSMain. Gate 6 reads
`PROVENANCE.md` only if it exists; no module was named only there.
