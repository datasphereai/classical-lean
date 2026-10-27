# Round 75 — witnesses for YuleWalker's Yule–Walker theorems (order VACUITY-5)

Session: Claude Code `session_01HgueTaMGxsMGo5HLwpJJjR` on DSMain, as dustin, executing order
`VACUITY-5` (`records/orders/20261027T052000Z__claude-ai__order-vacuity5-yule-walker-witnesses.md`,
written by claude-ai, copied verbatim; lane `lean/VACUITY-5/order.md`, sha256
`02a01495e1482cfaedeeeec91cc7191a0f38b3f9b41961ee41c7dfccde9c44d2`), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `vacuity-5`, made from `fb8beee` (LEAN-36's last
commit, equal to `git ls-remote origin master` and `git ls-remote github master`, both read
2026-10-27 12:05 EDT). Lean and Mathlib v4.34.0. Nothing pushed. The order is the first written to
the lighter procedure (store row 20261026-063): Lean's own check, the machine gates, one cold review
and claude-ai's push review; no plan-approval stop. Scratch files: `~/lean/vacuity5-checks/`
(outside the repository). The launch variable `CLAUDE_CODE_DISABLE_AUTO_MEMORY` printed `1`
(2026-10-27 01:21 EDT); the session then waited out the night window and resumed at 12:05 EDT, when
step 1's checks were run again and matched.

The order's copy: its sha256 read through the connector (`ds_hash`, equal to the value above), then
the file copied byte for byte into `records/orders/` and its sha256 checked equal. The two type-dump
files (`TypeDumpPI.lean`, `g8_typediff.py`) were read through the connector and written from its
replies, each sha256 checked against the order's value.

Before the work, on the clean tree at `fb8beee`: `lake build` completed (4193 jobs); the type dump
`td-before.jsonl` checked `CHECK records=4163 thm=3666 def=497 elided=0 missing_fields=0`.

First part written before the work; completed after it, below.

## Files this round changes

Module files (no module is added):

* `ClassicalLean/Probability/YuleWalker.lean`: three `example` blocks after its last line (one each
  for `covariance_eq_sum`, `isSolution_autocovariance` and `exists_poly_mk_autocovariance_eq`), the
  Mathlib import lines the blocks need among the three the order names, and the witness note of its
  module docstring. No declaration changed.

Also changed: `records/CLAIMS.md` and `records/orders/INDEX.md` (this order's rows appended at the
bottom, and LEAN-36's push recorded in LEAN-36's two rows), this fragment, the order's copy, and
`HANDOFF.md` sections 1 and 4 (one dated paragraph each). Nothing under `tools/`, `.github/` or
`records/rules.toml`; no other `.lean` file.

## Order LEAN-36's push

By records/README.md rule 2, this round's first commit inserts into LEAN-36's INDEX row (right after
`rule 8's reading of five reviews put to claude-ai (round 74)`, before its commits cell) and its
CLAIMS row (before the final ` |`) the text
`; pushed by Dustin: master fb8beee on both remotes, CI run 40443324601 green`, as the order gives
it, by the script `~/lean/vacuity5-checks/pushnote.py`, which asserts one matching row and one
anchor in each before inserting. Re-measured before the commit: `git ls-remote origin master` and
`git ls-remote github master` both gave `fb8beee37b74ea369f553c41a5b1279d1cf2490b`. The CI run's
number and colour are the order's (store row 20261027-003), not measured here.
