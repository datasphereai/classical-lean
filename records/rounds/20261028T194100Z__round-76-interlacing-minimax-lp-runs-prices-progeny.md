# Round 76 — interlacing, minimax by LP, runs, prices by LP, progeny series (order LEAN-37)

Session: Claude Code `session_01HgueTbGDPjToeXbmtvR4Wd` on DSMain, as dustin, executing order
`LEAN-37` (`records/orders/20261027T234445Z__claude-ai__order-lean37-interlacing-minimax-lp-runs-prices-progeny.md`,
written by claude-ai, copied verbatim; lane `lean/LEAN-37/order.md`, sha256
`06c7c140a70d437e41863acfe4e84685be488d8ee23bce5e24e5680d94b09123`), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `lean-37`, made from `67d05bf` (VACUITY-5's last
commit, equal to `git ls-remote origin master` and `git ls-remote github master`, both read
2026-10-28 15:37 EDT). Nothing pushed. Lighter procedure (store row 20261026-063). Scratch files:
`~/lean/lean37-checks/` (outside the repository). The launch variable
`CLAUDE_CODE_DISABLE_AUTO_MEMORY` printed `1` (2026-10-28 15:37 EDT).

The order's copy: its sha256 read through the connector (`ds_hash`, equal to the value above), then
the file copied byte for byte into `records/orders/` and its sha256 checked equal. The two type-dump
files (`TypeDumpPI.lean`, `g8_typediff.py`) were read through the connector and written from its
replies, each sha256 checked against the order's value (`~/lean/lean37-checks/step2-scripts.sha256`).

Before the work, on the clean tree at `67d05bf`: `lake build` completed (4193 jobs,
`~/lean/lean37-checks/build-before.out`); the type dump `td-before.jsonl` checked
`CHECK records=4163 thm=3666 def=497 elided=0 missing_fields=0` (`~/lean/lean37-checks/td-before.check`).

First part written before the work; completed after it, below.

## Files this round changes

Module files (no module is added):

* `ClassicalLean/Algebra/MinMax.lean` (item 123): `eigenvalues_compression_le`,
  `le_eigenvalues_compression`, two witnesses.
* `ClassicalLean/Analysis/FiniteGame.lean` (item 141): `minimax_eq_of_lp`; import line
  `ClassicalLean.Analysis.LinearProgram`.
* `ClassicalLean/Combinatorics/ArbitrageCycle.lean` (item 145): `hasPrices_iff_of_lp` and its
  private helpers, one witness; import line `ClassicalLean.Analysis.LinearProgram`.
* `ClassicalLean/Probability/LongestRun.lean` (item 143): `measureReal_no_run_two_eq`,
  `measureReal_no_run_three_eq` and their private helpers, two witnesses; import line
  `ClassicalLean.NumberTheory.Tribonacci`.
* `ClassicalLean/Probability/Extinction.lean` (item 149): `progeny_eval_one_eq_extinctionChance`,
  `existsUnique_progeny`, `coeff_progeny_catalan` and their private helpers, two witnesses; import
  lines `ClassicalLean.Combinatorics.AlgebraicGeneratingFunction` and
  `Mathlib.RingTheory.PowerSeries.Trunc`.

Also changed: `records/CLAIMS.md` and `records/orders/INDEX.md` (this order's rows appended at the
bottom, and VACUITY-5's push recorded in VACUITY-5's two rows), this fragment, the order's copy,
`HANDOFF.md` section 1 (one dated paragraph), `ROADMAP.md` (section 1.31),
`tools/vacuity_reviewed.txt` only if a helper is listed, and `records/bridges/LEAN-37/`.

## Order VACUITY-5's push

By records/README.md rule 2, this round's first commit inserts into VACUITY-5's INDEX row (right
after `type dump removed 0, added 0, changed 0, proof-only 0; drift PASS`, before its commits cell)
and its CLAIMS row (before the final ` |`) the text
`; pushed by Dustin: master 67d05bf on both remotes, CI run 40559114678 green`, as the order gives
it, by the script `~/lean/lean37-checks/pushnote.py`, which asserts one matching row and one anchor
in each before inserting. Re-measured before the commit: `git ls-remote origin master` and
`git ls-remote github master` both gave `67d05bfbd0efa80f0de679813b54500ae8c69122`
(`~/lean/lean37-checks/step1-check.out`). The CI run's number and colour are the order's (store row
20261027-017), not measured here.
