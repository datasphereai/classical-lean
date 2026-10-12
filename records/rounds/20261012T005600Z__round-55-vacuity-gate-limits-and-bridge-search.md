# Round 55 — the vacuity gate's open limits, and the bridge search as a tool (order VACUITY-2)

Session: Claude Code `session_011EbLXaTFXVhmDqos8VbGfe` on DSMain, as dustin, executing order
`VACUITY-2` (`records/orders/20261012T005500Z__claude-ai__order-vacuity2-gate-limits-and-bridge-search.md`), items 72 to 78 of the plan
`/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library-2.md` (sha256
6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `vacuity-2`, made from `origin/master` =
`d2cba27` (equal to `git ls-remote github master`). Lean and Mathlib v4.34.0. Nothing pushed.
Evidence: `~/lean/vacuity2-checks/` (outside the repository), `evidence.log` (time, label, rc,
prediction, command per run).

First part written before any tool or gate file changed; completed after the work, below.

**No module is added or changed in this round.** No file under `ClassicalLean/` changes, and
`ClassicalLean.lean` does not change. The work is in `tools/` (the vacuity gate, its tests,
its runner, its two reviewed lists, and the new `tools/bridge_search.py`) and in the new folder
`records/bridges/`.

## Standing rule 1: banned vocabulary (decision A of 2026-10-11, from VACUITY-2 on)

`tools/banned_vocab_scan.py` reads the patterns in Dustin's own file
`~/.config/classical-lean/banned-terms`. That file is Dustin's: no session edits it, and no
record, lane file or commit copies its patterns. If a batch needs a banned term for its
mathematics, the session reports the hit (file, line, and the term the mathematics needs) and
stops. Dustin narrows that one pattern in his own file, and the exception is recorded in that
batch's records.

## Standing rule 2: the bridge search (decision A of 2026-10-11, from VACUITY-2 on)

A *bridge* is a theorem whose proof must use two library modules that do not import each other,
through an object they share. `tools/bridge_search.py` lists the candidates. Every order from
VACUITY-2 on, at its end:

* re-runs `python3 -I tools/bridge_search.py --diff <baseline>` against the baseline the last
  report names (the current one: `records/bridges/VACUITY-1/`, made at `d2cba27`), under the
  memory cap `systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0`; exit 1 means
  "candidates to review", not a failed gate;
* checks each new import-unrelated pair by hand for a theorem whose proof needs both sides;
  import-related pairs and shape candidates are listed in the report, not reviewed;
* gives a real bridge an item number from 154 on, ranked after item 153, with the columns of
  section 7's table of MATH-PLAN-library-2.md, its cost, its "Shared object:" line and its own
  Mathlib grep;
* puts it in the lane file MATH-PLAN-library-2-bridges.md the first time, then -bridges-2.md and
  on, each a whole new file carrying all earlier rows, never an overwrite; every later order's
  read list names the newest one;
* never puts a found bridge into the batch that found it; the cut is re-drawn only at a batch
  boundary, and only if a new bridge is load-bearing for a scheduled row;
* when modules were added, commits a new baseline `records/bridges/<ORDER>/` and names it in
  the report; every report names its current baseline whether or not it changed.

The cold-reviewed plan file itself is not edited.

## Completed after the work

Items 72 to 78 of MATH-PLAN-library-2 are done, with one ruling during the order (Dustin,
2026-10-11, about 22:00 EDT): cold review r2's finding 3 ("glued assumptions") fixed here as case 5
of the fixed test, not listed as a limit, followed by a second cold review (r3). No module was
added or changed; `git diff d2cba27 -- ClassicalLean ClassicalLean.lean` is empty.

Commits on `vacuity-2` (from `d2cba27`; nothing pushed):

* `43145cb` records before the work (this fragment's first part).
* `156b69c` `tools/bridge_search.py` and the baseline `records/bridges/VACUITY-1/`.
* `9afa56b` tests for items 72 to 77, measured under the gate at `d2cba27` first.
* `e700691` items 72 and 74; `1f584d0` the HELPER entry for
  `ClassicalLean.Simplex.orderedSimplex_subset_closedSimplex` (the one library flag of item 72).
* `3889b26` item 73; `091995c` item 75; `541bd7c` item 76.
* `768efcf` item 77 (rule 5); `2c4b9b2` its fix (rule 5 read the negated conclusion as a
  hypothesis and failed four real theorems).
* `c81760a` cold review r2 applied or stated (item 78).
* `cdad034` and `14b7ca4` the ruling: tests first, then case 5.
* `d2503ba` cold review r3 applied or stated (its BLOCKER: no depth bound in case 5).

Whole-library numbers, all on the **clean** tree at `d2503ba`: build 4166 jobs, 0 warnings;
AxiomGate PASS 3158; VacuityGate PASS, 1 reviewed helper, 0 VACUOUS-PENDING, rule 5 ran out on 0
theorems (3:19.71, 5044008 KB; before the order 2:47.48, 4977060 KB); check_sorry PASS 120;
banned_vocab_scan PASS 120 files, 0 hits; check_records PASS 120. Gate 7 at `d2503ba`: ALL PASSED,
120 modules 0 failed, 90482 declarations no errors, three standard axioms, 3158, planted fault
named. Per-module theorem counts: unchanged, since no module changed.

The plan's checks after: 224 of 232; the eight misses equal the predicted multiset
(`setup.worktree`, `gate.maxUnfolds`, `gate.macro`, `gate.helper`, `gate.metacheck`,
`gate.test.lim_and_hyp`, `gate.test.lim_false`, `gate.list`). The bridge search's end diff against
`records/bridges/VACUITY-1/`: rc 0, nothing new or gone. **Current baseline:
`records/bridges/VACUITY-1/`.** Report: lane `VACUITY-2-report.md`.
