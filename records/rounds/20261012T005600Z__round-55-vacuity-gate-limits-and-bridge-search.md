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
