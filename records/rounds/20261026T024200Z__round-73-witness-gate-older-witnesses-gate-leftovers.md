# Round 73 — the witness gate, the older witnesses brought to rule 2, and the gate leftovers (order VACUITY-4)

Session: Claude Code `session_01CaiSGfxRa9So88se5LzGkG` on DSMain, as dustin, executing order
`VACUITY-4` (`records/orders/20261026T024100Z__claude-ai__order-vacuity4-witness-gate-older-witnesses-gate-leftovers.md`,
written by claude-ai, copied verbatim; lane `lean/VACUITY-4/order.md`, sha256
`68996aadffdc8660aa569344d1769453d4b035e49216a2fe8509d3b6936fd1b1`), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `vacuity-4`, made from `origin/master` = `ac62f50`
(LEAN-35's last commit, equal to `git ls-remote github master`). Lean and Mathlib v4.34.0. Nothing
pushed. Evidence: `~/lean/vacuity4-checks/` (outside the repository), `evidence.log` (UTC time,
label, rc, prediction, command per run; `COMMIT <hash>` marker lines). Plan: lane
`lean/VACUITY-4/plan-r2.md` (sha256 `90fde810a569bd846bd1a90b81fb243585a59968daca6e1187c493aeb0cea1d3`;
it replaces `lean/VACUITY-4/plan.md`, sha256
`991bfd960eb8c45b03460b66cd48733c8909f3838cd0bcb44c445c9d5fc18d39`), approved by Dustin on
2026-10-25 (EDT evening) with claude-ai's five rulings (lane `lean/VACUITY-4/ruling-1.md`, sha256
`accee2804ff50f7e3c4ad4318fb6ad9ca8cb37a6ae01b70f0db49b9d83fab173`); both saved in
`~/lean/vacuity4-checks/pre/` (label `approval`); the first line of `evidence.log` is at
2026-10-26T02:38:01Z.

The rulings, in short: (1) the plan's lane reads outside the connector are accepted, and every later
lane read and copy goes through the connector; (2) the Scope widens for exactly the pointer sentences
plan r2 lists (and any a Job 3 witness would make false the same way), each pointing at a witness by
its theorem, never by its place; (3) MaximalInequality's two re-witnesses at one step (`n = 1`),
after the two theorems' statements are probed; (4) the gate compares its docstring reading with
Lean's (`DOC-MISMATCH`), and a fixture compares the two on each layout before review (a); (5) the
rest of the plan stands.

First part written before the work; completed after it, below.

## Files this round changes

Module files (no module is added; only `example` blocks, their docstrings and `open … in` lines,
and the sentences of ruling 2):

* `ClassicalLean/Order/Superadditive.lean` (the typed claim at line 116 replaced by five witnesses);
* `ClassicalLean/Geometry/Spectral3x3.lean` (the typed claim at line 175);
* `ClassicalLean/Analysis/ConvexConjugate.lean` (the typed claim at line 126);
* `ClassicalLean/Statistics/GeneralizedLeastSquares.lean` (the typed claim at line 261);
* `ClassicalLean/Algebra/Kantorovich.lean` (the typed claims at lines 216 and 225);
* `ClassicalLean/Algebra/MinMax.lean` (the typed claims at lines 427 and 434; the witness-form block
  at line 443 moved after the module's last line);
* `ClassicalLean/InformationTheory/CompressionTest.lean` (the typed claim at line 462);
* `ClassicalLean/Probability/LongestRun.lean` (the typed claim at line 268 removed; its theorem has a
  witness; ruling 2's sentences);
* `ClassicalLean/Probability/EffectiveSampleSize.lean` (the typed claims at lines 583 and 595;
  ruling 2's sentences);
* `ClassicalLean/Probability/GamblersRuin.lean` (the typed claim at line 1046; ruling 2's
  sentences);
* `ClassicalLean/Probability/MaximalInequality.lean` (the witnesses at lines 697 and 736 re-witnessed
  under rule 3's case of the moving process).

Listed, not changed: `ClassicalLean/NumberTheory/PrimitiveDivisor.lean` (its line 423, a
name-resolution check, listed in `tools/witness_reviewed.txt` as `NO-DOCSTRING`).

A module that the gate's first library run or the process sweep adds is named in the follow-up edit,
with the run or review that added it.

Also: the new `tools/witness_gate.py`, `tools/witness_gate_tests.py`, `tools/witness-fixtures/` and
`tools/witness_reviewed.txt`; `tools/UninformativeReport.lean` (its one `set_option maxHeartbeats`
line), `tools/VacuityGate.lean` (FAIL text strings and comments only), `.github/workflows/ci.yml`
(one step, if the gate's time allows); `HANDOFF.md` sections 1 and 4; `records/CLAIMS.md` and
`records/orders/INDEX.md` (this order's rows appended at the bottom, and LEAN-35's push recorded in
LEAN-35's two rows), this fragment and the order's copy. No declaration, no import line, no other
file under `tools/`, nothing in `records/rules.toml`, the lake files or `lean-toolchain`; `HANDOFF.md`
sections 0, 2, 3, 5 and 6 untouched.

## Order LEAN-35's push

By records/README.md rule 2 ("the next order's records commit appends the push of the order before
it to that order's INDEX row and CLAIMS row"), this round's first commit inserts into LEAN-35's
INDEX row (after ``one bridge found (row 165, lane `MATH-PLAN-library-2-bridges-2.md`)``, before its
commits cell) and its CLAIMS row (before the final ` |`) the text ``; pushed by Dustin: DSMain's
master ref written 2026-10-25 09:08:03 EDT, GitHub master equal (`ac62f50`)``, by the script
`evidence/pushnote.py` (LEAN-35's, adapted), which asserts the text after each anchor before
inserting and runs before anything is appended. The time is the mtime of
`/data/git/classical-lean.git/refs/heads/master`, which holds `ac62f505db03edda95e7f7fa83a301a07ddda924`,
read again by this session (label `pushref`).

Records files written by this session's commands, not by the evidence helper (HANDOFF.md rule 23):
the order's copy (written from the connector's reply by `evidence/replyextract.py`, its sha256
checked, and copied into the tree by `evidence/records1.sh` through `ev.sh --nolean`, label
`records1`), this fragment, the INDEX row and the CLAIMS row (written with the Write tool into the
evidence folder, hashed by `hl.sh`, and copied or appended by `records1.sh` through `ev.sh --nolean`,
label `records1`).
