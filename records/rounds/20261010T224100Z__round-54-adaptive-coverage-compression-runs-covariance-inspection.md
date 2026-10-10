# Round 54 — adaptive coverage on any sequence, a code as a bet, streaks under chance, noise in correlation eigenvalues, and the inspection paradox (order LEAN-26)

Session: Claude Code `session_015ETfwXkALXqpC9EJSHqpTp` on DSMain, as dustin, executing order
`LEAN-26` (`records/orders/20261010T224000Z__claude-code__order-lean26-adaptive-coverage-compression-runs-covariance-inspection.md`),
batch 10 of the plan `/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md` (sha256
c73957af6a9f2d19aacfd3acfc1d42d9a2a124fabefae62bbfee026090422898), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `paper-crypto-21`, made from `origin/master` =
`bd8d151` (equal to `git ls-remote github master`). Lean and Mathlib v4.34.0. Nothing pushed.
Evidence: `~/lean/lean26-checks/` (outside the repository), `evidence.log` (time, label, rc,
prediction, command per run).

First part written before any module change, so that gate 6 finds the new modules' paths before
their commits; completed after the work, below. Item numbers are the plan's.

Modules this round plans to add or change (as the claim row):

* `ClassicalLean/Probability/InspectionParadox.lean` — new module, item 71; added to `ClassicalLean.lean`.
* `ClassicalLean/Statistics/AdaptiveCoverage.lean` — new module, item 67; added to `ClassicalLean.lean`.
* `ClassicalLean/Probability/LongestRun.lean` — new module, item 69; added to `ClassicalLean.lean`.
* `ClassicalLean/InformationTheory/CompressionTest.lean` — new module, item 68; added to `ClassicalLean.lean`.
* `ClassicalLean/Probability/CovarianceDirections.lean` — existing module, extended, item 70.

Mathlib re-checked before the records were written (`~/lean/lean26-checks/search.out`): none of
the five items is in Mathlib v4.34.0, so none is dropped or reduced. The plan written before any
Lean or records work: `~/lean/lean26-checks/plan.md`. Item 68 follows the ruling sent during the
session (in the order copy): a test against a null law fixed in advance, not a clumping test.
