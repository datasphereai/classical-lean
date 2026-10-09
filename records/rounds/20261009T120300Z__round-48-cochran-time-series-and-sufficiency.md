# Round 48 — Cochran's theorem, autocovariances, tail bounds, the condition number, linear ODEs, Euler's method, and sufficiency (order LEAN-20)

Session: Claude Code `session_01JNjgq2PB4rcJA4c8fQNFpA` on DSMain, as dustin, executing order
`LEAN-20` (`records/orders/20261009T120200Z__claude-code__order-lean20-cochran-time-series-and-sufficiency.md`), batch 4 of the plan
`/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md` (sha256
62001c8f9ac4d6cf7947c055c929967d6474ede8b47830f3c208f52213161e44), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `paper-crypto-15`, made from `origin/master` =
`dab0d3e`. Lean and Mathlib v4.34.0. Nothing pushed. Evidence: `~/lean/lean20-checks/` (outside the
repository), `evidence.log` (time, label, rc, prediction, command per run).

First part written before any module change, so that gate 6 finds the new modules' paths before
their commits; completed after the work, below.

Modules this round plans to change or add (as the claim row):

* `ClassicalLean/Statistics/Cochran.lean` — new module, item 24; added to `ClassicalLean.lean`.
* `ClassicalLean/Probability/YuleWalker.lean` — new module, item 25; added to `ClassicalLean.lean`.
* `ClassicalLean/Probability/MovingAverage.lean` — new module, item 26; added to `ClassicalLean.lean`.
* `ClassicalLean/Probability/TailBounds.lean` — new module, items 27 and 28; added to `ClassicalLean.lean`.
* `ClassicalLean/Analysis/ConditionNumber.lean` — new module, item 29; added to `ClassicalLean.lean`.
* `ClassicalLean/Analysis/LinearODE.lean` — new module, item 30; added to `ClassicalLean.lean`.
* `ClassicalLean/Analysis/EulerMethod.lean` — new module, item 31; added to `ClassicalLean.lean`.
* `ClassicalLean/Statistics/Sufficiency.lean` — new module, items 50 to 54; added to `ClassicalLean.lean`.

Items 30 and 31 are done last; if the session cannot finish them they move to batch 5, and this
fragment will say so.

Mathlib re-checked before the records were written (`~/lean/lean20-checks/search.out`): none of
the thirteen items is in Mathlib v4.34.0, so none is dropped. Item 30 is reduced to applying
Mathlib's `hasDerivAt_exp_smul_const` and `ODE_solution_unique_univ`; items 50 to 54 use order
LEAN-19's `integral_sq_condExp_sub_le` and `variance_condExp_le` and do not prove them again.

Added during the work (Dustin, in chat): item 61, the completeness of the coin-flip head count and
the sample mean as the least-variance unbiased estimator, in `ClassicalLean/Statistics/Sufficiency.lean`
with items 50 to 54. The plan's sha256 is now
a3006a18bb59a1228f69b5426beb12bb9ec9f9e79ba61c2bcf91563a14665216; rows 24 to 54 did not change.
Mathlib re-checked for item 61 (`~/lean/lean20-checks/search61.out`): not present.
