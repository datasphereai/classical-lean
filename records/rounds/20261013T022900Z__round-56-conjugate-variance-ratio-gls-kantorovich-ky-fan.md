# Round 56 — convex conjugate, variance ratio, GLS for a common mean, Kantorovich, Ky Fan (order LEAN-27)

Session: Claude Code `session_014kHVkG96PnyF2Mo91rghpR` on DSMain, as dustin, executing order
`LEAN-27` (`records/orders/20261013T022800Z__claude-ai__order-lean27-conjugate-variance-ratio-gls-kantorovich-ky-fan.md`),
batch 1 (items 79 to 83) of the plan `/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library-2.md`
(sha256 6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `lean-27`, made from `origin/master` = `92f8ae5`
(equal to `git ls-remote github master`). Lean and Mathlib v4.34.0. Nothing pushed.
Evidence: `~/lean/lean27-checks/` (outside the repository), `evidence.log` (time, label, rc,
prediction, command per run).

First part written before any Lean file changed; completed after the work, below.

## Modules this round adds or changes

* item 79: the new module `ClassicalLean/Analysis/ConvexConjugate.lean`
  (`ClassicalLean.Analysis.ConvexConjugate`);
* item 80: `ClassicalLean/Probability/EffectiveSampleSize.lean` (extended);
* item 81: `ClassicalLean/Statistics/GeneralizedLeastSquares.lean` (extended; gains an import of
  `ClassicalLean.Analysis.MinimumQuadraticForm`);
* item 82: the new module `ClassicalLean/Algebra/Kantorovich.lean`
  (`ClassicalLean.Algebra.Kantorovich`);
* item 83: `ClassicalLean/Algebra/MinMax.lean` (extended);
* `ClassicalLean.lean`: two import lines.

## Job 0: the vacuity gate fix

`tools/VacuityGate.lean`, function `unfoldNamed` only: its call to `whnfCore` is to reduce no
matchers or recursors, so a glued part computed by pattern matching passes, as Dustin ruled.
Tests first (`tools/VacuityGateTests.lean`: `vac_univ_mem`, `Small2`, `real_hyp_and_small2`;
`tools/vacuity_reviewed_tests.txt` for any generated name that must be LISTED), measured under
the gate at `92f8ae5`; then the fix, with the order's stop rule.

Standing rule 2 (round 55, the bridge search) applies; round 55's standing rule 1 (banned
vocabulary) is withdrawn by the order's revision r3 (Dustin's ruling of 2026-10-12 19:42 EDT,
store row 20261012-005).

## Completed after the work

(to be written after the work)
