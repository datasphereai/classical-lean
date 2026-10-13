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

Items 79 to 83 of MATH-PLAN-library-2 are proved, no `sorry`, no new axiom; nothing narrower than
the plan's rows (three statements wider, each said in its module docstring). Job 0 landed in two
stages, the second by Dustin's ruling of 2026-10-12 (PairT must FLAG); one question to him is open
(an all-`True` match on a type without eta passes, test `lim_nat_true`).

Commits on `lean-27` (from `92f8ae5`; nothing pushed):

* `442a536` records before the work (this fragment's first part).
* Job 0: `68759cd` tests, `df2bd52` the iota fix, `04fe81e` and `c1b22b8` its review's findings;
  reopened: `62b160e` tests, `f70aa50` branch opening, `66402b7` tests, `82899d4` the `isDefEq`
  check and depth cap.
* `8f0980e` item 81 (`ClassicalLean/Statistics/GeneralizedLeastSquares.lean`), `e31168b` item 82
  (`ClassicalLean/Algebra/Kantorovich.lean`), `2970d06` item 83 (`ClassicalLean/Algebra/MinMax.lean`),
  `e78115a` item 79 (`ClassicalLean/Analysis/ConvexConjugate.lean`), `f11be68` item 80
  (`ClassicalLean/Probability/EffectiveSampleSize.lean`); `ClassicalLean.lean` gained two import lines.
* `15e003f` HANDOFF.md and ROADMAP.md; `6d84072` the bridge baseline `records/bridges/LEAN-27/`.

Per-module theorem constants (census of scratch copies, the axiom gate's `.thmInfo` predicate under
`ClassicalLean`): ConvexConjugate 5; Kantorovich 3; EffectiveSampleSize 50 → 63; GeneralizedLeastSquares
6 → 12; MinMax 30 → 42.

Whole-library numbers, all on the **clean** tree at `6d84072`: build 4168 jobs, 0 warnings;
AxiomGate PASS 3197; VacuityGate PASS, 1 reviewed helper, 0 VACUOUS-PENDING, rule 5 ran out on 0
theorems, no new list entry (2:52.31, 5049780 KB); the gate's tests 85, 47 flagged, 0 mismatches;
check_sorry PASS 122; check_records PASS 122. Gate 7 at `6d84072`: ALL PASSED, 4168 jobs, 122 modules 0 failed, 90558 declarations no errors, three standard axioms, 3197, planted fault named (20:17.84, 4749584 KB); `6d84072` adds only `records/bridges/LEAN-27/` to `15e003f`.

Bridge search (standing rule 2) against `records/bridges/VACUITY-1/`: rc 1, 140 new, 28 gone; no new
bridge (the strong pairs are plan items 98 and 111). **Current baseline: `records/bridges/LEAN-27/`.**
Report: lane `LEAN-27-report.md`.

**Added 2026-10-13 after a second ruling (Dustin, about 23:52 EDT on 2026-10-12): NatT must fail
closed as UNCHECKED, never pass.** Job 0 reopened again: `66776eb` tests (`vac_unchecked_nat_true`,
`vac_unchecked_hyp_and_nat_true`, `real_nat_true_and_work`; the runner expects UNCHECKED for names
starting `vac_unchecked_`), `5344c16` the fix (an all-`True` match whose `True.intro` proof the
kernel cannot confirm makes the fixed test throw "every case is True; kernel could not confirm the
proof", which `judge` turns into UNCHECKED), confirming review PASS WITH FINDINGS (7 MINOR, stated
in HANDOFF.md §4), `ff68a8a` HANDOFF.md §4. No `ClassicalLean/` file changed. The open question to
Dustin above is answered by that ruling. Gates re-run on the **clean** tree at `ff68a8a`: build
4168 jobs, 0 warnings; AxiomGate PASS 3197; VacuityGate PASS, 1 reviewed helper, 0 VACUOUS-PENDING,
rule 5 ran out on 0, no UNCHECKED (2:47.33, 5051576 KB); tests 88, 47 flagged, 0 mismatches;
check_sorry PASS 122; check_records PASS 122. Gate 7 at `ff68a8a`: ALL PASSED, 4168 jobs, 122 modules 0 failed, 90558 declarations no errors, three standard axioms, 3197, planted fault named (20:02.26, 4749160 KB). Current bridge baseline
unchanged: `records/bridges/LEAN-27/` (no module changed since `15e003f`).
