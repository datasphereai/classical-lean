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

## Completed after the work

All five items of batch 10, the last batch of the plan, are done (67 to 71), with the plan's
numbering, built in the suggested order 71, 67, 69, 68, 70. No paper or book is cited.

Commits on `paper-crypto-21` (made from `origin/master` = `bd8d151`; nothing pushed):

* `e41e41c` records before the work (this fragment's first part).
* `b38ff92` `ClassicalLean/Probability/InspectionParadox.lean`, item 71 (new module; 19 theorem
  constants).
* `ab91757` `ClassicalLean/Statistics/AdaptiveCoverage.lean`, item 67 (new module; 12).
* `ba29bba` `ClassicalLean/Probability/LongestRun.lean`, item 69 (new module; 37).
* `2abfb61` `ClassicalLean/InformationTheory/CompressionTest.lean`, item 68 (new module; 15).
* `00d4f23` `ClassicalLean/Probability/CovarianceDirections.lean`, item 70 (extended; 19 -> 42,
  23 new).

Item 68 follows the ruling sent during the order: a test against a null law fixed in advance (any
finite law, and `n` independent trials with a win rate `p` fixed in advance), the fair coin as
`p = 1/2`; a rejection means "not this null law" (clumping, another win rate, or both); the exact
3/5 example is check C7. On estimating `p`, the checks support a narrower statement than the
ruling's sentence: a code fitted to the data without paying for it breaks the rate (C9, a Kraft
failure); the estimate plugged into the null law with a fixed code keeps it, conservatively (C8,
by hand and exhaustive to `n = 8`; not in Lean). Item 67 is wider than the plan's row (alpha may
be 0 or 1, err in [0, 1], any starting level) with the plan's bound. Item 71 needs only
`sum L >= 0` for the inequality; item 70 adds `E[S] = I`, the eigenvalue form and the bound
`(p - 1) / n`.

Gates at `00d4f23`: build 4166 jobs, 0 warnings; AxiomGate 3158; VacuityGate, check_sorry,
banned_vocab_scan, check_records PASS on 120. Build jobs predicted 4166 = 4160 + 4 new modules + 2
Mathlib modules (`Algebra.Order.Chebyshev`, `Algebra.Order.Rearrangement`): hit. The theorem count
was predicted blind: Method B 3158 (hit); Method A 3133 written blind, 3134 with the theorem review
r70 added, inside its range 3119 to 3203, a miss by 24. By kind, Method A against measured:
hand-written 43 / 43; `eq_N` 12 / 12; `eq_def` 1 / 1; matcher equations 0 / 2 (`alphaSeq`);
`IsMissSeq` fields 4 / 4; `_proof_` 18 / 16 (LongestRun 12 from 14 `omega`; `fairCoin._proof_1`
one, not two; `score._proof_1` not modelled; the `decide` gave none); `_simp_` 4 / 28 (LongestRun
16, CovarianceDirections 11: `simp only` calls with many membership or reversed lemmas);
`congr_simp` 0 / 0. Names in `~/lean/lean26-checks/census/`.

Gate 7 (`~/lean/recheck/run-recheck.sh 00d4f23 ~/lean/classical-lean-paper-crypto`): ALL PASSED;
4166 jobs; leanchecker 120 modules, 0 failed; nanoda 90,482 declarations, no errors, only propext,
Classical.choice and Quot.sound; 3158 theorems from the export; the planted wrong proof rejected and
named. The export leaves out 18 `_unsafe_rec` compiler helpers, 1 of them new
(`AdaptiveCoverage.alphaSeq`).

Cold reviews r71, r67, r69, r68, r70: PASS WITH FINDINGS, no BLOCKER or MAJOR, every finding
applied (r68's renaming note and its EValueStepUp note go to the report). Statements changed after
their reviews, at the reviewers' request: `exists_mem_gap` (a hypothesis dropped),
`alphaSeq_mem_Icc` (stated with `Set.Icc`), the two LongestRun theorems (the probability-measure
instance dropped), `half` renamed `fairCoin`, and two new theorems
(`mean_le_integral_gapLength`, `one_add_le_integral_trace_sq_sampleCov`); a statement-change
review (r-eq) proved in Lean each old statement from the new one: equivalent or stronger, none
weaker. Not reached: nothing in batch 10.
