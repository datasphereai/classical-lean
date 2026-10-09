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

## Completed after the work

Commits on `paper-crypto-15`, in order: `eeb8a37` (records, before the work), `55fb2ad` (Cochran
and `ClassicalLean.lean`, item 24), `c1d0c3b` (records: item 61 added during the work), `c22fa09`
(YuleWalker, item 25), `ba84d3d` (MovingAverage, item 26), `4222f67` (TailBounds, items 27 and
28), `ceec928` (ConditionNumber, item 29), `530140c` (Sufficiency, items 50 to 54 and 61),
`f4ae0a8` (LinearODE, item 30), `774705f` (EulerMethod, item 31), then the records commit that
completes this fragment (its hash is in the order's report, not here). Each module commit added
its own import line to `ClassicalLean.lean`, so no commit carried an unreviewed module's line.
All fourteen items are done; items 30 and 31 did not move to batch 5.

Declarations. Item 24 (`ClassicalLean/Statistics/Cochran.lean`): `rank_add_le`, `rank_sum_le`,
`mul_eq_zero_of_add_eq_one_of_rank_add_le`, `isIdempotentElem_of_add_eq_one_of_rank_add_le`,
`rank_eq_trace_of_isIdempotentElem`, `isIdempotentElem_of_sum_rank_eq`, `sum_rank_eq_iff`,
`mul_eq_zero_of_sum_rank_eq`, `completeOrthogonalIdempotents_of_sum_rank_eq`,
`rank_mul_leastSquares`. Item 25 (`ClassicalLean/Probability/YuleWalker.lean`):
`covariance_eq_sum`, `isSolution_autocovariance`, `exists_poly_mk_autocovariance_eq`. Item 26
(`ClassicalLean/Probability/MovingAverage.lean`): `movingAverage`, `covariance_movingAverage`,
`covariance_movingAverage_eq_zero_of_lt`. Items 27 and 28
(`ClassicalLean/Probability/TailBounds.lean`): `measureReal_sub_integral_ge_le`,
`measureReal_gt_ge`, `measureReal_gt_ge_of_nonneg`. Item 29
(`ClassicalLean/Analysis/ConditionNumber.lean`): `norm_sub_div_le_cond`,
`norm_sub_div_le_cond_of_mulVec`. Item 30 (`ClassicalLean/Analysis/LinearODE.lean`):
`hasDerivAt_exp_smul_mulVec`, `eq_exp_smul_mulVec`. Item 31
(`ClassicalLean/Analysis/EulerMethod.lean`): `eulerIterate`,
`abs_sub_sub_mul_le_of_lipschitzWith`, `abs_sub_eulerIterate_le`. Items 50 to 54 and 61
(`ClassicalLean/Statistics/Sufficiency.lean`): `IsSufficient`, `IsSufficient.exists_condExp_eq`,
`integral_sub_condExp_sq_eq`, `integral_sub_sq_eq_integral_condExp_sub_sq_add`,
`IsSufficient.raoBlackwell`, `IsComplete`, `variance_le_of_isSufficient_of_isComplete`,
`ae_eq_of_variance_eq_of_isSufficient_of_isComplete`, `stronglyMeasurable_comp_comap`,
`eq_of_ae_eq_of_pos`, `comap_le_of_finite`, `condExp_comap_ae_eq`,
`isSufficient_iff_factorization`, `coinFlips`, `numHeads`, `coinFlips_real_singleton`,
`coinFlips_real_singleton_eq_pow`, `numHeads_le`, `isSufficient_numHeads`,
`condExp_firstFlip_ae_eq`, `integral_sampleMean_sub_sq_le`, `isComplete_numHeads`,
`variance_sampleMean_le`, `eq_sampleMean_of_variance_eq`, and private helpers.

Names changed from the plan's rows: item 26's second theorem `covariance_movingAverage_eq_zero_of_lt`
(draft `covariance_movingAverage_of_lt`, review r26); item 31 `abs_sub_eulerIterate_le` (row:
`abs_sub_eulerStep_le`; it bounds `k` steps) and its helper `abs_sub_sub_mul_le_of_lipschitzWith`
(review r31); item 53 `isSufficient_numHeads` (row: `isSufficient_sum_bernoulli`); item 61
`isComplete_numHeads`, `variance_sampleMean_le`, `eq_sampleMean_of_variance_eq` (row:
`isComplete_sum_bernoulli`, `sampleMean_isMinVariance`; no `IsMinVariance` is defined). Item 22's
module `ClassicalLean.Statistics.RaoBlackwell` is used, not changed.

Statements changed after the statements run, each to a stronger or equal statement:
`IsSufficient.exists_condExp_eq` needs only finite measures and no `m ≤ m₀` (12:04, before any
proof); Paley–Zygmund needs only `0 ≤ E X` (review r27; the pointwise `X ≥ 0` form kept as
`measureReal_gt_ge_of_nonneg`, almost everywhere); Yule–Walker without the noise hypothesis `he`
(review r25); the condition number's matrix form over any `RCLike` field (review r29); Cochran's
forward direction over any field and orthogonality with `2 ≠ 0` (review r24); and `IsSufficient`
now contains `m ≤ m₀` (review r50, MAJOR: without it every family was sufficient by Lean's
convention), so `raoBlackwell` and the Lehmann–Scheffé theorems no longer take `hm` separately.

Mathlib re-checked before the records were written (`~/lean/lean20-checks/search.out`; item 61:
`search61.out`): none of the fourteen items is in Mathlib v4.34.0, so none was dropped. Reduced to
what is missing: item 30 applies `hasDerivAt_exp_smul_const'` and `ODE_solution_unique_univ`;
items 50 to 54 use order LEAN-19's `integral_sq_condExp_sub_le` and `variance_condExp_le` and do
not prove them again.

Citations: checked by a web-search subagent against publication records, not against the papers or
books; the module docstrings say which. Cochran (1934) states his theorem for quadratic forms in
normal variables, so the module calls its result the matrix algebra behind it; the plan's
Paley–Zygmund paper title was doubtful, so only "Paley and Zygmund (1932), modern form" is cited;
Euler's bound matches Burden and Faires Theorem 5.9 as numbered in lecture notes; no unverified
theorem number is cited.

Statements: drafted in `~/lean/lean20-checks/Statements.lean`, elaborated with `sorry` before any
proof. `st1` rc 1 (`σ` is reserved notation under `open scoped unitInterval`; unused instance
arguments); `st2` rc 0, 25 `sorry` warnings, nothing else (predicted 25); `st3` after the two
strengthenings, rc 0, 25; `st4` with item 61's three statements, rc 0, 28 (predicted 28).

Hypotheses: each module's docstring names, for each main theorem, the hypotheses that fail when
dropped, with the exact case, and those not shown needed. The cases are
`~/lean/lean20-checks/checks.py` (standard library, seeded, exact Fractions except a few marked
float checks, exit code 1 on any failure; fire-tested with a planted failure, `fire-checks` rc 1).
Runs: `chk1` ALL OK; `chk2` rc 1 (my own index error after adding computed cases); `chk3` to
`chk10` ALL OK as cases were made computed after reviews r25, r26, r29 and r31; the final run is
`chk10` ("ALL OK", rc 0). Cases marked "by hand" in the script need infinite spaces or
non-measurable sets.

Cold reviews (rule 13), each by a fresh general-purpose subagent in its own scratch folder under
`~/lean/lean20-checks/review/`, brief built by `prep_review.sh`; the sha256 of every file under
`~/.claude/agent-memory/` was the same before each review and after the last. All eight: PASS WITH
FINDINGS, no BLOCKER.

| review | module | findings | applied | not done |
|---|---|---|---|---|
| r24 | Cochran | 7 MINOR | 1, 2, 3, 4, 6, 7 | 5 the names (`sum_rank_eq_iff` is the order's) |
| r25 | YuleWalker | 1 MAJOR (root import), 6 MINOR | all but 7 | 7 the name `covariance_eq_sum` (the order's) |
| r26 | MovingAverage | 6 MINOR | all | — |
| r27 | TailBounds | 8 MINOR | 1, 2, 3, 4, 5, 7 | 6 the name; 8 a Paley–Zygmund title (not verifiable) |
| r29 | ConditionNumber | 4 MINOR | 1, 2, 3, 4a | 4b the left-inverse hypothesis form |
| r50 | Sufficiency | 1 MAJOR, 9 MINOR | MAJOR; 2, 3, 4 (recorded), 5, 7 (unused instance), 8, 9 (docstring) | 6 `IsComplete` kept (the order's name; noted); 7 `hpos` and `p ∈ [0, 1]`; 10 outside the diff |
| r30 | LinearODE | 4 MINOR | 1, 2 (noted), 4 | 3 wider forms |
| r31 | EulerMethod | 8 MINOR | 1, 3, 4, 5, 6, 7, 8 | 2 the `abs h` form |

Review files and sha256 (inserted by script; six of the eight hashes first typed by hand were
wrong):
r24 1120d7f9...dc3c6b47, r25 bb755a0a...d5a23985, r26 7a0a0159...7050e4d4,
r27 92258f08...aa7c9a6f, r29 f79bb868...2c5941f4, r50 2cc5a439...c676d226, r30 75e1fe46...ee00d903,
r31 c912ce9f...8c43d063.

New theorem constants: 126 predicted by `Count.lean` (the gate's predicate, by module; `count.out`
reads "total 126"), written in
`prediction.txt` at 2026-10-09T12:59:23Z before any whole-library gate: Cochran 18, YuleWalker 11,
MovingAverage 8, TailBounds 11, ConditionNumber 10, LinearODE 2, EulerMethod 14, Sufficiency 52;
2316 + 126 = 2442 predicted. The axiom gate measured 2442 (order LEAN-19: 2316): a hit. A clean
tree at `774705f`.

Gates on the clean tree at `774705f` (`gates.sh g1`, every rc 0): `lake build` "Build completed
successfully (4041 jobs)." with 0 warning lines (predicted 4041); "axiom gate PASS — 2442 theorem
constant(s) under [ClassicalLean]"; "vacuity gate PASS — no vacuous theorems in [ClassicalLean]";
"check_sorry PASS — 96 file(s) under ClassicalLean"; "banned_vocab_scan PASS — 96 file(s) under
ClassicalLean + ClassicalLean.lean, 0 hits"; "check_records PASS — 96 module(s) under
ClassicalLean". check_sorry fire test: a `sorry` planted in a scratch copy outside the repository
gave rc 1, "check_sorry FAIL — 1 violation(s) across 96 file(s).", naming only the plant.
`#print axioms` (`Axioms.lean`, `axioms2`, rc 0): all 50 new public declarations print exactly
`[propext, Classical.choice, Quot.sound]` (counted by script; a first run listed a false name
taken from a docstring line and was redone). The vacuity gate's budget was not changed.
