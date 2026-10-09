# Round 51 — Courant–Fischer min–max and Weyl's inequality, strong duality for linear programs, Simpson's rule error bound, and Euler–Maclaurin to first order (order LEAN-23)

Session: Claude Code `session_01Sygvo6Yn77Tbb7i6N4k4a1` on DSMain, as dustin, executing order
`LEAN-23` (`records/orders/20261009T185500Z__claude-code__order-lean23-min-max-lp-duality-simpson-euler-maclaurin.md`),
batch 7 of the plan `/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md` (sha256
5c2381ba371a3b810dbc39302c724ff7d2279fca9d9870d354f269ae6f048fc0), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `paper-crypto-18`, made from `origin/master` =
`607f185`. Lean and Mathlib v4.34.0. Nothing pushed. Evidence: `~/lean/lean23-checks/` (outside the
repository), `evidence.log` (time, label, rc, prediction, command per run).

First part written before any module change, so that gate 6 finds the new modules' paths before
their commits; completed after the work, below. Item numbers are the plan's.

Modules this round plans to add (as the claim row):

* `ClassicalLean/Analysis/Simpson.lean` — new module, item 48; added to `ClassicalLean.lean`.
* `ClassicalLean/Analysis/EulerMaclaurin.lean` — new module, item 49; added to `ClassicalLean.lean`.
* `ClassicalLean/Algebra/MinMax.lean` — new module, item 46; added to `ClassicalLean.lean`.
* `ClassicalLean/Analysis/LinearProgram.lean` — new module, item 47; added to `ClassicalLean.lean`.

Mathlib re-checked before the records were written (`~/lean/lean23-checks/search.out`): none of
the four items is in Mathlib v4.34.0, so none is dropped or reduced. Statements elaborated with
`sorry` before this fragment, in scratch files outside the repository (`stmt/`): `st1-*.out`, rc 0,
23 `sorry` warnings (24 predicted: I counted 8 theorems in the linear-program file, which has 7)
and 2 lint warnings (`Fintype` where `Finite` suffices); after the fix `st2-*.out`, rc 0, 23 `sorry`
warnings, nothing else. The checks behind the needed-hypothesis table: `checks.py`, `chk1.out`,
ALL OK (34 lines).

## Completed after the work

All four items of batch 7 are done (46 to 49), with the plan's numbering, built in the suggested
order 48, 49, 46, 47. Citations of works nobody here read are author, title and year only:
Courant 1920, Fischer 1905, Weyl 1912; Farkas 1902, Gale, Kuhn and Tucker 1951; Euler 1738,
Maclaurin 1742.

Commits on `paper-crypto-18` (made from `origin/master` = `607f185`; nothing pushed):

* `3e3f442` records before the work (this fragment's first part).
* `5240ec1` `ClassicalLean/Analysis/Simpson.lean`, item 48 (new module).
* `4020331` `ClassicalLean/Analysis/EulerMaclaurin.lean`, item 49 (new module).
* `6997dc2` `ClassicalLean/Algebra/MinMax.lean`, item 46 (new module).
* `531f4c8` `ClassicalLean/Analysis/LinearProgram.lean`, item 47 (new module).

Changes from the drafted statements (`~/lean/lean23-checks/stmt/`, `st2-*.out`): item 48 gained
`abs_simpson_error_pow_four_eq_bound` (review r48); item 49's integrability helper is
`intervalIntegrable_sawtooth_mul`, with `abs_sawtooth_le`, `measurable_sawtooth`,
`integral_sawtooth_mul_unit`; item 46's Weyl hypotheses became inequalities, `i + j ≤ k` and
`k + n ≤ i + j + 1` (review r46), `S` comes before `T` in the arguments, and the helpers
`re_inner_eq_sum`, `norm_sq_eq_sum`, `eigenSpan` and its lemmas, `exists_unit_mem_inf`,
`abs_re_inner_le`, `re_inner_add_apply` were added; item 47 gained
`exists_linearIndependent_of_nonneg` (Carathéodory for cones), `nonneg_of_forall_dotProduct_nonneg`,
`dualitySystem`, and `isGreatest_primal_isLeast_dual_of_bddAbove` / `_of_bddBelow` (the textbook
form, review r47), and six `example`s that check the needed hypotheses in Lean.
Routes that differ from the plan's rows: item 47 does not use `ProperCone.hyperplane_separation`
(the row's "rests on"; Mathlib's Farkas needs a closed cone): it proves the image of the
nonnegative orthant closed and separates with `geometric_hahn_banach_closed_point`; item 48 does
not use Taylor's theorem (the mean value theorem and the trapezoid file's integration step);
item 49 is proved directly, one integration by parts per unit interval, not from Abel summation,
and holds for negative integer endpoints.

Cold reviews, one per module before its commit, each by a fresh general-purpose subagent with no
persistent memory, in its own scratch folder (`~/lean/lean23-checks/reviews/`); all four PASS WITH
FINDINGS, no BLOCKER, no MAJOR. MINOR: r48 5, r49 6, r46 9, r47 4; all applied except r47's first,
which concerns the plan's row (recorded above, not edited). Hashes (sha256, first 16 hex digits):

| review | brief sha256 | review sha256 |
|---|---|---|
| r48 | `c0c9fd8fa481fa1d` | `0ac850443cd9ed15` |
| r49 | `794d99efd22f5df4` | `1c6dc4abca6e8416` |
| r46 | `c2773aec08aff07b` | `e74796cf8d25ede3` |
| r47 | `54bb6ab524357462` | `fd84c94498c1a2d3` |

`~/.claude/agent-memory/`: the sha256 of every file (58) was the same before the first review and
after the last.

Gates on the clean tree at `531f4c8` (`~/lean/lean23-checks/g1-*.out`): `nice -n 19 lake build`
rc 0, 4126 jobs, 0 warning lines; AxiomGate PASS, 2744 theorem constants; VacuityGate PASS;
check_sorry PASS, 109 files; banned_vocab_scan PASS, 109 files; check_records PASS, 109 modules.
The needed-hypothesis checks (`checks.py`, sha256 `f8f51fcd455ba5c6`; output `chk4.out`, ALL OK)
fail with rc 1 on a copy with one planted failure, naming only the plant (`fire-checks.out`).

Theorem constants: 2744 against 2640, so 104 new. Predicted before any gate (`prediction.txt`,
sha256 `8da90897d8f4313d`): by compiling a scratch copy of each new module with the census
(Method B): Simpson 30, EulerMaclaurin 12, MinMax 30, LinearProgram 32, so 2744: a hit. Not a
blind test: the vacuity probe, run on each built module before its review, had already printed
the same totals. From the source alone (Method A): 45 hand-written theorems (47 lines begin with
"theorem"; two are docstring prose), a hit by name; the helpers (34 `_simp_`, 21 `_proof_`, 4
equation lemmas) were not modelled blind, since the totals were known by then.

Build jobs: 4126, not the order's 4076 + 4 = 4080: the new imports bring 46 Mathlib modules into
the import closure, nearly all through `Mathlib.NumberTheory.ZetaValues` (item 49's
`periodizedBernoulli`); measured before the build from the environment's module list (5611 to
5661 modules) and predicted as 4126: a hit.

Gate 7, `~/lean/recheck/run-recheck.sh 531f4c8 ~/lean/classical-lean-paper-crypto`: rc 0, last line
`ALL PASSED for 531f4c80e9cb882d215da1f8c9e8b4c21373945b` (`g7a-recheck.out`): 4126 jobs;
leanchecker 109 modules, 0 failed; nanoda checked 88968 declarations with no errors, only the
three standard axioms; 2744 theorems under the ClassicalLean name, counted from the export (equal
to AxiomGate); the planted wrong proof was rejected and named
(`ClassicalLean.Analysis.LogDrag.mean_log_one_add_le`). Predicted before the run: rc 0, 4126
jobs, 109 modules, 2744, about 88967 declarations (88900 to 89050, from a reachability count of
my own calibrated on LEAN-22's 88639): all hit; the declaration count was one above the point
prediction, inside the range.

Not touched: anything under `~/trading`; nothing under `~/lean/recheck` was edited (its script was
run). No push.
