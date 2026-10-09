# Round 52 — Neyman–Pearson, Karlin–Rubin, Sanov for a finite alphabet, Basu, James–Stein and Glivenko–Cantelli (order LEAN-24)

Session: Claude Code `session_01QpAr2Yyk1XLSrhVcfEz1tw` on DSMain, as dustin, executing order
`LEAN-24` (`records/orders/20261009T215000Z__claude-code__order-lean24-neyman-pearson-sanov-basu-james-stein-glivenko-cantelli.md`),
batch 8 of the plan `/opt/datasphere/lane/inbox/threads/staging/MATH-PLAN-library.md` (sha256
5c2381ba371a3b810dbc39302c724ff7d2279fca9d9870d354f269ae6f048fc0), in the worktree
`~/lean/classical-lean-paper-crypto` on branch `paper-crypto-19`, made from `origin/master` =
`4a1accf` (equal to `git ls-remote github master`). Lean and Mathlib v4.34.0. Nothing pushed.
Evidence: `~/lean/lean24-checks/` (outside the repository), `evidence.log` (time, label, rc,
prediction, command per run).

First part written before any module change, so that gate 6 finds the new modules' paths before
their commits; completed after the work, below. Item numbers are the plan's.

Modules this round plans to add or change (as the claim row):

* `ClassicalLean/Statistics/NeymanPearson.lean` — new module, items 55 and 56; added to `ClassicalLean.lean`.
* `ClassicalLean/Statistics/Sufficiency.lean` — existing module, item 58 (Basu's theorem) added.
* `ClassicalLean/InformationTheory/MethodOfTypes.lean` — new module, item 57; added to `ClassicalLean.lean`.
* `ClassicalLean/Probability/GlivenkoCantelli.lean` — new module, item 60; added to `ClassicalLean.lean`.
* `ClassicalLean/Statistics/JamesStein.lean` — new module, item 59; added to `ClassicalLean.lean`.

Mathlib re-checked before the records were written (`~/lean/lean24-checks/search.out`,
`search2.out`): none of the six items is in Mathlib v4.34.0, so none is dropped or reduced. The
plan written before any Lean or records work: `~/lean/lean24-checks/plan.md`.

## Completed after the work

All six items of batch 8 are done (55 to 60), with the plan's numbering, built in the suggested
order 55 and 56, 58, 57, 60, 59. Citations of works nobody here read are author, title and year
only: Neyman and Pearson 1933; Karlin and Rubin 1956; Sanov 1957; Basu 1955; Stein 1956, James
and Stein 1961, Stein 1981; Glivenko 1933, Cantelli 1933.

Commits on `paper-crypto-19` (made from `origin/master` = `4a1accf`; nothing pushed):

* `3d56fc7` records before the work (this fragment's first part).
* `31adf17` `ClassicalLean/Statistics/NeymanPearson.lean`, items 55 and 56 (new module).
* `71eddbd` `ClassicalLean/Statistics/Sufficiency.lean`, item 58 (Basu's theorem added).
* `f2c93ba` `ClassicalLean/InformationTheory/MethodOfTypes.lean`, item 57 (new module).
* `dff5586` `ClassicalLean/Probability/GlivenkoCantelli.lean`, item 60 (new module).
* `6f7ce6b` `ClassicalLean/Statistics/JamesStein.lean`, item 59 (new module).

Item 56 is the narrower Karlin–Rubin form, as ruled from Dustin's side during the order: the
monotone likelihood ratio is `f θ' = g (S ω) · f θ` with `g ≥ 0` nondecreasing on all of `ℝ`, at
every `ω`. Excluded: models whose support gains points as `θ` grows (uniform on `[0, θ]`, on
`[θ, θ + 1]`). Qualify: normal laws in their mean, coin flips in their chance of heads, shifted
exponential laws on `[θ, ∞)`. The theorem Lean proves is
`isUniformlyMostPowerful_of_monotoneLikelihoodRatio`.

Changes from the drafted statements (`~/lean/lean24-checks/stmt/`, `st1-*.out`, `st2-*.out`):
item 55's existence theorems take `α ∈ (0, 1]` (size `1` added) and `exists_thresholdTest_size_eq`
takes one density (review r55); item 56's index type needs only a partial order (review r55);
item 57 drops `∑ p = 1` (unused) and asks `d ≤ D` only at the types in `E` (review r57); item 58
drops the coin-flip corollary (there every ancillary event has chance `0` or `1`); item 60 asks
measurability of `X 0` only and adds `bddAbove_abs_empiricalCDF_sub` (review r60); item 59 adds
the exact risk formula, `integral_inv_sqNorm_pos`, the comparison stated against the risk of `X`
(review r59) and the `d = 2` theorems. Routes that differ from the plan's rows: item 59 uses
`integral_mul_deriv_eq_deriv_mul_of_integrable` (whole line), not
`integral_mul_deriv_eq_deriv_mul`; item 60 uses the strong law at quantile grid points.

Cold reviews, one per module before its commit, each by a fresh general-purpose subagent with no
persistent memory, in its own scratch folder (`~/lean/lean24-checks/reviews/`), told to run no
census, probe or count; all five PASS WITH FINDINGS, no BLOCKER. MAJOR: r55 1 (the shifted
exponential was wrongly listed as excluded from item 56), fixed. MINOR: r55 7, r58 5, r57 4,
r60 3, r59 6; all applied, except r58's fifth (the plan's name `indepFun_of_isComplete_of_ancillary`
omits sufficiency), noted in the docstring. Hashes (sha256, first 16 hex digits):

| review | brief sha256 | review sha256 |
|---|---|---|
| r55 | `de6595488243cb78` | `be3692baabddb9f1` |
| r58 | `3ab2a09c2d9b51c6` | `7412ba6173c736e4` |
| r57 | `40cd7d1f1c2b78aa` | `44805a83cda6d4a9` |
| r60 | `e6ae321d205a12ff` | `e1bd1b458b9fba2d` |
| r59 | `b3c87ed59dc888e7` | `1a68edd2777ec527` |

`~/.claude/agent-memory/`: the sha256 of every file (58) was the same before the first review and
after the last.

Gates on the clean tree at `6f7ce6b` (`~/lean/lean24-checks/g1-*.out`): `nice -n 19 lake build`
rc 0, 4133 jobs, 0 warning lines; AxiomGate PASS, 2854 theorem constants; VacuityGate PASS;
check_sorry PASS, 113 files; banned_vocab_scan PASS, 113 files; check_records PASS, 113 modules.
The needed-hypothesis checks (`checks.py`, sha256 `b20201bf10f4d805`; output `chk10.out`, 29
lines, ALL OK) fail with rc 1 on a copy with one planted failure, naming only the plant
(`fire-checks.out`).

Theorem constants: 2854 against 2744, so 110 new. Predicted blind (`prediction.txt`, sha256
`7b8bf91de3c30de0`; its first part, Method A, hashed `0d1b8c220e5b513e` before the census ran): no
census, vacuity probe or gate was run on any new module before it was written, and the review
briefs forbade counts. Method B (scratch copies with the census): NeymanPearson 19,
MethodOfTypes 21, GlivenkoCantelli 16, JamesStein 51, Sufficiency +3, so 2854: a hit. Method A
(source only): 2865, range 2835 to 2895, a miss by 11 inside the range; by kind, the 65
hand-written theorems and instances and the 11 equation lemmas hit by name; `_proof_` 7 against
8 (missed `jamesStein._proof_1`, inside a definition); `_simp_` 38 modelled against 24 measured
(the theorems with a field_simp have 0 to 8 each, not 7); 2 `congr_simp` lemmas, a kind not modelled.

Build jobs: 4133 = 4126 + 4 new modules + 3 Mathlib modules newly in the import closure
(`Mathlib.Probability.CDF`, `Mathlib.Probability.Distributions.Gaussian.Real`,
`Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform`; the environment's module list
went from 5661 to 5668), predicted before the build: a hit.

Gate 7, `~/lean/recheck/run-recheck.sh 6f7ce6b ~/lean/classical-lean-paper-crypto`: rc 0, last
line `ALL PASSED for 6f7ce6b394965bede4343c6e1c4ff6cdd9649278` (`g7a-recheck.out`): 4133 jobs;
leanchecker 113 modules, 0 failed; nanoda checked 89585 declarations with no errors, only the
three standard axioms; 2854 theorems under the ClassicalLean name, counted from the export (equal
to AxiomGate); the planted wrong proof was rejected and named
(`ClassicalLean.Analysis.LogDrag.mean_log_one_add_le`). Predicted before the run: rc 0, 4133
jobs, 113 modules, 2854, planted fault rejected: all hit; the declaration count was predicted
only as more than LEAN-23's 88968 (no reachability count was run, to keep the census blind).

Not touched: anything under `~/trading`; nothing under `~/lean/recheck` was edited (its script was
run). No push. Batches 9 and 10 not started.
