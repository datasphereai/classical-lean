# Round 79 — Holm inside Benjamini–Hochberg, the correlation in [−1, 1], a Pinsker bound for tests, Richardson-extrapolated Heun is Simpson, Heun's exact error by Euler–Maclaurin (order CLOUD-MATH-5)

Session: Claude Code cloud session `session_01HgueTYMESHnLVKHDy4XkAM`
(https://claude.ai/code/session_01HgueTYMESHnLVKHDy4XkAM), executing order `CLOUD-MATH-5`
(`records/orders/20261030T211529Z__claude-ai__order-cloudmath5-holm-correlation-pinsker-heun-richardson-euler-maclaurin.md`),
bridge rows 158, 155, 164, 166 and 167 of `MATH-PLAN-library-2-bridges-2.md`, in a cloud container's
clone of GitHub `datasphereai/classical-lean` on branch `cloud-math-5`, from
`8631a8d3c4316d85c78df697436b0245fa24cf1b` (checked equal to `origin/cloud-math-5` before any
change). `git ls-remote origin master` at the start: `8631a8d3c4316d85c78df697436b0245fa24cf1b`
(`$HOME/cm5/start-refs.txt`). Lean and Mathlib v4.34.0 (`lake exe cache get`, 8908 files,
`cache-get.txt`).

**No drafts.** Each of the five bridges is stated and proved by this session from its row's sketch in
the order; no proof comes from an earlier draft.

Evidence: `$HOME/cm5/` (outside the repository); every count below is read from a saved output
there, cited by its file name (rule 9).

First part written before any Lean file changed; completed after the work, below.

## Modules this round adds (five new modules)

* bridge 158: `ClassicalLean/Probability/HolmInsideStepUp.lean`
  (`ClassicalLean.Probability.HolmInsideStepUp`), importing
  `ClassicalLean.Probability.StepDownProcedure` and `ClassicalLean.Probability.StepUpProcedure`;
* bridge 155: `ClassicalLean/Probability/CorrelationBound.lean`
  (`ClassicalLean.Probability.CorrelationBound`), importing `ClassicalLean.Analysis.Gruss` and
  `ClassicalLean.Probability.LinearPrediction`;
* bridge 164: `ClassicalLean/Statistics/PinskerTest.lean` (`ClassicalLean.Statistics.PinskerTest`),
  importing `ClassicalLean.Statistics.NeymanPearson` and `ClassicalLean.InformationTheory.Channel`;
* bridge 166: `ClassicalLean/Analysis/HeunRichardson.lean` (`ClassicalLean.Analysis.HeunRichardson`),
  importing `ClassicalLean.Analysis.EulerMethod` and `ClassicalLean.Analysis.Simpson`;
* bridge 167: `ClassicalLean/Analysis/HeunEulerMaclaurin.lean`
  (`ClassicalLean.Analysis.HeunEulerMaclaurin`), importing `ClassicalLean.Analysis.EulerMethod` and
  `ClassicalLean.Analysis.EulerMaclaurin`;
* `ClassicalLean.lean`: five import lines, at the end of its import block, in landing order, each
  added by its module's landing commit.

No existing module changes. `tools/vacuity_reviewed.txt` changes only if a helper is listed (the
order's rule 4). Nothing else under `tools/` changes.

## Starting counts (measured in this session, before any new module, clean tree at `8631a8d`)

* `curl -sSI https://cache.mathlib.org/ | head -3`: `HTTP/1.1 200 Connection Established`, then
  `HTTP/2 404` from the cache server itself, not a stop (`curl-cache.txt`); `lake exe cache get`
  then downloaded and decompressed 8908 files (`cache-get.txt`).
* `lake build`: exit 0, `Build completed successfully (4196 jobs).`, 0 lines with `warning:`
  (`start-lake-build.txt`).
* `lake env lean tools/AxiomGate.lean`: `axiom gate PASS — 3844 theorem constant(s) under
  [ClassicalLean] …; 0 scoped exceptions` (`start-axiom.txt`).
* `python3 -I tools/check_sorry.py`: PASS, 143 files (`start-sorry.txt`).
* `python3 -I tools/check_records.py`: PASS, 143 modules, 1 named exemption (`start-records.txt`).
* `lake env lean tools/VacuityGate.lean`: PASS, 1 reviewed helper, 0 VACUOUS-PENDING, rule 5 out of
  heartbeats on 0 theorems (`start-vacuity.txt`).
* sha256 of each output: `start_sha256.txt`.

## Probes (Setup 4)

One file per new module, importing exactly its imports (`$HOME/cm5/probes/probe158.lean`,
`probe155.lean`, `probe164.lean`, `probe166.lean`, `probe167.lean`; outputs `probe<n>.out`). Every
name the order cites was found. Two were not found as written, and were found under other names or
supplied otherwise (`probe158b.out`, `probe155b.out`, `probe155c.out`):

* `Finset.filter_card_add_filter_neg_card_eq_card`: Mathlib's name at v4.34.0 is
  `Finset.card_filter_add_card_filter_not`.
* the instance `IsProbabilityMeasure ((4⁻¹ : ℝ≥0) • Measure.count : Measure (Fin 2 → Bool))` is not
  synthesized; it is proved inline by
  `⟨by simp [Measure.smul_apply, ENNReal.smul_def]; exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩`,
  so bridge 155's witnesses supply it as a named argument, as the order allows.

## Statement stage and its cold review (rule 1, rule 5)

The five modules were written with every statement final, every proof `sorry` and every witness
complete, and each was elaborated with `lake env lean` with only `sorry` warnings
(`stmt-HolmInsideStepUp.out`, `stmt-CorrelationBound.out`, `stmt-PinskerTest.out`,
`stmt-HeunRichardson.out`, `stmt-HeunEulerMaclaurin.out`). Bridge 158's witness first looped in
`simp` (`card_filter` against `sum_boole`); its two `simp [Finset.card_filter, Fin.sum_univ_three]`
became `rw [Finset.card_filter, Fin.sum_univ_three]` before the outputs above were taken. The brief
for the review was built by script (`$HOME/cm5/review/mkbrief.py`, which copies the order's table,
rules 2 and 3 and bridge rows, HANDOFF.md's "Satisfiability witnesses" paragraph, the statements the
bridges rest on from their modules and Mathlib, the five modules and their elaboration outputs;
`review/brief.md`, sha256 `cc678ae580087b33d7049b9f2c69a262886f2419ea5b6eada346bebb1bf45572`). One
fresh subagent reviewed it: `incoming/reviews/review-1.md` (sha256
`b89a78be6dbcc54aa5ba6d7e5f41e34841fed124a3b7815dc8d49cf082c91d9e`), **PASS WITH FINDINGS (7), all
MINOR**:

1. six docstring lines over 100 characters (the `lakefile.toml` linter set, which `lake env lean`
   does not apply, would warn): re-wrapped by a script that keeps code spans whole; the words are
   unchanged (checked by a word diff against the copy before the wrap, 0 changed words);
2. `linter.flexible` on the `simp [...]` before `exact` in CorrelationBound's two witnesses' `hμ`
   proofs: replaced by the `simp only` list the linter gives (plus the lemmas `simp?` gave for the
   last step); the witnesses' arguments did not change;
3. HeunRichardson's helper docstring had a garbled sum: now `∑_{k < n}`;
4. HeunRichardson's module docstring had misplaced backticks in its proof sketch: reworded;
5. HeunRichardson's witness docstring did not say the two Heun runs move at every step: added (the
   reviewer's increments, checked by hand in this session);
6. HeunEulerMaclaurin's theorem-2 witness docstring did not say the iterate moves: added;
7. a stray line break in CorrelationBound's first witness docstring: joined.

No fix changed a statement or a witness's arguments, so no second pass (rule 5). Verdicts: every
statement FAITHFUL; `heunIterate_add_eq_trapezoidal` and `richardson_heunIterate_eq_simpson`
GENERALIZED against the row (no `N ≥ 1`, as the order's table asks). No theorem WEAKER; all seven
witnesses PASS, every numeric claim of their docstrings checked by the reviewer in exact fractions.

## Proofs, by bridge (start times: `start158.txt`, `start155.txt`, `start164.txt`, `start166.txt`, `start167.txt`)

* **158** (from 2026-10-30 21:32:49 UTC): `k = countLE x (x i)`, `1 ≤ k ≤ m`; for `x j ≤ x i` the
  p-values below `x j` lie in `{l | x l ≤ x i}` without `j` (`card_le_card`, `card_erase_of_mem`),
  so `card_filter_add_card_filter_not` gives at least `m − k + 1` p-values at least `x j`; then
  `div_le_div_of_nonneg_left` and `div_le_div_iff₀` with `(k − 1)(m − k) ≥ 0` give `x j ≤ q k / m`;
  `le_numRej` and `thr_mono` finish. Built on the first run, 0 warnings (`build158.txt`).
* **155** (from 21:40:12 UTC): the step of `abs_covariance_le_mul_div_four`, copied
  (`variance_add`, `variance_smul`, `covariance_smul_left`, `discrim_le_zero`, then `nlinarith`);
  the second theorem by `abs_div`, `Real.abs_le_sqrt` and `div_le_one_of_le₀`. The first linted
  build had 2 `linter.flexible` warnings, the review's finding 2; after the fix, 0 warnings
  (`build155.txt`).
* **164** (from 21:48:23 UTC): `φ i (p₁ i − p₀ i) ≤ (|p₁ i − p₀ i| + (p₁ i − p₀ i))/2` cell by
  cell, summed with `∑ p₀ = ∑ p₁ = 1`; then `sq_sum_abs_sub_le_two_mul_relEntropy hp₁ hp₁1 hp₀ hp₀1
  hsupp` and `Real.le_sqrt_of_sq_le`. Built on the first run, 0 warnings (`build164.txt`).
* **166** (from 21:55:28 UTC): the helper `heunIterate_eq_add_sum` by induction; theorem 1 by
  `sum_range_succ` and `sum_range_succ'` on the nodes `a + k h`, with `a + n h + h = b`; theorem 2
  by theorem 1 at `2N` (`push_cast`) and at `N`, and `simpson_eq_trapezoidal`; theorem 3 by
  theorem 2, `add_sub_add_left_eq_sub` and `simpson_error_le`. The first build failed once (the
  node rewrite did not fire because `simp` normalized the cast inside it first; split into two
  `simp only` calls); then 0 warnings (`build166.txt`).
* **167** (from 22:02:57 UTC): theorem 1 by `Int.le.dest` (`b = a + n`) and induction on `n`, with
  `Finset.insert_Icc_right_eq_Icc_add_one` and `Finset.sum_insert`; theorem 2 by theorem 1,
  `sum_eq_integral_add_two` and `ring`. Built on the first run, 0 warnings (`build167.txt`).

No proof forced a statement to change: no narrowing (rule 7). Every bridge closed well inside its
two hours. No helper was flagged, so `tools/vacuity_reviewed.txt` is unchanged.

## Per bridge: the gates before each landing commit

| bridge | module build | witness gate | root build | vacuity gate |
|---|---|---|---|---|
| 158 | 0 warnings (`build158.txt`) | PASS, OK=1, copy-error=0 (`witness158.txt`) | 4197 jobs, 0 warnings (`rootbuild158.txt`) | PASS, 1 reviewed helper (`vacuity158.txt`) |
| 155 | 0 warnings (`build155.txt`) | PASS, OK=2, copy-error=0 (`witness155.txt`) | 4198 jobs, 0 warnings (`rootbuild155.txt`) | PASS, 1 reviewed helper (`vacuity155.txt`) |
| 164 | 0 warnings (`build164.txt`) | PASS, OK=1, copy-error=0 (`witness164.txt`) | 4199 jobs, 0 warnings (`rootbuild164.txt`) | PASS, 1 reviewed helper (`vacuity164.txt`) |
| 166 | 0 warnings (`build166.txt`) | PASS, OK=1, copy-error=0 (`witness166.txt`) | 4200 jobs, 0 warnings (`rootbuild166.txt`) | PASS, 1 reviewed helper (`vacuity166.txt`) |
| 167 | 0 warnings (`build167.txt`) | PASS, OK=2, copy-error=0 (`witness167.txt`) | 4201 jobs, 0 warnings (`rootbuild167.txt`) | PASS, 1 reviewed helper (`vacuity167.txt`) |

The vacuity gate prints a line for a theorem only when it flags one, so its lines for the new
theorems are none: its whole output each time is the summary line `vacuity gate PASS — no vacuous
theorems in [ClassicalLean] (1 reviewed helpers and 0 VACUOUS-PENDING on
tools/vacuity_reviewed.txt); rule 5 ran out of its 400000 heartbeats on 0 theorems`.

## Witnesses (seven, each after its module's last line; all OK in the witness gate)

* `le_mul_numRej_div_of_holmRejected`: `ι = Fin 3`, `x = (1/100, 1/50, 9/10)`, `q = 1/10`, `i = 1`.
  What moves: Holm rejects `i = 1`, not the smallest p-value, so both of Holm's steps are used
  (`1/100 ≤ (1/10)/3`, `1/50 ≤ (1/10)/2`); `numRej = 2`, and the conclusion `1/50 ≤ 2/30` is strict.
  The cards are computed by `Finset.card_filter` and `Fin.sum_univ_three`.
* `covariance_sq_le_variance_mul` and `abs_correlation_le_one`: two fair coins,
  `μ = (4⁻¹ : ℝ≥0) • Measure.count` on `Fin 2 → Bool` (its `IsProbabilityMeasure` proved in the
  block as the named argument `hμ`), `X = ±1` by the first flip, `Y = X + (±1 by the second)`.
  What moves: neither is constant, they are neither independent nor proportional;
  `cov[X, Y] = Var X = 1`, `Var Y = 2`, so `1 ≤ 2` is strict and the correlation `1/√2` lies
  strictly inside `(−1, 1)`, with a nonzero root.
* `size_add_one_sub_power_ge_pinsker`: NeymanPearson's model, `ι = Fin 3`, `p₀ = (1/2, 1/2, 0)`,
  `p₁ = (1/4, 3/4, 0)`, `φ = (0, 1, 0)`. What moves: the laws differ, so `D ≈ 0.131 > 0` and the
  bound `≈ 0.744` is below `1` and below the size plus missed detection `3/4`; the test is not
  constant; the third cell, where both laws vanish, exercises `hsupp`.
* `abs_sub_richardson_heunIterate_le`: `g x = x ^ 4` on `[0, 1]`, derivatives `4 x ^ 3`,
  `12 x ^ 2`, `24 x`, `24`, `M = 24`, `N = 2`, `y₀ = 1`. What moves: both Heun runs move at every
  step (the 2-step run by `1/64`, `17/64`; the 4-step run by `1/2048`, `17/2048`, `97/2048`,
  `337/2048`); `g⁗ ≠ 0`, so Simpson's rule is not exact, and the bound `1/1920` is positive (the
  error attains it, by the reviewer's exact computation).
* `heunIterate_one_eq_add_sum_sub`: `a = 0`, `b = 3`, `g x = x ^ 2`, `y₀ = 1`. What moves: three
  steps, the iterate moving by `1/2`, `5/2`, `13/2`, to `21/2`.
* `sub_heunIterate_eq_eulerMaclaurin`: `g x = x ^ 4` on `[0, 2]`, `g' = 4 x ^ 3`,
  `g'' = 12 x ^ 2`, `y₀ = 1`. What moves: the iterate moves at both steps (by `1/2`, `17/2`, to
  `10`); `g''` is not linear, so the remainder is `1/15 ≠ 0`.

## The modules and their theorem-constant counts

Measured with `$HOME/cm5/count/census.lean`: the axiom gate's predicate (user name under
`ClassicalLean`, no macro scopes, `.thmInfo`), restricted to the constants that `env.getModuleFor?`
places in the module (`count/census.txt`). Measured on the tree at `90898da`, with all five modules
landed and the tree clean.

| module | bridge | theorem constants |
|---|---|---|
| `ClassicalLean/Probability/HolmInsideStepUp.lean` | 158 | 6: 1 written, 1 `_proof_`, 4 `_simp_` |
| `ClassicalLean/Probability/CorrelationBound.lean` | 155 | 2: 2 written |
| `ClassicalLean/Statistics/PinskerTest.lean` | 164 | 1: 1 written |
| `ClassicalLean/Analysis/HeunRichardson.lean` | 166 | 5: 4 written (3 main, 1 helper), 1 `_proof_` |
| `ClassicalLean/Analysis/HeunEulerMaclaurin.lean` | 167 | 4: 2 written, 2 `_proof_` |
| **five modules** | | **18** |

3844 + 18 = 3862, the axiom gate's count below. The import closure went from 5732 to 5737 modules
(`ClassicalLean` from 144 to 149, Mathlib and others 5588 both times; `count/closure_base.txt`,
`count/closure_after.txt`), so no new Mathlib module, and the build has 4196 + 5 = 4201 jobs.

## End check 1 (clean tree at `90898da`, predictions first: `expected.txt`, sha256 `ad7ca6ae…`)

| command | expected | measured |
|---|---|---|
| `lake build` | 4201 jobs, 0 warnings | `Build completed successfully (4201 jobs).`, 0 `warning:` lines (`ec1_build.txt`) |
| `lake env lean tools/AxiomGate.lean` | PASS 3862 | PASS 3862, 0 scoped exceptions (`ec1_axiom.txt`) |
| `python3 -I tools/check_sorry.py` | PASS 148 | PASS 148 (`ec1_sorry.txt`) |
| `python3 -I tools/check_records.py` | PASS 148, 1 exemption | the same (`ec1_records.txt`) |
| `lake env lean tools/VacuityGate.lean` | PASS, 1 reviewed helper | the same, 0 VACUOUS-PENDING, rule 5 out on 0 (`ec1_vacuity.txt`) |
| `python3 -I tools/witness_gate.py` on the five modules | PASS, OK=7, copy-error=0 | the same, every other verdict 0 (`ec1_witness.txt`) |
| `python3 tools/compile_rules.py drift records/rules.toml HANDOFF.md` | PASS no drift | `PASS no drift` (`ec1_drift.txt`) |

**End check 2** (not run here; they run on DSMain at MERGE-5): gate 7, the banned-vocabulary scan,
the whole-library witness gate, the bridge search and the report tool.

**End check 3** (`ec3.txt`): both greps on the five new files find nothing (rc 1). The output of
`git diff --name-only 8631a8d HEAD` lists only the five modules, `ClassicalLean.lean`, `records/`
and `incoming/reviews/review-1.md`; in `ClassicalLean.lean` the diff is only the five added import
lines; under `records/` only `A` (the order's copy, this fragment) and `M` (`INDEX.md`,
`CLAIMS.md`), and those two diffs are one `+` line each, at the end of the file. Every output's
sha256 is in `end_sha256.txt`.

## Commits (branch `cloud-math-5`, each pushed with `git push origin cloud-math-5`)

* `1eb5209` — records first: the order's copy, its INDEX row, the CLAIMS row and this fragment's
  first part.
* `266dd79` — `incoming/reviews/review-1.md`.
* `1a9e0cc` — bridge 158, `ClassicalLean/Probability/HolmInsideStepUp.lean`, and its import line.
* `3d2f4cc` — bridge 155, `ClassicalLean/Probability/CorrelationBound.lean`, and its import line.
* `c1762fd` — bridge 164, `ClassicalLean/Statistics/PinskerTest.lean`, and its import line.
* `6c18194` — bridge 166, `ClassicalLean/Analysis/HeunRichardson.lean`, and its import line.
* `90898da` — bridge 167, `ClassicalLean/Analysis/HeunEulerMaclaurin.lean`, and its import line.
* The commit that carries this section: the CLAIMS row closed and the INDEX row's state. A commit
  cannot cite its own hash.
* Then `incoming/REPORT.md`.

All five bridges are closed: none narrowed, none undone. `master` was not touched.
