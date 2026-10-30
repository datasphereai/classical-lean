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
