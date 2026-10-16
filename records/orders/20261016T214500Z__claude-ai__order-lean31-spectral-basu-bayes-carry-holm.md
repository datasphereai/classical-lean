# LEAN-31 order: batch 5 of the library's second plan (items 101 to 105), and LEAN-30's threads

Written 2026-10-16 by claude-ai for a plain Claude Code session on DSMain, as dustin, after Dustin's
"ready for lean 31" (2026-10-16 13:34 EDT). LEAN-31 comes after LEAN-30, whose last commit `49c4c98`
(`49c4c9833f4f49610ef710aa69531cb84490b6e1`) Dustin pushed to both remotes at 2026-10-16 13:16 EDT
(store rows 20261016-007, the push review; 20261016-010, the push; 20261016-012, the close).
Lane files named here without a folder are in /opt/datasphere/lane/inbox/threads/staging/; files
named `lean/...` are in its subfolder /opt/datasphere/lane/inbox/threads/staging/lean/ (read
`lean/README.md`). Your plan, the report and the push-review file go to `lean/` through
ds_write_staging, since the lane is read-only on disk for you.

**Track the order's steps with the task tools (TaskCreate, TaskUpdate), as Dustin's standing rule
asks** (lane `lean/NOTE-20261015-task-list-rule.md`): lay the jobs out as tasks at the start, mark
each `in_progress` when you start it and `completed` when it is done.

Review: Two passes by one fresh cold reviewer that had not seen it written, reading the order, its
check script, Appendix A, the two carried drafts, LEAN-30's order, the plan's section 5 and 8
excerpts and the earlier closure script in the cloud, with claude-ai's DSMain outputs copied byte
for byte. Pass 1: PASS WITH FINDINGS (0 BLOCKER, 3 MAJOR, 13 MINOR); every finding applied (r1).
Pass 2, the same reviewer: PASS WITH FINDINGS, 14 of pass 1's findings FIXED and 2 PARTLY (rule
10's terms; the dating of the order's own times), and new findings (0 BLOCKER, 1 MAJOR, 8 MINOR);
all applied (r2), which have not had a third review. Not reviewed: anything that needs Lean
beyond the scratch files' own elaboration, the modules' existing rows, check_records, and the
plan's check script's search scope.

It rests on:
- **LEAN-30's close note** (lane `lean/LEAN-30-CLOSE.md`) and claude-ai's push review (lane
  `lean/LEAN-30-review.md`). Their seven threads, and what this order does with each:
  1. the plan's checks, rows E2, H4, H5, K1, K3 (six lines that miss because order CLOUD-MATH-1's
     modules now hold their words): the plan's check script is **not** changed. claude-ai ran it at
     `49c4c98` with the exact list of misses written first, and every miss was predicted (facts);
     Setup 5 predicts the same list line by line;
  2. brief times always with a date: new rule 9 below (filed as HANDOFF.md §6 rule 36), with a
     machine check in your brief builder (Setup 2);
  3. `el.sh` refuses names with no probe line: new rule 10 below (HANDOFF.md §6 rule 37), with the
     check built and tested in Setup 2;
  4. commit messages: rule 8 (HANDOFF.md §6 rule 35, filed by LEAN-30) stands; rule 10's machine
     check removes its commonest cause;
  5. the report's dangling pointer: nothing (the lane report stays as hashed);
  6. the Bloomfield and Watson credit: **checked** by claude-ai on 2026-10-16 against the
     journal's contents page (academic.oup.com, Biometrika volume 62, issue 1, April 1975):
     Peter Bloomfield and Geoffrey S. Watson, "The inefficiency of least squares", pages 121 to
     128. Job 0 says so in the docstring;
  7. the closure script read import lines inside comments: fixed by claude-ai (Appendix A1, with a
     self-test); the fix moved the absolute count, not the prediction (facts, "Imports").
  And the close's deviation 4.1 (rows say "not pushed" after the push): the records commit appends
  LEAN-30's push to its INDEX and CLAIMS rows, and `records/README.md` gains one sentence making
  that the practice (Setup 3).
- **Rows 103 and 104 are carried, not drafted again** (store rows 20261015-010 and -011, Dustin's
  ruling relayed; lane `lean/API-CREDIT-CARRY-1.md`): the drafts `d3103-r1-s1.lean` and
  `d3204-r4-s1.lean` in DSMain's `/data/api-credit/20261015/lean-carry/` (sha256 in "Check, then
  read"). Their statements are this order's statements for items 103 and 104. The carry list's
  other rows (VACUITY-3 rows 7, 8, 9, 10, 31, 32, 67, 70, and plan rows 119 and 120) are not in
  this order.

**Facts at `49c4c98`**, measured on DSMain by claude-ai on 2026-10-16 from 13:42 to 14:54 EDT
(DSMain's `date`), read-only, in `~/lean/classical-lean-paper-crypto` on branch `lean-30` at
`49c4c98` (`git status --porcelain` empty after every run). Outputs saved in
`/tmp/claude-ai-lean31/` on DSMain; the scratch files and the closure script are in Appendix A
with their sha256.

- **The repository.** `git ls-remote origin master` and `git ls-remote github master` both give
  `49c4c9833f4f49610ef710aa69531cb84490b6e1` (claude-ai, after the push). `lean-toolchain` is
  `leanprover/lean4:v4.34.0`; the pinned Mathlib is `5ed2965256430c3649e86755f9576b54eca72435`.
  128 modules under `ClassicalLean/`, 43718 lines.
- **The gates at `49c4c98`**, from LEAN-30's report (gates at `3b293a1`; `49c4c98` changes only
  `records/`, checked by claude-ai's push review): build 4176 jobs, 0 warnings; AxiomGate PASS
  3345; VacuityGate PASS (1 reviewed helper, 0 VACUOUS-PENDING, 0 rule-5 run-outs, no UNCHECKED);
  the gate's tests 89 verdicts, 47 flagged, 3 UNCHECKED as expected, 0 mismatches; check_sorry
  PASS 128; check_records PASS 128; gate 7 ALL PASSED, 4176 jobs, 128 modules 0 failed, 91038
  declarations, three standard axioms, 3345, planted fault named. The report tool: 1848 written
  theorems; section A 1071 (0 close, 1032 open, 39 dependent); section B 777 (16 close); section
  C 34 Prop-valued definitions, 0 recursive.
- **The plan's checks** (MATH-PLAN-library-2-checks.py, `--repo ~/lean/classical-lean-paper-crypto
  --master ~/lean/vacuity2-checks/mm --lean`, under the 12G cap, 2026-10-16 13:42:10 to 13:44:25
  EDT, 2 min 15 s wall, 4377740 KB peak; `checks-lean.out`, sha256
  `022cb0d0189337201c053171ed2f28e240801ca6e2765c2565ec58c60c9889ad`; prediction
  `pred-plan-checks.txt`, sha256 `8846b5a5bedae957b88bd894f4daea744f52b2dc9a8118afa45a070d568a1bd9`,
  written before the run): **174 of 232** hit, rc 1, **as predicted**. The 58 misses are LEAN-30's
  52 of its run `checks0` (`~/lean/lean30-checks/checks0.out`, at `5417d49`) with the same labels,
  plus six new, each predicted: `row.X6`, `row.X8`, `row.X16`, `row.L3` and `row.L7` (both
  searches), whose words LEAN-30's own docstrings now hold. The 58, by label: `setup.modules`
  (128), `setup.worktree` (`49c4c98`), `row.L3`, `row.L7` (two), `row.A2`, `row.A3`, `row.C2`
  (two), `row.C3`, `row.E2`, `row.F4`, `row.F5`, `row.F6`, `row.H4`, `row.H5` (two), `row.H6`,
  `row.K1`, `row.K2`, `row.K3`, `row.X2`, `row.X3` (two), `row.X4`, `row.X6`, `row.X8`, `row.X12`,
  `row.X14`, `row.X15`, `row.X16`, `trackL.L4`, `trackL.L15`, `trackL.L18`, `trackL.L19`,
  `trackL.L2`, the seven `gate.*` lines (`maxUnfolds`, `macro`, `helper`, `metacheck`,
  `test.lim_and_hyp`, `test.lim_false`, `list`), and 15 `--lean` lines: `census.theorems` 3345,
  `census.written` 1848, `census.hyp1` 1138, `census.hyp2` 683, `census.hyp3` 431,
  `census.helpers` 623, `census.derived` (616, 4, 620), `used.lines` 61036, `bridges.modules` 127,
  `bridges.pairs` 2556, `bridges.named`, and the four `bridges.rank` lines.
  - **Every line of rows 101 to 105 hits:** `row.L9` (`spectral density`: 0 in Mathlib pinned and
    master, 0 in the library), `row.L14` (`boundedly complete|bounded completeness`: 0, 0; 1 in the
    library, Sufficiency's docstring), `row.B3` (`holm|bonferroni|familywise error|step-down`: 0,
    0, 0), `trackL.L16` (FiniteGame still assumes `hℓ`), `trackL.L17` (item 5 still assumes
    `q < 1`, item 6 a probability measure), and the plan's exact lines `L9.spectral` and
    `B3.holm`. So neither Mathlib (pinned or master `2da3ab0a`) nor the library has any of the
    five rows.
- **The homes.** At `49c4c98` (sha256 in "Check, then read"):
  - `ClassicalLean.Probability.MovingAverage` (227 lines, namespace `ClassicalLean.Probability`,
    imports only `Mathlib.Probability.Moments.Covariance`): `movingAverage q θ e t ω =
    ∑ j ∈ range (q + 1), θ j * e (t + q - j) ω`; `covariance_movingAverage (he : ∀ t, MemLp (e t)
    2 μ) (hcov : ∀ s t, cov[e s, e t; μ] = if s = t then v else 0) (t k)`: `cov[X (t + k), X t; μ]
    = v * ∑ j ∈ range (q + 1 - k), θ j * θ (j + k)`; one witness, from line 109, a 118-line
    block (white noise on `ℕ` with chances `2^-(n+1)`). `ProbabilityTheory.covariance_self` and
    `variance_nonneg` are **not** visible through its imports (S101's first probes: "Unknown
    identifier"; Mathlib has them in `Probability/Moments/Variance.lean`).
  - `ClassicalLean.Statistics.Sufficiency` (1188 lines, namespace `ClassicalLean.Statistics`):
    `IsSufficient`, `IsComplete` (line 383: every integrable `m`-measurable function with mean
    `0`), `IsAncillary` (line 461), `indep_of_isSufficient_of_isComplete_of_isAncillary` (line
    469, item 58) and `indepFun_of_isComplete_of_ancillary` (line 509); `isComplete_numHeads` and
    `comap_le_of_finite`; the witness of `indepFun_of_isComplete_of_ancillary` (from line 1072: a
    biased coin beside a fair coin). Its Basu bullet says the bounded form is "usually stated"
    (review r58, "not checked against a source") and "this form is narrower in that respect".
  - `ClassicalLean.Analysis.FiniteGame` (867 lines, namespace `ClassicalLean.Analysis`):
    `iSup_bayesRisk_eq_minimaxRisk_of_finite` (line 796) with `(hℓ : ∀ θ y, ℓ θ y ≠ ∞)`; its
    docstring's item 63 bullet (lines 29 to 33) and the hypotheses line "Item 63, `ℓ θ y ≠ ∞`:
    kept; whether it is needed is open" (line 95).
  - `ClassicalLean.Statistics.ResidualVariance` (146 lines, namespace `ClassicalLean.Statistics`),
    `ClassicalLean.Probability.LikelihoodScore` (401 lines, namespace
    `ClassicalLean.Probability.LikelihoodScore`) and `ClassicalLean.Probability.EffectiveSampleSize`
    (640 lines, namespace `ClassicalLean.Probability.EffectiveSampleSize`, imports
    `Mathlib.Probability.Moments.Variance` and two library modules): `integral_residual_sq` (line
    74), `measureReal_sum_ge_le_exp_neg_relEntropy` (line 294), `variance_average_le_of_steady`
    (line 400).
  - `ClassicalLean.Probability.StepUpProcedure` (namespace
    `ClassicalLean.Probability.StepUpProcedure`): the Benjamini–Hochberg step-up procedure
    (`countLE`, `numRej`, `falseShare`, `integral_falseShare_le`). Item 105's new module
    `ClassicalLean.Probability.StepDownProcedure` sits beside it; neither imports the other.
- **The carried drafts elaborate at `49c4c98`** (from the worktree root, rule 20's four flags,
  under the cap, 2026-10-16 13:47:58 EDT): `d3103-r1-s1.lean` rc 0, no `sorry`, **3 warnings**
  (linters: `matrixRisk_mono_loss'` does not use `[Fintype Θ]` in its type; `haveI` where `have`
  will do; a `show` that changes the goal); `d3204-r4-s1.lean` rc 0, no `sorry`, **10 warnings**
  (linters, by line: unused `simp` argument at 135, 141 and 201; at 135 and 195 a `norm_num` that
  does nothing, two warnings each, "never executed" and "does nothing"; at 201 a `<;>` where `;`
  will do; at 146 a line over 100 characters; at 262 a `show` that changes the goal). The build gate
  wants 0 warnings, so landing clears every one (rule 11). Logs `e1-d3103-r1-s1.out` and
  `e1-d3204-r4-s1.out`.
- **Imports, measured.** The import lines this order adds: EffectiveSampleSize gains
  `import Mathlib.Probability.HasLawExists` and
  `import Mathlib.Probability.Distributions.Gaussian.Real` (the carried witness needs them; the
  carry list, point 4); the new module imports `Mathlib.MeasureTheory.Measure.Real`; the root
  `ClassicalLean.lean` gains the new module. A1 (`closure.py`, revised), run from the worktree root
  on 2026-10-16 at 14:38 EDT as
  `python3 -I closure.py ClassicalLean.Probability.StepDownProcedure=Mathlib.MeasureTheory.Measure.Real ClassicalLean.Probability.EffectiveSampleSize=Mathlib.Probability.HasLawExists,Mathlib.Probability.Distributions.Gaussian.Real ClassicalLean=ClassicalLean.Probability.StepDownProcedure`
  (`closure3.out`, the same lines as `closure2.out` of 2026-10-16 14:29 EDT), gives **base closure
  4160, with the additions 4161, added modules 1** (the new module), and no unresolved name (`[]`):
  both Mathlib modules are already in the root's closure (GamblersRuin and JamesStein import them).
  **Lean agrees:** the scratch file `count.lean` (A5: `import ClassicalLean`, then a count of the
  imported modules) printed 5712 modules, 4160 without Init, Std, Lean and Lake, and 129 under
  `ClassicalLean` (the root and its 128), on 2026-10-16 at 14:29 EDT (`count.out`). LEAN-30's A1 on
  the same arguments says base 9037, 9038, added 1. **The two disagree on the size, not on the
  change.** LEAN-30's A1 read `import` lines inside comments and docstrings anywhere in a file (its
  own "unresolved" list held words such as `cycle.` and `diff`), so its absolute count was inflated
  (inferred also from the build: Lake runs a job for each module it builds or replays, and its 4176
  jobs are fewer than 9037). The revision reads only the header, as Lean does, and stops with exit 2
  on a header line it cannot read rather than guess (self-test 8 of 8, including the planted case of
  LEAN-30's close; in the cloud, and on DSMain on 2026-10-16 at 14:37 EDT, `pass2-facts.out`).
  **Inferred: the build after the work is 4177 jobs** (4176 plus the new module).
- **The statements elaborate.** The scratch files S101, S102 and S105 (A2 to A4) hold every new
  statement of items 101, 102 and 105 with `sorry`, the two definitions in full, and a
  `#check @name` probe for every public name their routes below cite. Elaborated from the
  worktree root with rule 20's four flags under the cap (`el.sh` from LEAN-30's folder): first
  drafts on 2026-10-16 at 13:47:58 EDT (S101's probes of `ProbabilityTheory.covariance_self` and
  `variance_nonneg` and S102's of `StronglyMeasurable.max` and `.min` failed: no such names visible;
  S102's of `ae_bdd_condExp_of_ae_bdd` warned: deprecated); final files on 2026-10-16 at 13:49:31
  EDT, and S101 again on 2026-10-16 at 14:29 EDT with two probes added after cold review 1: rc 0
  each, the only warnings `declaration uses sorry`, 2, 2 and 1 of them (one per theorem); about 3 s,
  at most 3291844 KB; every probe printed its type. Items 103 and 104 are the carried drafts above.
- **The exact checks**, `lean/LEAN-31-checks.py` (standard library, `python3 -I`, exact fractions
  under Lean's conventions, no floating point; predictions in its docstring before the first run).
  **21 of 21 checks hit, 7 BY HAND lines, rc 0** (revision 5, after cold review 1); output sha256
  `6df5623ad97e8fd6d115d1df06ea49d4a47700e8b7e136125446dc87afb02238` in the cloud sandbox (Python
  3.13), and the same on DSMain from the lane copy (Python 3.12.3, on 2026-10-16 at 14:33 EDT,
  `checks31r5-dsmain.out`). Two counting misses by claude-ai, both said in the docstring: 24 checks
  predicted (its own list has 21, every one a hit), and 7 BY HAND lines predicted and written into
  revision 1's report line when revisions 1 to 4 printed 6. Revision 5 added a seventh, the
  corollary's `he` row, so 7 is now right.
- **The bridge baseline** `records/bridges/LEAN-30/` (`COMMIT` `4d4ec55`): `pairs.tsv`, 2556
  import-unrelated pairs over N = 127 modules (2558 lines with its two header lines), and
  `shapes.tsv` (609 lines). StepUpProcedure appears in it (rank 9, with Sufficiency). The lane's
  bridges file has moved to `lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md` (the
  lane's own record of the move: `ds_hash` of the old path answers with `moved_to`); sha256
  `0dea55c0…`, the value ruling 20261015-017 accepted; its last row is 157, so a new bridge is row
  158.
- **LEAN-30's numbers**, for the order table, from its report: filed `5417d49`
  2026-10-15T17:27:34Z, closed `49c4c98` 18:41:49Z (1 h 14 min); 19 commits; 128 modules (none
  new); 43718 lines under `ClassicalLean/` (+542); 3345 theorem constants (+10); six gates as
  predicted; Dustin's decisions: the plan approved with three additions (store row 20261015-019),
  the bridges-file fingerprint ruling (20261015-017), and the push.

## Goal

1. **Items 101 to 105** of MATH-PLAN-library-2.md (section 5, "Batch 5"), proved in
   classical-lean under the vacuity gate as LEAN-30 left it, by the plan's per-batch method (its
   section 8), with the statements below. Items 103 and 104 land the carried drafts. Planned
   wider than the plan's reading (claude-ai's ruling, Dustin's veto open), **two conditions**:
   item 105 for any finite measure, not only a probability measure; and item 104's Chernoff bound
   with no `p₀ < 1`, which the unprimed theorem has and the carried one drops (cold review 1;
   `p₀ = 1` forces `q = 1`, where the bound is `1`). Nothing is meant to be narrower. Two
   hypotheses of item 104's Chernoff bound are kept though not needed, because the carried
   statement has them; say so where rule 4 says: `q ≤ 1` (check `104.q_gt_1`), and `0 < p₀` (cold
   review 2, by hand: for `p₀ < 0` the hypotheses cannot hold together, since
   `0 ≤ μ[W (n + 1) | 𝒢 n] ≤ p₀` almost everywhere under a probability measure; for `p₀ = 0` every
   outcome is `0` almost surely, so the event is null when `q > 0` and `N ≥ 1`, and both sides are
   `1` when `q = 0` or `N = 0`, as `relEntropy ![0, 1] ![0, 1] = 0 · log (0 / 0) + 1 · log 1 = 0`
   by the library's definition, `∑ i, p i * log (p i / q i)`, InformationTheory/Entropy line 74).
   LikelihoodScore's docstring already says `0 < p₀` is not claimed needed (its line 43).
2. **Job 0**, the Bloomfield and Watson credit in `ClassicalLean.Statistics.GeneralizedLeastSquares`
   (LEAN-30's thread 6), marked checked.

Dustin pushes after claude-ai checks the result.

The statements, as elaborated in A2 to A4 and in the carried drafts (the plan's section 5 table is
the source for the mathematics; the Lean form is this order's). One new module.

- **101**, in `ClassicalLean.Probability.MovingAverage` (no new import): the spectral density of a
  moving average, finite form, and the plan's "so it is never negative" in real form.

  ```
  theorem sum_covariance_mul_cexp_eq {q : ℕ} {θ : ℕ → ℝ} {e : ℕ → Ω → ℝ} {v : ℝ}
      (he : ∀ t, MemLp (e t) 2 μ) (hcov : ∀ s t, cov[e s, e t; μ] = if s = t then v else 0)
      (t : ℕ) (φ : ℝ) :
      ∑ k ∈ Icc (-(q : ℤ)) q,
          (cov[movingAverage q θ e (t + k.natAbs), movingAverage q θ e t; μ] : ℂ) *
            Complex.exp (-((k : ℂ) * φ * Complex.I))
        = v * Complex.normSq
            (∑ j ∈ range (q + 1), (θ j : ℂ) * Complex.exp ((j : ℂ) * φ * Complex.I))

  theorem zero_le_sum_covariance_mul_cos {q : ℕ} {θ : ℕ → ℝ} {e : ℕ → Ω → ℝ} {v : ℝ}
      (he : ∀ t, MemLp (e t) 2 μ) (hcov : ∀ s t, cov[e s, e t; μ] = if s = t then v else 0)
      (t : ℕ) (φ : ℝ) :
      0 ≤ ∑ k ∈ Icc (-(q : ℤ)) q,
        cov[movingAverage q θ e (t + k.natAbs), movingAverage q θ e t; μ] * Real.cos (k * φ)
  ```

  Both under the module's `[IsFiniteMeasure μ]`. The frequency is `φ` (the module's `ω` is a sample
  point). The second theorem is an addition the plan's sentence asks for ("so it is never
  negative"), not a widening; it needs no `0 ≤ v`, since `v = cov[e 0, e 0; μ] ≥ 0`.

- **102**, in `ClassicalLean.Statistics.Sufficiency`: bounded completeness, that completeness gives
  it, and Basu's theorem with it.

  ```
  def IsBoundedlyComplete (P : Θ → Measure[m₀] Ω) (m : MeasurableSpace Ω) : Prop :=
    ∀ f : Ω → ℝ, StronglyMeasurable[m] f → (∃ C, ∀ ω, |f ω| ≤ C) →
      (∀ θ, ∫ ω, f ω ∂P θ = 0) → ∀ θ, f =ᵐ[P θ] 0

  theorem IsComplete.isBoundedlyComplete {P : Θ → Measure[m₀] Ω} [∀ θ, IsFiniteMeasure (P θ)]
      (hm : m ≤ m₀) (hC : IsComplete P m) : IsBoundedlyComplete P m

  theorem indep_of_isSufficient_of_isBoundedlyComplete_of_isAncillary {β : Type*}
      [MeasurableSpace β] {P : Θ → Measure[m₀] Ω} [∀ θ, IsProbabilityMeasure (P θ)]
      (hS : IsSufficient P m) (hC : IsBoundedlyComplete P m) {A : Ω → β} (hA : Measurable[m₀] A)
      (hanc : IsAncillary P A) (θ : Θ) :
      Indep m (MeasurableSpace.comap A inferInstance) (P θ)
  ```

  "Bounded" is a bound at every point; for a bound holding almost surely under every `P θ` with
  one constant, the function equals a bounded one almost surely under every `P θ` (set it to `0`
  where it exceeds the bound), so the two readings give the same condition. The plan's two names
  are kept; `IsComplete.isBoundedlyComplete` is an addition that shows the new hypothesis is the
  weaker one. `IsSufficient P m` includes `m ≤ m₀` (its definition, Sufficiency line 181: `m ≤ m₀ ∧
  …`), and probability measures are finite, so item 58's theorem follows from the new one through
  `IsComplete.isBoundedlyComplete hS.1 hC`: the new theorem is wider, as the plan says.

- **103**, in `ClassicalLean.Analysis.FiniteGame`: item 63's open point, closed: `hℓ` is not
  needed. The carried statement, unchanged:

  ```
  theorem iSup_bayesRisk_eq_minimaxRisk_of_finite' {Θ 𝓧 𝓨 : Type*} [MeasurableSpace Θ]
      [MeasurableSpace 𝓧] [MeasurableSpace 𝓨] [Finite Θ] [Finite 𝓧] [Finite 𝓨]
      [MeasurableSingletonClass Θ] [MeasurableSingletonClass 𝓧] [MeasurableSingletonClass 𝓨]
      [Nonempty 𝓨] (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) [IsFiniteKernel P] :
      ⨆ (π : Measure Θ) (_ : IsProbabilityMeasure π), bayesRisk ℓ P π = minimaxRisk ℓ P
  ```

  The unprimed theorem stays (callers unchanged; the carry list, point 5).

- **104**, the three optional generalisations of LEAN-17's reviews (r3, r5, r6), each landed in its
  own module beside the theorem it generalises (the carry list, point 4), statements unchanged
  from `d3204-r4-s1.lean`:
  - in ResidualVariance: `integral_residual_sq'`, the mean residual sum of squares
    `σ² (n − p)` under **any** measure (no `[IsProbabilityMeasure μ]`; the noise square-integrable,
    mean `0`, covariances `σ² δᵢⱼ`);
  - in LikelihoodScore: `measureReal_sum_ge_le_exp_neg_relEntropy'`, the relative-entropy Chernoff
    bound for `0 < p₀ ≤ q ≤ 1`, so **`q = 1` included** (there the bound is `p₀ ^ N`). The unprimed
    theorem also has `hp1 : p₀ < 1` (LikelihoodScore line 296); the carried one has no such
    hypothesis, so `p₀ = 1` is allowed too (it forces `q = 1`, and the bound is `1`): the order's
    second widening (Goal 1);
  - in EffectiveSampleSize: `variance_average_le_of_steady'`, with **no**
    `[IsProbabilityMeasure μ]` and no `[IsFiniteMeasure μ]` (the module's line 138; independence of
    the family gives both).
  The unprimed theorems stay. `q ≤ 1` is not needed (for `q > 1` the event is empty once `N ≥ 1`,
  since every `W ≤ 1`, and at `N = 0` both sides are `1`; check `104.q_gt_1`): kept as carried,
  said so (Goal 1); so is `0 < p₀` (Goal 1). The three statements, as the draft has them (namespaces
  aside):

  ```
  theorem integral_residual_sq' {ι κ Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
      [DecidableEq κ] {m0 : MeasurableSpace Ω} {μ : Measure Ω}
      {X : Matrix ι κ ℝ} (hX : IsUnit (Xᵀ * X).det) (β : κ → ℝ)
      {ε : ι → Ω → ℝ} (hε : ∀ i, MemLp (ε i) 2 μ) (hmean : ∀ i, μ[ε i] = 0) {σ : ℝ}
      (hcov : ∀ i j, cov[ε i, ε j; μ] = if i = j then σ ^ 2 else 0) :
      ∫ ω, ∑ i, (residualMaker X *ᵥ (X *ᵥ β + fun i ↦ ε i ω)) i ^ 2 ∂μ =
        σ ^ 2 * (Fintype.card ι - Fintype.card κ)

  theorem measureReal_sum_ge_le_exp_neg_relEntropy' {Ω : Type*} {m0 : MeasurableSpace Ω}
      {μ : Measure Ω} [IsProbabilityMeasure μ] {𝒢 : Filtration ℕ m0} {p₀ q : ℝ}
      {W : ℕ → Ω → ℝ} (hadp : StronglyAdapted 𝒢 W)
      (hW0 : ∀ n ω, 0 ≤ W n ω) (hW1 : ∀ n ω, W n ω ≤ 1)
      (hcond : ∀ n, μ[W (n + 1) | 𝒢 n] ≤ᵐ[μ] fun _ ↦ p₀) (hp0 : 0 < p₀)
      (hq0 : p₀ ≤ q) (hq1 : q ≤ 1) (N : ℕ) :
      μ.real {ω | q * N ≤ ∑ i ∈ range N, W (i + 1) ω} ≤
        Real.exp (-(N * relEntropy ![q, 1 - q] ![p₀, 1 - p₀]))

  theorem variance_average_le_of_steady' {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
      {Z x : ℕ → Ω → ℝ} {a s : ℝ}
      (hZ : ∀ i, Measurable (Z i))
      (hZ2 : ∀ i, MemLp (Z i) 2 μ) (hind : iIndepFun Z μ) (hx0 : x 0 = Z 0)
      (hx : ∀ t ω, x (t + 1) ω = a * x t ω + Z (t + 1) ω) (ha0 : 0 ≤ a) (ha1 : a < 1)
      (hvar : ∀ t, variance (Z (t + 1)) μ = s ^ 2) (hstart : variance (x 0) μ = s ^ 2 / (1 - a ^ 2))
      (n : ℕ) :
      Var[fun ω ↦ (∑ t ∈ range n, x t ω) / n; μ] ≤ s ^ 2 / ((1 - a) ^ 2 * n)
  ```

- **105**, in the new module `ClassicalLean.Probability.StepDownProcedure`: Holm's step-down
  procedure. The definition is complete as A4 elaborates it:

  ```
  def holmRejected (q : ℝ) (x : ι → ℝ) (i : ι) : Prop :=
    ∀ j, x j ≤ x i → x j ≤ q / (univ.filter fun l ↦ x j ≤ x l).card

  theorem measureReal_exists_holmRejected_true_le [IsFiniteMeasure μ] {P : ι → Ω → ℝ}
      {H : Finset ι} {q : ℝ} (hq : 0 ≤ q)
      (hP : ∀ i ∈ H, ∀ u, 0 ≤ u → μ.real {ω | P i ω ≤ u} ≤ u) :
      μ.real {ω | ∃ i ∈ H, holmRejected q (fun j ↦ P j ω) i} ≤ q
  ```

  With `[Fintype ι]`; `H` is the set of true nulls. The definition is Holm's rule without sorting:
  the number of p-values at least `x j` is `m − r + 1` for the first rank `r` that `x j` takes,
  so ties get Holm's strictest threshold, and a tied group is rejected together, as Holm's rule
  does (check `105.sorted`, every vector of up to four p-values on a grid with ties). Validity is
  asked for `u ≥ 0` only (for `u < 0` it would ask a chance to be negative, so the hypothesis could
  never hold). **Wider than the plan's reading** (claude-ai's ruling, Dustin's veto open): any
  finite measure, not only a probability measure; the union bound needs nothing more (check
  `105.fwer` at total mass `2`), and without finiteness it fails (`105.drop.finite`).

No result from below the plan's cut is pulled in.

## Scope

- **Branch.** `lean-31` from `49c4c98` in `~/lean/classical-lean-paper-crypto`, made after Dustin
  approves your plan. Nothing pushed. No sudo.
- **You may change:**
  - the six homes named above (MovingAverage, Sufficiency, FiniteGame, ResidualVariance,
    LikelihoodScore, EffectiveSampleSize), EffectiveSampleSize gaining the two import lines named
    for it and no other module gaining any;
  - the new module `ClassicalLean.Probability.StepDownProcedure`, importing only
    `Mathlib.MeasureTheory.Measure.Real` (or, if a proof needs more, a Mathlib module A1 shows is
    already in the closure, said in the plan or the report), and its import line in
    `ClassicalLean.lean`;
  - for job 0, `ClassicalLean/Statistics/GeneralizedLeastSquares.lean`: docstring and comment
    lines only;
  - `tools/vacuity_reviewed.txt` (job 2's 2c only), `records/` (including `records/README.md`,
    Setup 3), and `HANDOFF.md` and `ROADMAP.md` (job 3);
  - in the lane, through ds_write_staging only: your plan, report and push-review file in `lean/`
    (new files, never overwriting), and, only in job 4a and only for a real bridge, a new section
    at the end of `lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md`.
- **You may not change** anything else under `ClassicalLean/` or `tools/`, or the plan's check
  script in the lane. Needing to is a stop.
- **Off limits:** the main clone's working tree `~/lean/classical-lean` and its `master` (the
  nightly's clone). The worktree shares the main clone's `.git`, so `git fetch`, your branch and
  your commits are written there; that is expected. Also off limits: anything under `~/trading`
  or `~/lean/recheck` (`run-recheck.sh` is run, as gate 7, not edited), and the carried drafts in
  `/data/api-credit/` (read them; copy what you land).
  `~/.config/classical-lean/banned-terms` is Dustin's: never edit it, never copy its patterns.
- **The night window.**
  - Start nothing that loads the library and could still be running at 02:00 EDT.
  - Start nothing that loads the library between 02:00 and 05:45 EDT (the night jobs: cron 02:20
    restic, 03:00 `daily_verify.sh`, 03:30 `datasphere-backup.sh`, user timer 03:30
    `lean-nightly`, cron 05:40 `ds-backup sync.sh`; gate 7 takes about 21 minutes).
  - Do not start a whole-library run in the 15 minutes before the 00:00 `memory-index` timer.
  - Check `crontab -l` and both `systemctl list-timers` lists again before you start.
  - Reading, hash checks and records commits may run inside the window.
  - If a step that loads Lean comes due inside the window, stop and tell Dustin in one line.
  - Every clock time you write in a brief, a prediction or a record carries its date (rule 9).
- **The memory cap.**
  - Every run that loads the whole library goes under
    `systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0 <command>`: a full build, the
    gate, a whole-library census, the plan's checks with `--lean`, A5 (`count.lean`, which imports
    the whole library: 4067964 KB peak in claude-ai's run), the report tool,
    `tools/bridge_search.py` and gate 7.
  - A run the cap kills is a stop.
  - Never run two whole-library runs at once, a reviewer's included.
  - A non-interactive shell on DSMain may lack `~/.elan/bin` in `PATH`; put it there or call
    `~/.elan/bin/lake`.
- **Your plan** goes to `lean/LEAN-31-PLAN.md` (then -PLAN-2, never overwriting). Report its
  sha256.

## Check, then read

Check these sha256s first; if any differs, stop and say which:
- this order, `lean/LEAN-31-order.md`: the value in Dustin's prompt;
- `lean/LEAN-31-checks.py` `0038352f642b79804c03d9da731efd4ac8857ae8ab38c1f0326e3c7f586dc936`;
- MATH-PLAN-library-2.md `6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166`;
- MATH-PLAN-library-2-checks.py `92eedbc6598361a06a50bdf3a1b4fa1698c1d1d7a3dfe783cc79dd9c1c38307e`;
- `lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md`
  `0dea55c0e3c9c2d268fc15650fb2cf0eeb4c567b70e474f1413a94da0f8fb253`;
- `lean/LEAN-30-order.md` `2452e0c6c9635f19b364e16ff315b9f0337450713b9ce8ad4578bb524b94a85d`;
- `lean/LEAN-30-report.md` `0d4321469bc44748af50b2fd4bc3df9bfd7876b948930bae6691d687a5d42e4a`;
- `lean/LEAN-30-review.md` `d0b822f11782867bd5712c9346b7b84e3723a9e922976f940f047943db52cc61`;
- `lean/LEAN-30-CLOSE.md` `14d3771916e7728104e3fca81917109a537a29a883867cb990769420fd6b253c`;
- `lean/API-CREDIT-CARRY-1.md` `0d3e809688be9e1bc25251b338cc9644a7d8a23b65c7872ed017c73da220731d`;
- `lean/VACUITY-3-ruling-3.md` `aa0d17e403031b81d0e0803c3308002ed985b416d788980de0f61cc79e13a4f2`;
- `lean/NOTE-20261015-task-list-rule.md`
  `76cfb510d0023c0c8cb2e843877417c387fe05b92f9ef5dfbe24dc18457194ef`;
- `lean/README.md` `0af69b1afed49098220cbe6b8fe69c9e766bac3054180e319fdae68b7bbbe38c`;
- LEAN-16-order.md `d494728c561a922b1227587395f9650f33dd3182791620e7a0d0fb6469f3120e`;
- the carried drafts, in `/data/api-credit/20261015/lean-carry/` on DSMain:
  - `d3103-r1-s1.lean` `300b8263f9501cea98bb442f7173cf50ac9957761c940a5728f8ac7548093633`;
  - `d3204-r4-s1.lean` `0c25ac775e2c6d233ef0cf1ab140e9faf154958c528bcb759950aea76f945e31`;
- in the repository at `49c4c98`:
  - `ClassicalLean/Probability/MovingAverage.lean`
    `3808723122615ef111036d25cff294b4e5040ee2ffa73a66da35c69443796205`;
  - `ClassicalLean/Statistics/Sufficiency.lean`
    `4158f2992054828fed2f9bcacb57c4a88bf11dbe9755ec8e14a136a59482652e`;
  - `ClassicalLean/Analysis/FiniteGame.lean`
    `9ac45152cbdaa837763a3d27a0f5552644fb4e99b4ec4eae168642ed7cd0631b`;
  - `ClassicalLean/Statistics/ResidualVariance.lean`
    `a66214ed7d655c531197ab034ac54ae86bfb1a73e8f067165a9ba379fc22af71`;
  - `ClassicalLean/Probability/LikelihoodScore.lean`
    `1546ae4849b1565bc682dce0853bdc85981ebed205e182c2b1b1a50412dd51b6`;
  - `ClassicalLean/Probability/EffectiveSampleSize.lean`
    `f8fca70f564a7fd5e0e4450a34477336c5677ca426d21f964f5acf8d66d36239`;
  - `ClassicalLean/Probability/StepUpProcedure.lean`
    `2d876f4de16731cd17afba191f1942c3133fd7caa42003a48f8bcbcc7e8427e3`;
  - `ClassicalLean/Statistics/GeneralizedLeastSquares.lean`
    `da72230d6beaf3734ef512d36b72b17bc1307720f54518773fc2a3cb236d768a`;
  - `ClassicalLean.lean` `5748cab362f32ebb481bc00012c9adce15fc3b31e95da5f6a07b8be54a394d6a`;
  - `HANDOFF.md` `9c6faf97a5f0c8f5bcf2d0c7b478416aec922cad9c123e232b16743e8e8d7647`;
  - `ROADMAP.md` `c9dbd9281ed461f1e6cf3d5d35fd7769faeb95d7034dc9ec45c115cafcff9892`;
  - `records/README.md` `752da4ceb464f0072cabfb5bfc0e5dfee1b381e94522c8acdc657162480d3f61`;
  - `records/orders/INDEX.md` `9de3184e9a0129e085b5bc3101ae755ca4dbd2bae598dddbdcb3b8bf5ba0cbcc`;
  - `records/CLAIMS.md` `fc25be98f38f5c0297cf36cd005453c71ccd74bec0bfb62249b82f0783fa92a6`;
  - `tools/vacuity_reviewed.txt`
    `b5d168d4474375cbba3d5fd29948da316109b4323fa768af433b71df29fa8bde`.

Then read:
- **In the lane:**
  - MATH-PLAN-library-2.md: section 5's "Batch 5" table (items 101 to 105), section 6's rows 101 to
    105, section 7's table header, and section 8 in full;
  - LEAN-30-order.md's sections "Scope", "Rules for this order", "Setup", "Job 2" and "Job 4" (this
    order follows them where it does not say otherwise), and LEAN-30-report.md in full (the
    report's model);
  - LEAN-30-CLOSE.md and LEAN-30-review.md (the seven threads this order answers);
  - API-CREDIT-CARRY-1.md in full (rows 103 and 104, and its points 1 to 7);
  - VACUITY-3-ruling-3.md in full (the witness form and rule 3's two cases);
  - the bridges file (rows 154 to 157);
  - the "Known traps" section of LEAN-16-order.md;
  - `lean/README.md`;
  - `lean/LEAN-31-checks.py`'s docstring (its predictions are this order's exact rows).
- **On DSMain:** the two carried drafts in full.
- **In the repository:** HANDOFF.md §4 and §6 (rules 17, 18, 20, 27, 31 and 35 apply: reviewer
  outputs saved verbatim with their sha256; records follow the clock; scratch files elaborated
  with the lakefile's options; a count Lean generates predicted by a Lean measurement; no
  statement drafted before its searches and cells, which this order and its checks supply; a
  commit message says only what the evidence log shows), records/README.md, round 62's fragment,
  and the sources of the six homes and of StepUpProcedure.

Which steps of the plan's section 8 apply: all of them, with the gates of step 9 as LEAN-30 ran
them (six: build, AxiomGate, VacuityGate, check_sorry, check_records, gate 7) and
`banned_vocab_scan` run beside them as LEAN-30 did (not counted as a gate; only PASS or FAIL and
the count are reported, its output file stays in the evidence folder, never committed, never in
the lane).

## Rules for this order

1. **The gate as LEAN-30 left it** (HANDOFF.md §4). A flag or an UNCHECKED verdict on a main
   theorem is a stop. On a helper: rewrite it, remove it if Mathlib or `simp` already does its
   job, or list it in `tools/vacuity_reviewed.txt` as HELPER with a one-line reason its module's
   cold reviewer checks (2c). A VACUOUS-PENDING entry is a stop. The known gap stays: a recursive
   all-`True` predicate passes silently; each module's cold reviewer checks that no main theorem's
   conclusion is such a predicate and says so, and the report tool's section C after the work
   still shows 0 recursive.
2. **Witnesses, in round 58's standing form as HANDOFF.md §4 files it**: every new main theorem
   with a hypothesis gets an `example` after the module's last line that applies the theorem
   itself, `example := Full.name (x := …) h₁ h₂ …`, every chosen argument by name, optional
   `open … in` lines of their own, the docstring "The hypotheses of `name` hold together: …", no
   `sorry`, `admit`, `native_decide`, `implemented_by`, `axiom` or `set_option`, one inline block
   with no helper declarations; not degenerate (rule 3), with ruling 3's two cases: no hypothesis
   met only because a function is identically `0` past some point, and no kernel or observation
   that fails to depend on the parameter it is about. **Nine witnesses are owed:** both of 101,
   both of 102 (`IsComplete.isBoundedlyComplete` and the Basu theorem), 103, the three of 104,
   and 105.
   **One possible exception, claude-ai's ruling, Dustin's veto open:**
   `variance_average_le_of_steady'` needs an infinite independent family. Mathlib at the pinned
   version has one, `Measure.infinitePi` (`Probability/ProductMeasure.lean`, line 355), found by
   claude-ai's grep after cold review 1 (finding 10), and it is visible from EffectiveSampleSize:
   claude-ai's probe A6 (`P104.lean`, that module's three imports at `49c4c98` plus its two new
   lines) elaborated on 2026-10-16 at 14:54:33 EDT, rc 0, no warning (`e1-P104.out`): it prints
   `Measure.infinitePi`, `iIndepFun_infinitePi` (`Probability/Independence/InfinitePi.lean`, line
   125) and `Measure.infinitePi_map_eval` (`Probability/ProductMeasure.lean`, line 478), and Lean
   finds the instance that `Measure.infinitePi` of probability measures is a probability measure.
   So first try rule 2's form: `Ω = ℕ → ℝ`; `μ = Measure.infinitePi` of the laws the carried
   witness uses, written as it writes them,
   `gaussianReal 0 (if i = 0 then (⟨4 / 3, by norm_num⟩ : NNReal) else 1)`, so that the instance is
   found (`if … then gaussianReal … else gaussianReal …` would not find it); `Z i` the coordinate
   `fun ω ↦ ω i`; `x` by `Nat.rec`, as the carried proof builds it; each coordinate's law from
   `Measure.infinitePi_map_eval` (where the carried proof uses `HasLaw.map_eq`); independence from
   `iIndepFun_infinitePi`; `(n := 3)`; every proof inline, no new import. If it does not close
   within one hour of attempts (Dustin, 2026-10-16), keep the carried witness: one `example` with no helper
   declarations stating that a model exists (Mathlib's `exists_hasLaw_indepFun`) meeting every
   hypothesis, with `0 < variance (x 0) μ` so it is not degenerate, and applying the theorem to it;
   its docstring rewritten to begin "The hypotheses of `variance_average_le_of_steady'` hold
   together: …". Falling back is not a missing witness under rule 7: the first try's hour is
   its own, and rule 7's clock starts only if the carried form fails too. The report says which form
   landed and why. The later order that VACUITY-3's ruling 3 names for rows 9, 10 and 67 decides
   whether library definitions replace such blocks.
3. **A claim in the library is checkable from the library** (store row 20261013-014). No
   docstring or comment in a module says a case was "checked in Lean", "elaborated" or "`#check`
   resolves" unless the check is an `example` in the module. Records, commit messages and the
   report may cite a run, by its evidence label (rule 8). A dropped-hypothesis row's evidence is
   one of: an `example` in the module; a labelled line of `lean/LEAN-31-checks.py` or of your own
   checks script, named by label; or "by hand", said so. A citation checked against a publication
   record says what it was checked against (job 0).
4. **Narrowing and widening are said the same way everywhere.** Before the last records commit,
   the INDEX row, round 63's completed section and the report's "In short" each name every
   narrowing of this order, or say "none", name the two widenings (item 105 for any finite
   measure; item 104's Chernoff bound with no `p₀ < 1`), and say that item 104's `q ≤ 1` and
   `0 < p₀` are kept though not needed. Check it on the report's draft:
   `grep -n -i -E 'narrow|widen|wider|not needed' <round 63 fragment> <report draft>` and
   `grep -n -i -E 'narrow|widen|wider|not needed' records/orders/INDEX.md | grep 'LEAN-31'`; paste
   the output into the report. INDEX rows start `| LEAN-NN |`.
5. **Method A carries LEAN-30's lesson:** its four `field_simp` calls made no helper and Method A
   said 3352 against 3345 (a miss of 7, high), after LEAN-29's miss of 3 low. Count each
   `field_simp` and each `simp` that closes an equation as making 0 to 2 helpers, and give the
   range both ways. The carried drafts are source too: count them by Method A like the rest.
6. **A question to Dustin holds only its own outcome open.** Don't apply your own answer before he
   replies; the work it does not touch goes on.
7. **Stops inside an item.** A witness still missing after about 30 minutes of attempts, or a
   module not clean after two fix-and-confirm review rounds, makes that item not closed: its
   changes are reverted before job 3 and the other items go on. Item 104's three modules are one
   item: if one of them is not clean after two rounds, revert that module's part and report it;
   the other two stand. A finding after the second round that needs a change only inside
   docstrings or comments is fixed, not reverted, as LEAN-29's ruling 1 sets out (a code-only
   comparison with a negative control, a rebuild with 0 warnings, one fresh reviewer on that diff
   alone, reported as "third fix, docstrings only"). Never weaken, restate or add a hypothesis to
   get a witness.
8. **A commit message says only what the evidence log shows** (HANDOFF.md §6 rule 35).
9. **Every clock time carries its date** (new; filed as HANDOFF.md §6 rule 36 in job 3). On
   2026-10-15 LEAN-30's brief builder (`~/lean/lean30-checks/scripts/mkintros.py`, line 67) wrote
   "none after 01:45 EDT" with no date, and four item reviewers read it on 2026-10-15 at 13:53 EDT
   as already past and ran no Lean (LEAN-30's close, thread 2). So: a clock time in a brief, a
   prediction or a record carries its ISO date on the same line (for example
   `2026-10-16T01:45 EDT`, or `2026-10-16 01:45 EDT`), or the text names no clock. Your brief
   builder refuses to write a brief with a line that holds a time, matched by
   `(?<![\d:])\d{1,2}:\d{2}(?!\d)`, and no date `\d{4}-\d{2}-\d{2}` anywhere on that line;
   tested on planted lines (Setup 2): "none after 01:45 EDT" and "none after 1:45pm" refused,
   "none after 2026-10-16 01:45 EDT" and "01:45 EDT on 2026-10-16" written. The copy of this order
   in `records/orders/` is exempt (it is copied verbatim); records you write are not. The night
   window's daily times (Scope) are not copied into a brief: the brief names "the night window in
   the order's Scope" and gives the dated end of its own run (cold review 2).
10. **A name is probed before the text that uses it, and `el.sh` enforces it** (new; filed as
    HANDOFF.md §6 rule 37 in job 3). LEAN-30 used names in drafts before their `#check` probes,
    again (its review r98's MAJOR and others; its close, thread 3). So `el.sh`, **before it runs
    Lean**, reads the text and refuses the run while a name in it is not cleared. It works on the
    text, not on Lean's output, because a name that does not exist never becomes a used constant
    (Lean reports it unknown) and would slip past a check of the elaborated file (cold review 1,
    finding 2). Its terms (cold review 2, finding N1):
    - **The text:** for a scratch draft, the whole file; for a library module, only the lines added
      or changed against `49c4c98` (`git diff -U0 49c4c98 -- <file>`). In both, comments,
      docstrings and string literals are removed first.
    - **The tokens:** the identifiers in that text that contain `.` or `_`.
    - **A token is cleared** when any of these holds: it, or a dot-prefix of it
      (`ENNReal.ofReal_pos` for `ENNReal.ofReal_pos.mpr`), is a full name with a successful
      `#check` line in `evidence.log` or in the seed file; a full name probed so ends in `.` and
      the token (`Finset.sum_le_sum` clears `sum_le_sum` written under `open Finset`); its first
      component is a name the text declares or binds (a hypothesis, or a `have`, `obtain`,
      `intro`, `fun` or `∀` binder: `hq0` clears `hq0.trans_lt`); or it is in the allowlist file
      (tactic names such as `simp_rw` and the like, each entry with a one-line reason, the file
      hashed into `evidence.log` whenever it changes).
    - A token not cleared refuses the run, logged `NOT RUN` with the tokens. Refusing too much is
      safe: a probe clears it.
    - **The seed:** Setup 7's runs are the probes, not subject to the check. Every token in the
      code of A2 to A4, A6 and the two carried drafts (after the same removal) is written to the
      seed file as probed by those runs (rc 0); the file is hashed into the log, and the check
      reads it beside `evidence.log`.
    - **Tested before first use** (Setup 2), on planted drafts: one that names an unprobed Mathlib
      lemma is refused and names it; one that names a lemma that does not exist is refused, and
      its probe fails; one that uses field notation on a local (`h.trans` after `intro h`) is
      accepted; and the first draft runs once its probe succeeds.
11. **The carried drafts land as their statements stand.** Each primed theorem is written with the
    draft's own binders, word for word (its `{Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}`
    and the rest), not with the module's `variable` lines: in Lean 4 a module variable such as
    ResidualVariance's `[IsProbabilityMeasure μ]` (its line 53), EffectiveSampleSize's
    `[IsFiniteMeasure μ]` (its line 138) or LikelihoodScore's `[IsProbabilityMeasure μ]` (its line
    132) is added to a theorem that uses that `μ`, with no error, which would undo r3's or r6's
    point quietly (cold review 1, finding 3). Two checks, both logged. First, the text up to `:=`,
    whitespace normalised, equals the draft's (namespaces aside). Second, Lean's own: in a scratch
    file that imports the landed modules and opens what the draft opens, each draft statement with
    `theorem name'` written `example` and its proof replaced by `Full.name'` applied to its explicit
    arguments in order elaborates, rc 0; an instance the landed theorem needs and the draft does
    not supply makes it fail (cold review 2, finding N6: a printed `#check` can differ for reasons
    that do not matter). Its negative control, in a second scratch file: the same `example` for r3
    with the unprimed `integral_residual_sq` fails, for want of `IsProbabilityMeasure μ`. Proofs
    change only where the module needs it and to clear the linter warnings in the facts (each change
    logged). Docstrings are rewritten in the module's style; the witnesses keep their models (except
    item 103's optional noisy witness, and rule 2's first try for r6) and get rule 2's docstring.
    The unprimed theorems stay.

## Before approval (read-only in the repository)

1. `git fetch origin` in the worktree. Then, each predicted and checked: origin/master and
   `git ls-remote github master` are both `49c4c9833f4f49610ef710aa69531cb84490b6e1`;
   `git show 49c4c98:lean-toolchain` is `leanprover/lean4:v4.34.0` and the Mathlib `rev` in
   `git show 49c4c98:lake-manifest.json` is `5ed2965256430c3649e86755f9576b54eca72435`;
   `git status --porcelain` is empty. If any differs, stop and report.
2. Check the hashes above and read the read list.
3. Check the night jobs and `free -g`.
4. Write your plan to `lean/LEAN-31-PLAN.md`: the jobs in order, every prediction you can already
   make, and the order of the items; and the plan-fit check (HANDOFF.md §6 rule 16): for each of
   items 101 to 105, section 5's row of MATH-PLAN-library-2 beside this order's statement (A2 to
   A4, and the carried statements for 103 and 104), with every difference named and anything else
   you find. At least: the two widenings; item 101's added corollary; item 102's added
   implication; item 104's kept `q ≤ 1` and `0 < p₀`; items 103 and 104 adding primed names and
   keeping the unprimed theorems, where the plan says "restated"; item 105's validity asked for
   `u ≥ 0` only (needed: for `u < 0` no measure meets it; for a probability measure the same as `u`
   in `[0, 1]`; the part `u > 1` is what carries the finite-measure widening); and the method's
   differences carried over from LEAN-30 (reviewers may elaborate two small files, where section 8,
   step 8 says they run no probe; `banned_vocab_scan` runs beside the gates, where step 9 lists it
   among them). And **one row per primed theorem comparing its hypotheses with its unprimed
   theorem's**, read from the module: the carried rows hold only where the primed hypotheses are the
   unprimed ones minus those dropped (cold review 1, finding 11). Dustin's approval of the plan
   closes rule 16's statement review for these statements. Then stop and wait for his approval.

## Setup (after approval)

1. **Branch.** `git switch -c lean-31 49c4c9833f4f49610ef710aa69531cb84490b6e1`.
2. **Evidence folder** `~/lean/lean31-checks/`, with `evidence.log` (date and time, label, rc,
   prediction, command). Every prediction file is hashed into the log before the run it predicts;
   hashes go into records and the report by script, never typed; every compile-fix run through
   `el.sh` is logged; every refused or not-run call is logged `NOT RUN` (HANDOFF.md §6 rule 30).
   Extract Appendix A's six files byte for byte into `~/lean/lean31-checks/appendix/` and check
   their sha256 against the appendix. Copy your helpers from `~/lean/lean30-checks/` and read each
   before use; then **build the two machine checks of rules 9 and 10** into the brief builder and
   `el.sh`, and run each on its planted cases first (rules 9 and 10 list them): the undated lines
   refused and the dated ones written; the unprobed draft refused naming the lemma, the draft
   naming a lemma that does not exist refused with its probe failing, the draft with field notation
   on a local accepted, and the first draft run after its probe. Log each run with its prediction. A
   check that does not behave as predicted is a stop. Then write the seed file of rule 10 after
   Setup 7.
3. **Records first.** The first commit on `lean-31`, with no `.lean` file:
   - this order's copy as
     `records/orders/<UTC>__claude-ai__order-lean31-spectral-basu-bayes-carry-holm.md`;
   - its INDEX row and a CLAIMS row;
   - round 63's fragment, which names in full every module file this order changes, the new
     module's included, and records LEAN-30's push: both remotes at `49c4c98`, re-measured by
     `git ls-remote` before you write it; who and when from store row 20261016-010
     (Dustin, 2026-10-16 13:16 EDT);
   - LEAN-30's INDEX State cell and its CLAIMS row: append
     "; pushed by Dustin to both remotes 2026-10-16 13:16 EDT (`49c4c98`)"
     and change nothing else in them; earlier rows stay as written;
   - `records/README.md`: one sentence where it describes the INDEX (its line "`records/orders/
     INDEX.md` lists every order and its state."), saying that a row records the state when it was
     written and that the next order's records commit appends the push of the order before it.
   check_records then: PASS 128 (the new module does not exist yet).
4. **The before runs, at the records commit**, predicted from the facts:
   - build rc 0, 4176 jobs, 0 warnings;
   - AxiomGate PASS 3345: the base for job 1's blind prediction;
   - the report tool, rc 0: 1848 written; A 1071 (0 / 1032 / 39); B 777 (16 close); C 34, 0
     recursive; saved as `report-before.out` for job 4b.
5. **The plan's checks**, with `--lean`, using `~/lean/vacuity2-checks/mm` (at `2da3ab0a`).
   Predicted: 174 of 232, rc 1, the 58 misses exactly those of the facts (copy the list into your
   prediction file line by line; `setup.worktree`'s measured value will be your records commit),
   and every line of rows 101 to 105 a hit. Only a miss on a row 101 to 105 line means Mathlib or
   the library has that row by now: drop that row and say so. A `setup.*`, `gate.*`, `census.*`,
   `used.*` or `bridges.*` miss never drops a row.
6. **The exact checks:** `python3 -I` on the lane's `lean/LEAN-31-checks.py`. Predicted: 21 of 21
   checks hit, 7 BY HAND lines, rc 0, output sha256
   `6df5623ad97e8fd6d115d1df06ea49d4a47700e8b7e136125446dc87afb02238` (claude-ai's run on DSMain
   from the lane copy gave exactly that). A different output hash with 21 of 21 is reported, not a
   stop.
7. **The statements:** elaborate A2 to A4, A6 and the two carried drafts from the worktree root with
   rule 20's four flags (`lake env lean -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false
   -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3`). Predicted: A2, A3, A4 rc 0
   each with only the warnings `declaration uses sorry`, 2, 2 and 1; A6 rc 0, no warning, its three
   names printed and the instance found; `d3103-r1-s1.lean` rc 0, no
   `sorry`, 3 warnings; `d3204-r4-s1.lean` rc 0, no `sorry`, 10 warnings (facts, by line). These
   six runs are probes, not drafts: rule 10's check does not apply to them, and they seed it. Also
   A5 (`count.lean`), under the cap: predicted to print 4160 modules without Init, Std, Lean and
   Lake.

## The work

Job 0 comes first; it touches no statement. Items 101 to 105 then go through jobs 1 to 4 together.
A suggested order: 103 and 104 (carried, so their proofs exist), 105, 102, 101.

### Job 0: the Bloomfield and Watson credit (LEAN-30's thread 6)

- `ClassicalLean/Statistics/GeneralizedLeastSquares.lean` credits "P. Bloomfield and G. S. Watson,
  "The inefficiency of least squares"" in its module docstring (from line 58) and in the docstring
  of `onesQuad_mul_onesInvOnes_le` (from line 242). Make each credit read: Peter Bloomfield and
  Geoffrey S. Watson, "The inefficiency of least squares", Biometrika 62(1), 121–128 (1975), and
  add, once, in the module docstring's citation sentence: "checked against the journal's contents
  page (Biometrika volume 62, issue 1, April 1975) by claude-ai on 2026-10-16, not by reading the
  paper", in the style of Sufficiency's "What is cited". Any line there that says the credit is
  unchecked or from memory is reworded to match.
- No code changes: a code-only comparison of the file (comments and docstrings stripped) before
  and after, predicted equal, with a negative control (a one-word code change must be detected);
  a rebuild of the module, 0 warnings.
- One fresh cold reviewer reads the diff only, with this section as its brief, about 10 calls; its
  confirming pass closes the job.

### Item 101, `ClassicalLean.Probability.MovingAverage`

- **Route, the identity** (A2 probes every name): rewrite each covariance by
  `covariance_movingAverage he hcov t k.natAbs`. On the right, `Complex.mul_conj` (`z * conj z =
  normSq z`) with the conjugate of the sum term by term (`map_sum`, `Complex.exp_conj`, the
  weights real), and `Finset.sum_mul_sum` with `Complex.exp_add`, give
  `v * ∑ j, ∑ l, θ j * θ l * exp (i (j − l) φ)`. Group that double sum by `d = l − j` (as an
  integer in `Icc (−q) q`, for example `Finset.sum_fiberwise_of_maps_to` or a bijection through
  `Finset.sum_nbij'`): the fibre of `d ≥ 0` is `{(j, j + d) : j < q + 1 − d}`, the fibre of `d < 0`
  is `{(l + |d|, l)}`, and both give `∑_{j < q + 1 − |d|} θ j θ (j + |d|)` against `exp (−i d φ)`.
  Cost S–M; say if the regrouping needs more than about 60 lines.
- **Route, the corollary:** take real parts of the identity (`Complex.re_sum`,
  `Complex.exp_ofReal_mul_I_re`, `Real.cos_neg`, `Complex.re_ofReal_mul`, `Complex.normSq_nonneg`,
  all probed in A2); the right side is `v * normSq …` with
  `0 ≤ v`, since `v = cov[e 0, e 0; μ]` (`hcov 0 0`) and a covariance of a function with itself
  is the integral of a square (unfold `covariance`; `integral_nonneg`, `mul_self_nonneg`).
  Variance lemmas are not visible here (facts); do not add an import for them.
- **Rows:** `hcov`, `101.drop.hcov`, for both theorems (noise correlated at lag 1: the real form is
  `−2 < 0` at `φ = π`, and no `v` matches). `he`, two rows, both by hand:
  - for the identity, the module's own square-integrability row (`q = 1`, `θ = (1, 1)`, `v = 0`:
    the left side `8/9` at every `φ`, the right side `0`). It does **not** break the corollary
    (`0 ≤ 8/9` holds), so it is the identity's row only;
  - for the corollary, cold review 1's case (the BY HAND line `101 (he, corollary)`): `W` a fair
    sign and `Y` independent of it with `P(Y = 2ⁿ) = 2⁻ⁿ`, so `Y` is not integrable; `e 0 = Y`,
    `e 1 = W − Y`, `e 2 = 9W + Y`, `e t = Y` after. Every `e t` and every product `e s · e t` has a
    part in `Y` or `Y²` that is not integrable, so every noise mean and covariance is Lean's `0`
    and `hcov` holds with `v = 0`; with `q = 1`, `θ = (1, 1)`, `t = 0`: `X 0 = W`, `X 1 = 10W`, and
    the real sum at `φ = π` is `1 + 20 cos π = −19 < 0`.
  `[IsFiniteMeasure μ]`: the module's sentence (assumed because Mathlib's covariance algebra assumes
  it; not tested) stays, for both. Junk values: the integral of a non-integrable function is `0`
  (both `he` rows; in the corollary's, twice: the means and the covariances).
- **Exact cases:** `101.identity` (200), `101.model` (60, Walsh white noise), `101.nonneg` (200).
- **Witnesses:** both theorems at the module's existing model (white noise on `ℕ` with chances
  `2^-(n+1)`, from line 109): one inline block each, as rule 2 asks, the existing block's proof of
  `he` and `hcov` copied in. Choose `q = 2`, `θ j = j + 1`, `t = 3` as that witness does, and any
  `φ`, for example `φ = 1`.
- **Docstring:** the list of results gains both theorems; "Mathlib at v4.34.0" gains this order's
  search (`row.L9`, 0 in Mathlib pinned and master).

### Item 102, `ClassicalLean.Statistics.Sufficiency`

- **The definition** `IsBoundedlyComplete` exactly as above, after `IsComplete`.
- **Route, `IsComplete.isBoundedlyComplete`** (A3): a bounded `m`-measurable `f` is integrable
  under each finite `P θ` (`Integrable.of_bound`, with `(hf.mono hm).aestronglyMeasurable`), so
  `hC` applies to it.
- **Route, the Basu theorem:** item 58's proof (line 469), with one change where it calls `hC`:
  replace the common version `g` of `P(B | m)` by `g' = max 0 (min 1 g)`, which is `m`-measurable
  (`StronglyMeasurable.sup`, `.inf`, probed), bounded by `1`, and equal to `g` almost surely under
  every `P θ'`, since `g` is a version of the conditional expectation of an indicator, which lies
  in `[0, 1]` almost surely (`condExp_nonneg`, `condExp_mono` against `condExp_const`, or
  `ae_bdd_abs_condExp_of_ae_bdd_abs`, all probed). Then `g' − c` is bounded by `1 + |c|` and
  `hC` applies to it; the rest is item 58's argument with `g'` for `g`.
- **Rows** (`LEAN-31-checks.py`, exact): `hC`, `102.drop.hC`; `hS`, `102.drop.hS` (LEAN-24's B1
  case); `hanc`, `102.drop.hanc`; `hA`, `102.drop.hA` (the arithmetic) and by hand (the junk `map`
  of a function that is not almost everywhere measurable is the zero measure, so it counts as
  ancillary); the probability measures, `102.drop.prob` (the arithmetic; the case is by hand). For
  `IsComplete.isBoundedlyComplete`, three rows (claude-ai's cases; write each out in the
  docstring's rows):
  - `hC`: the model of `102.drop.hC` (one uniform law on two points, `m` all events): finite, and
    `m ≤ m₀`, but `1_{0} − 1/2` is bounded, `m`-measurable, of mean `0` and not `0`, so neither
    complete nor boundedly complete; the conclusion fails (cold review 1, finding 4);
  - `hm`, by hand: on `Bool` with `m₀` trivial and `m` all sets (LEAN-19's case in the module's
    rows), one probability law. Integrable functions must be almost everywhere `m₀`-measurable, so
    constant (the only null `m₀`-set is empty), and the only one with mean `0` is `0`: `IsComplete`
    holds. The indicator of `true` is bounded and `m`-measurable but not almost everywhere
    `m₀`-measurable, so not integrable, and its Lean integral is `0`; it is not `0` almost surely:
    `IsBoundedlyComplete` fails. Junk value: the integral of a non-integrable function is `0`.
  - the finite measures, by hand: one law, the counting measure on `ℕ` (infinite), `m` trivial. The
    `m`-measurable functions are the constants; the only integrable one is `0`: `IsComplete`
    holds. The constant `1` is bounded, not integrable, so its Lean integral is `0`, and it is not
    `0` almost surely: `IsBoundedlyComplete` fails. The same junk value.
- **Witnesses:** `IsComplete.isBoundedlyComplete` at two coin flips with the number of heads
  (`isComplete_numHeads 2`, `comap_le_of_finite`); the Basu theorem at the module's own Basu model
  (a coin with chance `p` beside a fair coin, from line 1072), its completeness proof turned into
  bounded completeness inside the block.
- **Docstring:** the Basu bullet's "usually stated with the weaker hypothesis of bounded
  completeness (review r58 …), so this form is narrower in that respect" now names the new
  theorem, and keeps "not checked against a source" unless you check it (web search allowed;
  then say what was checked, rule 3). The list of results gains the three names.

### Item 103, `ClassicalLean.Analysis.FiniteGame`

- **Land** `iSup_bayesRisk_eq_minimaxRisk_of_finite'` and its three private lemmas from
  `d3103-r1-s1.lean` after the unprimed theorem (rule 11); clear the draft's three linter
  warnings (facts).
- **Docstring:** the item 63 bullet (lines 29 to 33) says the loss may take the value `∞`, naming
  the new theorem and the truncation argument; line 95 ("kept; whether it is needed is open")
  says it is not needed, by the new theorem, with the case of check `103.noisy` as its example
  (a wrong guess costs `∞`, abstaining costs `1`, a noisy observation; both sides `1`).
- **Rows:** `[Nonempty 𝓨]`, the module's row (by hand); `hℓ`, removed (the theorem is the evidence;
  `103.noisy` and `103.identity` are cases). The finiteness and measurability instances are the
  setting, as in item 63; say "not shown needed" for them, as the module does.
- **Witness:** the carried example (`P = Kernel.id`, loss `0` or `∞`) with rule 2's docstring; or
  the noisy kernel of `103.noisy` (`P θ` puts `3/4` on the observation `θ`), whose value is `1`
  rather than `0`, if it closes within the 30 minutes. Either meets ruling 3: the identity kernel
  depends on the parameter.
- **Mathlib:** `iSup_bayesRisk_le_minimaxRisk` is still Mathlib's only direction (the plan's
  search `trackL.L16`).

### Item 104, ResidualVariance, LikelihoodScore and EffectiveSampleSize

- **Land** the three primed theorems of `d3204-r4-s1.lean`, each in its module's namespace after
  its unprimed theorem (rule 11), and each of the three witnesses after its module's last line;
  EffectiveSampleSize gains its two import lines (facts). Clear the draft's ten linter warnings.
- **Rows:** where a primed theorem's hypotheses are its unprimed theorem's minus those it drops
  (your plan's comparison, one row per theorem), the module's existing rows for the shared
  hypotheses are its rows (cite them by the module's lines). The Chernoff bound drops two
  (`q < 1` becomes `q ≤ 1`, and `p₀ < 1` goes); r3 drops the module's `[IsProbabilityMeasure μ]`
  (ResidualVariance line 53); r6 drops two instance binders, the module's `[IsFiniteMeasure μ]`
  (line 138) and its own `[IsProbabilityMeasure μ]` (cold review 2, finding N6). The new rows:
  `104.r3` (any measure: counting measure of mass `4`), `104.r5` (`q = 1`: the bound is `p₀ ^ N`,
  reached by independent outcomes; the arithmetic of the chances, with Lean's value of `relEntropy`
  at `q = 1`, `1 · log (1 / p₀) + 0 · log (0 / (1 − p₀)) = log (1 / p₀)`, by hand), `104.q_gt_1`
  (`q ≤ 1` not needed, kept), `104.r6` (the witness's numbers) and by hand (independence gives the
  probability measure); `0 < p₀`, the module's sentence (not claimed needed, its line 43) stays,
  with Goal 1's argument that it is not needed. No junk value decides a row: at `q = 1` the second
  term of `relEntropy` is `0 · log (0 / (1 − p₀)) = 0` whatever the logarithm gives (cold review 2).
- **Witnesses:** the carried two for r3 and r5 (rule 2), and for r6 rule 2's first try, or else the
  carried form under rule 2's exception.
- **Docstrings:** each module's list of results gains its primed theorem, and the line that says
  which generalisation LEAN-17's review proved by hand, if there is one, now names it.

### Item 105, the new module `ClassicalLean.Probability.StepDownProcedure`

- **The module:** the copyright header the other modules carry; a module docstring with the
  library's sections (what it proves, "Hypotheses", "What is cited", "Mathlib at v4.34.0"); the
  namespace `ClassicalLean.Probability.StepDownProcedure`, like StepUpProcedure's; the definition
  and theorem as above. Add its import line to `ClassicalLean.lean`.
- **Route** (A4 probes every name): write `h` for the number of true nulls, `H.card`. The event is
  empty when `H` is empty (`0 ≤ q`); otherwise it lies inside `⋃ i ∈ H, {ω | P i ω ≤ q / h}`. For
  `ω` in the event, take `i* ∈ H` with the least p-value over `H` (`Finset.exists_min_image`); it is
  at most the rejected null's, so `holmRejected` gives `x i* ≤ q / c` with `c` the number of
  p-values at least `x i*`;
  every true null's p-value is at least `x i*`, so `H` lies in that set and `h ≤ c`
  (`Finset.card_le_card`), hence `q / c ≤ q / h` (`div_le_div_of_nonneg_left`, with `0 ≤ q`).
  Then `measureReal_mono`, `measureReal_biUnion_finset_le`, `hP` at `u = q / h ≥ 0`, and
  `h · (q / h) = q`.
- **Rows** (exact): `hq`, `105.drop.hq`; `hP`, `105.drop.valid`; `[IsFiniteMeasure μ]`,
  `105.drop.finite` (the arithmetic) and by hand (the counting measure on `ℕ`, where validity
  holds because Lean's real value of an infinite measure is `0`). Junk value: `μ.real` of a set of
  infinite measure is `0` (row finite measure). No junk value enters the definition: the count is
  at least `1` (it counts `j` itself), so no `x / 0` arises.
- **Exact cases:** `105.sorted` (the definition is Holm's rule, ties included), `105.fwer`.
- **Witness:** two equally likely points (`Fin 2`, `uniformOn Set.univ` or `Measure.count`
  scaled), `P 0 = (1/2, 1)` across the two points, `P 1 = 0`, `H = {0}`, `q = 1/2`
  (`105.witness`): `P 0` is valid at every `u ≥ 0`, and the bound is reached (chance `1/2`), so
  the witness is not degenerate.
- **Docstring:** cite S. Holm, "A simple sequentially rejective multiple test procedure",
  Scandinavian Journal of Statistics, 1979, by author, title and year only (not read here); say
  how the definition matches Holm's sorted rule (ties); "Mathlib at v4.34.0": the plan's search
  `row.B3`, 0 in Mathlib pinned and master; and that StepUpProcedure is the Benjamini–Hochberg
  procedure beside it.

### Job 1, predictions (section 8, step 4)

- **The job count:** 4177 (A1: added modules 1, the new module; facts). Confirm by A1 with the
  import lines as you finally write them, before any build, naming the new module on the left of
  an argument with its own imports (a module named only on the right is printed as unresolved and
  not counted: a re-run by claude-ai on 2026-10-16 at 14:37 EDT did that and printed added
  modules 0). The prediction holds only if both lines print `unresolved []`. Use the revised A1;
  LEAN-30's would say 9038 for the same thing (facts).
- **The theorem constants, blind:** Method A from the source (the carried drafts included), then
  Method B by a census of scratch copies, both before any gate; base 3345; rule 5. Job 0 adds none.
- **The bridge diff** before its run (job 4a): no new import edge between library modules
  (EffectiveSampleSize's two lines are Mathlib's), so no listed pair turns related; new pairs of
  the new module with the modules that share its constants, StepUpProcedure likely among the
  first (the two procedures share `Finset.card_filter` and the like). That pair may be a **real
  bridge**: Holm's rejections are a subset of Benjamini–Hochberg's at the same `q`, because Holm's
  threshold at rank `k`, `q / (m − k + 1)`, is at most `q k / m`; if you find it real, it is row
  158 of the bridges file, not this batch. Predict the pairs gone by the document-frequency cut as
  a range, LEAN-30's miss in mind (39 against 0 to 15): count, before the run, the constants of
  your new proofs that `records/bridges/LEAN-30/` shows used by exactly 10 modules.
- **The plan's checks after the work** are not re-run as a gate. If you re-run them, expect the
  library counts of `row.L9`, `row.L14` and `row.B3` to turn into misses as the new docstrings use
  their words. `trackL.L16` and `trackL.L17` may still hit, since the unprimed theorems keep
  `hℓ`, `q < 1` and the probability measure; predict each by grep before any re-run (cold review
  1, finding 12).

### Job 2, statements, hypotheses and reviews (section 8, steps 5 to 8)

Start from A2 to A4 and the carried drafts (the statements are final there unless a review changes
them). With:
- **2a.** Every new main theorem with a hypothesis gets its witness (rule 2), checked by its
  module's cold reviewer against rule 3 with ruling 3's two cases.
- **2b.** Lean's junk values named in every row where they decide the case.
- **2c.** A vacuity flag on a short helper that only restates a definition is not a stop: remove
  it, or list it as HELPER (rule 1). A flag or UNCHECKED on a main theorem, or a VACUOUS-PENDING
  entry, is a stop.
- **2d.** Every review ends with a confirming pass on the fix diff only; at most two
  fix-and-confirm rounds (rule 7). A reviewer may elaborate at most two small Lean files, each
  under `systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=0`, and its brief says until
  when, with the date (rule 9). A witness or a docstring that comes from a reviewer gets its
  confirming pass from a different, fresh reviewer (VACUITY-3's ruling 2). Item 104's three
  modules get one review together; each other module its own. HANDOFF.md §6 rule 16's statement
  review for this order's statements is the cold reviews of the order with your plan's plan-fit
  check, closed by Dustin's approval; a statement you change gets a statement-equivalence review
  before its proof.
- **2e.** A narrower statement than this order's is said plainly in the module docstring, the
  report's item line and the hypothesis table, and rule 4 holds. A row whose statement turns out
  false is reported with its counterexample and narrowed, never dropped silently.
- **2f.** Each new theorem's docstring names the plan's item, and each module docstring's list of
  results gains the new names.

### Job 3, documents

- `HANDOFF.md`: §1, a dated LEAN-31 paragraph with the counts (and the corrected A1: the closure is
  4160 modules at `49c4c98`, not 9037); §6, rules 36 and 37 from rules 9 and 10 above, each with its
  source (LEAN-30's close, threads 2 and 3); the rules' lead-in names them.
- `ROADMAP.md`: batch 5, §1.23, after LEAN-30's §1.22.
- One fresh cold reviewer reads the documents commit's diff alone (about 15 calls): every count
  against its gate or census output, the new rules against rules 9 and 10 here; its confirming pass
  closes the job.

### Job 4, the end checks, in this order

- **4a. The bridge search:** `tools/bridge_search.py --diff records/bridges/LEAN-30/` under the
  cap, on a clean commit of jobs 0 to 3; rc 1 means candidates to review. Report NEW and GONE keys
  against job 1's prediction; check each NEW import-unrelated pair and each NEW shape by hand for a
  theorem whose proof needs both sides; a real one gets row 158 (then 159, …) and goes into the
  lane's `lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md` (ds_write_staging with its
  current sha256 as `expect_sha256`, in a new section after the end of the file, the plan's
  section 7 columns); it never enters this batch. Say for each whether it is load-bearing for a
  scheduled row (items 106 to 110); only that re-draws the cut, at a batch boundary. Write the new
  baseline to `records/bridges/LEAN-31/`; its commit touches only `records/`.
- **4b. The report tool**, under the cap, on the same clean commit: a report, not a gate.
  Predicted from `report-before.out` and job 1; section C: 34 plus the new Prop-valued definitions
  (`IsBoundedlyComplete` and `holmRejected` take values in `Prop`, so 36 is expected), still 0
  recursive. List every `CLOSES` line that names a theorem of this order, for Dustin to read; none
  is expected for a main theorem.
- **4c. Commit everything above. Then the six gates** on the clean tree, predicted first: build rc
  0, 4177 jobs (or job 1's corrected count), 0 warnings; AxiomGate PASS at job 1's count;
  VacuityGate PASS, no new flag (or job 2's listed helpers), 0 VACUOUS-PENDING, 0 run-outs, no
  UNCHECKED, and its tests unchanged (89, 47 flagged, 3 UNCHECKED as expected, 0 mismatches);
  check_sorry PASS 129; check_records PASS 129; gate 7 under the cap
  (`systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0 ~/lean/recheck/run-recheck.sh <commit> ~/lean/classical-lean-paper-crypto`):
  ALL PASSED, 4177 jobs, 129 modules 0 failed, the theorem count, three standard axioms, planted
  fault named. `banned_vocab_scan` beside them, as in "Check, then read". After the gates, only
  commits that touch nothing outside `records/` are allowed.
- **4d. Report** `lean/LEAN-31-report.md` through ds_write_staging, post_sha256 compared with your
  own sha256sum, laid out like LEAN-30-report.md: in short; setup (with the two machine checks and
  their planted cases); job 0; each item with its statements, hypothesis table, witness, review
  and any narrowing or widening; rule 4's grep output; predicted beside measured for jobs,
  constants, the report tool and every gate; list entries with reasons; the bridge diff and the
  baseline; documents changed; commits; misses and not reached; LEAN-30's row of numbers for the
  order table (facts) and this order's own row (filing commit to closing commit in UTC, commits,
  modules, lines under `ClassicalLean/`, theorem constants, Dustin's decisions); the push command
  as one line, not run:
  `cd ~/lean/classical-lean-paper-crypto && git push origin lean-31:master && git push github lean-31:master`.
  Every pointer in the report ("below", "above", a label) points to something that is there.
- **4e. Push-review file** `lean/LEAN-31-push-review.txt` through ds_write_staging, written by one
  script from the repository as it is after the last commit, each command followed by its full
  output: `git rev-parse HEAD`, `git status --porcelain`, `git ls-remote origin master`,
  `git ls-remote github master`, `git merge-base --is-ancestor 49c4c98 HEAD` with its exit code,
  `git rev-list --count 49c4c98..HEAD`, `git log --name-only --format='== %h %cI %s' 49c4c98..HEAD`,
  and `git show` of every commit after the last confirming review, of every commit that touches a
  module after that module's own last confirming pass, and of every commit that touches
  `HANDOFF.md` or `ROADMAP.md` (files under `records/bridges/` as `--stat` only). Report its
  sha256. Then stop. claude-ai reviews it before Dustin pushes.

## Done means

- Branch `lean-31` from `49c4c98`, clean tree, nothing pushed; its first commit is the records
  commit and holds no `.lean` file; every prediction hashed in `evidence.log` before its run;
  hashes in records written by script; `el.sh` runs logged; the jobs tracked with the task tools.
- Rules 9 and 10's machine checks built, each run on its planted case first, as predicted.
- Job 0: the credit reworded as job 0 says, no code changed (the code-only comparison with its
  negative control), its review closed by a confirming pass.
- Items 101 to 105 proved with no `sorry` and no new axiom, as stated here, or each narrowing said
  plainly with its reason; the two widenings (items 105 and 104) and item 104's kept `q ≤ 1` and
  `0 < p₀` said in the module docstrings, the report, the INDEX row and round 63; the carried
  statements equal to the drafts' (rule 11's check); any dropped row named with the line that has
  it; any item not closed after two review rounds reported, its changes reverted.
- Nine witnesses in rule 2's form (at most one under its exception), each checked by its module's
  reviewer against rule 3 with ruling 3's two cases; every hypothesis has a dropped-hypothesis row
  whose evidence is an `example`, a labelled check or "by hand" (rule 3), or is named "not shown
  needed", with Lean's junk values where they decide the case.
- Each changed module had its cold review after its statements were final, ending with a
  confirming pass, and each review answered rule 1's check; any statement changed after its review
  had a statement-equivalence review.
- Every reviewer's and checker's output saved verbatim with its sha256 in the evidence folder
  (HANDOFF.md §6 rule 17), and `~/.claude/agent-memory/` hashed before the first review and after
  the last.
- Every commit message that cites a run names its evidence label (rule 8); every clock time in a
  brief, prediction or record carries its date (rule 9).
- Every new vacuity-list entry named in the report with its reason and its reviewer's check; no
  VACUOUS-PENDING entry and no UNCHECKED verdict in the library.
- The job count and the constant count predicted (blind, before any census) beside measured.
- Job 3's documents changed and named, their review closed by a confirming pass; rule 4's three
  files agree and the grep is in the report; LEAN-30's push appended to its rows and
  `records/README.md`'s sentence added (Setup 3).
- The report tool's run reported (4b).
- All six gates as predicted, or each miss reported; gate 7 ALL PASSED on the last commit that
  touches anything outside `records/`, and later commits touch only `records/`.
- The bridge diff run and reported against its prediction; the new baseline committed and named.
- The report and the push-review file are in `lean/` and their hashes match yours.

Then report in a few plain sentences: what was proved, any narrowing and the two widenings, the gate
results, the new list entries, the two files' hashes and the push command. Dustin reads your
replies carefully and is still learning to read code: use plain words and define a technical term
the first time you use it. When you need a decision from him, ask in one line with your recommended
answer first.

## Not in this order

- Items 106 to 110 (LEAN-32), and rows 154 to 157 of the bridges file.
- The carry list's other rows: VACUITY-3 rows 7, 8, 9, 10, 31, 32, 67 and 70 (the next gate
  order), and plan rows 119 and 120 (Dropped files outside the library, a later order).
- A bridge found in job 4a: the lane's bridges file only.
- Removing `q ≤ 1` and `0 < p₀` from item 104's theorem (`104.q_gt_1` and Goal 1 show they are
  not needed): a later order.
- The plan's check script (its lines 106, 121, 122, 125 and 127, which LEAN-30's thread 1 named):
  not changed;
  its misses are predicted instead.
- Rewriting older INDEX or CLAIMS rows that say "not pushed": only LEAN-30's are amended.
- The main clone, `~/trading`, `~/lean/recheck`, Dustin's `banned-terms` file, and any push.

## Revisions

- r1 (cold review 1, PASS WITH FINDINGS, 0 BLOCKER, 3 MAJOR, 13 MINOR; all applied):
  - MAJOR: item 101's `he` row (`8/9` against `0`) breaks the identity but not the corollary
    (`0 ≤ 8/9` holds); the corollary now has its own row, the reviewer's case (`−19 < 0` at
    `φ = π`), as the BY HAND line `101 (he, corollary)` of the checks (revision 5).
  - MAJOR: rule 10's check read the elaborated draft, which runs the draft it should stop and
    cannot see a name that does not exist; it now reads the text before Lean runs, with an
    allowlist file, seeded by Setup 7's runs (which are probes, not subject to it), and tested
    on an unprobed lemma and on one that does not exist.
  - MAJOR: rule 11 allowed "the module's variables", through which a module's
    `[IsProbabilityMeasure μ]` or `[IsFiniteMeasure μ]` would come back into r3 or r6 silently;
    the draft's binders now land word for word, and `#check @name'` must print the draft's type
    with neither instance in r3's and r6's (the module lines are named: EffectiveSampleSize 138,
    LikelihoodScore 132).
  - MINOR: `IsComplete.isBoundedlyComplete` has an `hC` row; `IsSufficient` includes `m ≤ m₀`
    (Sufficiency, line 181, read by claude-ai), so item 58's theorem is a corollary of the
    new one (facts); the ten warnings of `d3204-r4-s1.lean` are listed by line; rule 9's pattern
    is `(?<![\d:])\d{1,2}:\d{2}(?!\d)`, the date may stand anywhere on the line, the records
    copy of this order is exempt, and the order's own times carry their dates.
  - MINOR: the checks' docstring says revision 1's "7" was copied from the prediction (6 were
    printed); revision 5 adds the seventh line, so the order says 7, from its runs in the cloud
    and on DSMain (`0038352f…`, output `6df5623a…`). `105.drop.hq` now computes its event;
    `102.drop.prob` and `104.r5` are marked as arithmetic, the case by hand.
  - MINOR: the closure script refuses a header line holding `import` that it cannot read (exit
    2, self-test 8 of 8), the facts give its unresolved list (`[]`), and Lean's own count
    (`count.lean`, A5) agrees: 4160.
  - MINOR: rule 2's exception for r6 rested on "no inline infinite family"; claude-ai found
    `Measure.infinitePi` and `iIndepFun_infinitePi` at the pinned Mathlib, so r6 first tries
    rule 2's form, the carried existential form as the fallback, for Dustin's veto.
  - MINOR: the plan-fit list gains the new primed names, item 105's `u ≥ 0`, the method's two
    differences carried from LEAN-30, and one row per primed theorem comparing its hypotheses
    with its unprimed theorem's (which found the second widening: the Chernoff bound drops
    `p₀ < 1` too); job 1 says `trackL.L16` and `trackL.L17` may still hit; rule 11 names item
    103's optional noisy witness; Scope lists the bridges-file write of job 4a.
  - MINOR, wording: dated times; "warnings", not "messages"; `h` for the number of true nulls
    in item 105's route; "Not in this order" says its numbers are line numbers of the plan's
    check script; Setup 3's push is the commit by `ls-remote`, who and when by store row
    20261016-010; item 101's real-part step names `Complex.re_ofReal_mul` and
    `Complex.normSq_nonneg`, probed in A2 (re-elaborated on 2026-10-16 at 14:29 EDT, rc 0).
- r2 (cold review 2, PASS WITH FINDINGS; pass 1: 14 FIXED, 2 PARTLY; new: 0 BLOCKER, 1 MAJOR,
  8 MINOR; all applied):
  - MAJOR: rule 10 did not say which text it scans, which tokens it takes or what clears one; it
    now scans a scratch draft whole and a module's changed lines only, comments and strings
    removed; takes identifiers with `.` or `_`; clears a token by a probed name or dot-prefix, a
    probed name's dot-suffix, a bound local's field notation, or the allowlist; reads the seed
    file beside `evidence.log`; and gains a planted field-notation case.
  - MINOR: item 104's `0 < p₀` is also kept though not needed (the reviewer's argument, by hand,
    checked by claude-ai against the library's `relEntropy`, InformationTheory/Entropy line 74, and
    LikelihoodScore line 43, which already does not claim it needed); no junk value decides at
    `q = 1`.
  - MINOR: r6's first try is specified: claude-ai's probe A6 (`P104.lean`, new) shows the three
    names visible from EffectiveSampleSize's imports and the instance found (2026-10-16 14:54 EDT,
    rc 0); the laws written as the carried witness writes them; `(n := 3)`; falling back is not a
    missing witness under rule 7.
  - MINOR: rule 11's second check is Lean's own (an `example` with the draft's statement and
    `Full.name'` as proof, with a negative control), and it names ResidualVariance line 53; r6's
    plan-fit row shows both instance binders dropped.
  - MINOR: three places still read "the third under rule 2's exception", "one under its exception"
    and "the widening"; A5 runs under the memory cap; job 1's run of 2026-10-16 14:37 EDT is a
    re-run, and both closure lines must print `unresolved []`; the six fact lines whose time and
    date stood apart now share a line, and briefs name the night window instead of copying its daily
    times.
- r3 (Dustin's ruling, 2026-10-16 16:57 EDT): rule 2's first try for r6 gets one hour, not
  30 minutes; nothing else changed.

## Appendix A: the measurement files

Each block below is the file byte for byte, between its fence lines; the file ends with a newline
after its last line. `closure.py` is run from the worktree root with `python3 -I` (its self-test
with `--selftest`); the `.lean` files are elaborated from the worktree root with rule 20's four
flags (A5 with plain `lake env lean`). On DSMain all six are in `/tmp/claude-ai-lean31/app/`.

### A1: `/tmp/claude-ai-lean31/app/closure.py`, the import closure, revised (LEAN-30's close, thread 7)

sha256 `a8c20424dc9e0d504a6d9a011b6fa12f4e33162ac0bcac006a21dcb6a0989a24`

```python
"""Import closure of the classical-lean library, for order LEAN-31's job prediction.

Run from the worktree root: python3 -I closure.py [Module.Name=Extra.Import,...] ...
Each argument adds imports to a module (simulating the order's new import lines); a module named
on the left that does not exist is a new module (its file is not read). Prints the size of the
closure of ClassicalLean.lean (the root) over modules found as source files in the repository or
in .lake/packages/*, core modules (Init, Std, Lean, Lake) excluded, and lists the modules the
additions bring in.

Revision of LEAN-30's A1 (LEAN-30's close, thread 7): imports are read from the file's header
only, as Lean reads them. Block comments (nested `/- ... -/`, docstrings included) and line
comments (`--`) are removed first; then the header is the run of `import` lines (with `public`,
`private`, `meta` or `all` modifiers) and `module`/`prelude` lines at the start, and the first
other line ends it. So an `import` line inside a comment, or anywhere after the header, is not an
import. A header line that holds the word `import` but is not one import of a plain module name
(for example two imports on one line, or a name in guillemets) is not guessed at: the script names
the file and line and exits 2 (cold review 1, finding 9). `python3 -I closure.py --selftest` checks
all this on planted texts and exits 1 on a failure.
"""
import os, re, sys
IMP = re.compile(r'^(?:public\s+)?(?:private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z_][\w.]*)\s*$')
CORE = ('Init', 'Std', 'Lean', 'Lake')


def strip_comments(text):
    """Remove nested block comments and line comments, keeping line breaks."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        two = text[i:i + 2]
        if two == '/-':
            depth += 1
            i += 2
        elif depth and two == '-/':
            depth -= 1
            i += 2
        elif depth:
            if text[i] == '\n':
                out.append('\n')
            i += 1
        elif two == '--':
            j = text.find('\n', i)
            i = n if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)


class HeaderError(Exception):
    pass


def header_imports(text):
    found = []
    for line in strip_comments(text.lstrip('\ufeff')).split('\n'):
        s = line.strip()
        if not s or s in ('module', 'prelude'):
            continue
        m = IMP.match(s)
        if not m:
            if re.search(r'\bimport\b', s):
                raise HeaderError(s)
            break
        found.append(m.group(1))
    return found


def roots():
    pk = '.lake/packages'
    return ['.'] + (sorted(os.path.join(pk, d) for d in os.listdir(pk)) if os.path.isdir(pk) else [])


ROOTS = None


def path_of(mod):
    rel = mod.replace('.', '/') + '.lean'
    for r in ROOTS:
        p = os.path.join(r, rel)
        if os.path.isfile(p):
            return p
    return None


def imports(mod, extra):
    out = list(extra.get(mod, []))
    p = path_of(mod)
    if p is not None:
        with open(p, encoding='utf-8') as fh:
            try:
                out.extend(header_imports(fh.read()))
            except HeaderError as err:
                print('UNREADABLE HEADER LINE in', p, ':', err)
                sys.exit(2)
    return out


def closure(start, extra):
    seen, stack, missing = set(), [start], set()
    while stack:
        m = stack.pop()
        if m in seen or m.split('.')[0] in CORE:
            continue
        if path_of(m) is None and m not in extra:
            missing.add(m)
            continue
        seen.add(m)
        stack.extend(imports(m, extra))
    return seen, missing


def parse(args):
    extra = {}
    for a in args:
        mod, imps = a.split('=', 1)
        extra.setdefault(mod, []).extend(x for x in imps.split(',') if x)
    return extra


def selftest():
    cases = [
        ('LEAN-30 close, thread 7: an import inside a block comment',
         '/-\nimport Fake.Module.FromComment\n-/\nimport Mathlib.Data.Real.Basic\n',
         ['Mathlib.Data.Real.Basic']),
        ('a copyright block, then imports, then a docstring quoting an import',
         '/-\nCopyright\n-/\n\nimport A.B\nimport C\n\n/-!\nimport Not.This\n-/\n',
         ['A.B', 'C']),
        ('a line comment holding an import, and a trailing comment',
         '-- import Fake.One\nimport Real.One -- import Fake.Two\n', ['Real.One']),
        ('nested block comments',
         '/- outer /- inner -/ import Fake.Nested -/\nimport X.Y\n', ['X.Y']),
        ('an import after the first command is not read',
         'import P\nopen Foo\nimport Q\n', ['P']),
        ('modifiers and the module keyword',
         'module\npublic import M.N\nmeta import all K\n', ['M.N', 'K']),
        ('a byte-order mark before the header', '\ufeffimport A\nimport B\n', ['A', 'B']),
        ('two imports on one line are refused, not guessed', 'import A import B\n', 'ERROR'),
    ]
    bad = 0
    for what, text, want in cases:
        try:
            got = header_imports(text)
        except HeaderError:
            got = 'ERROR'
        ok = got == want
        bad += not ok
        print(('OK   ' if ok else 'FAIL ') + what + ': ' + repr(got))
    print('selftest', 'PASS' if not bad else 'FAIL', len(cases) - bad, 'of', len(cases))
    return 1 if bad else 0


if __name__ == '__main__':
    if sys.argv[1:] == ['--selftest']:
        sys.exit(selftest())
    ROOTS = roots()
    base, miss0 = closure('ClassicalLean', {})
    print('base closure', len(base), 'unresolved', sorted(miss0))
    if len(sys.argv) > 1:
        extra = parse(sys.argv[1:])
        new, miss1 = closure('ClassicalLean', extra)
        print('with additions', len(new), 'unresolved', sorted(miss1))
        print('added modules', len(new - base))
        for m in sorted(new - base):
            print('  +', m)
        for mod in extra:
            if path_of(mod) is not None:
                own0, _ = closure(mod, {})
                own1, _ = closure(mod, extra)
                print('module', mod, 'own closure', len(own0), '->', len(own1))
```

### A2: `/tmp/claude-ai-lean31/app/S101.lean`, item 101, statements and probes

sha256 `0b337a77e5ed2e4d82568a4e28adfbf65a8b450d145178cb58b22d1ef71b3e0e`

```lean
import ClassicalLean.Probability.MovingAverage

/-! Order LEAN-31, item 101: statements with `sorry`, and probes. Scratch file, not a module. -/

open MeasureTheory ProbabilityTheory Finset

namespace ClassicalLean.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Item 101: the spectral density of a moving average, finite form. -/
theorem sum_covariance_mul_cexp_eq {q : ℕ} {θ : ℕ → ℝ} {e : ℕ → Ω → ℝ} {v : ℝ}
    (he : ∀ t, MemLp (e t) 2 μ) (hcov : ∀ s t, cov[e s, e t; μ] = if s = t then v else 0)
    (t : ℕ) (φ : ℝ) :
    ∑ k ∈ Icc (-(q : ℤ)) q,
        (cov[movingAverage q θ e (t + k.natAbs), movingAverage q θ e t; μ] : ℂ) *
          Complex.exp (-((k : ℂ) * φ * Complex.I))
      = v * Complex.normSq
          (∑ j ∈ range (q + 1), (θ j : ℂ) * Complex.exp ((j : ℂ) * φ * Complex.I)) := by
  sorry

/-- Item 101, the plan's "so it is never negative", in real form. -/
theorem zero_le_sum_covariance_mul_cos {q : ℕ} {θ : ℕ → ℝ} {e : ℕ → Ω → ℝ} {v : ℝ}
    (he : ∀ t, MemLp (e t) 2 μ) (hcov : ∀ s t, cov[e s, e t; μ] = if s = t then v else 0)
    (t : ℕ) (φ : ℝ) :
    0 ≤ ∑ k ∈ Icc (-(q : ℤ)) q,
      cov[movingAverage q θ e (t + k.natAbs), movingAverage q θ e t; μ] * Real.cos (k * φ) := by
  sorry

end ClassicalLean.Probability

#check @ClassicalLean.Probability.covariance_movingAverage
#check @ClassicalLean.Probability.covariance_movingAverage_eq_zero_of_lt
#check @Complex.normSq_apply
#check @Complex.mul_conj
#check @Complex.normSq_eq_conj_mul_self
#check @Complex.exp_conj
#check @Complex.exp_add
#check @Complex.exp_neg
#check @Complex.exp_ofReal_mul_I_re
#check @Complex.ofReal_cos
#check @Complex.re_sum
#check @Complex.ofReal_sum
#check @map_sum
#check @Finset.sum_mul_sum
#check @Finset.sum_comm
#check @Finset.sum_nbij'
#check @Finset.sum_product
#check @Int.natAbs
#check @ProbabilityTheory.covariance
#check @MeasureTheory.integral_nonneg
#check @mul_self_nonneg
#check @Real.cos_neg
#check @Complex.ofReal_re
#check @Complex.re_ofReal_mul
#check @Complex.normSq_nonneg
#check @MeasureTheory.MemLp.aemeasurable
```

### A3: `/tmp/claude-ai-lean31/app/S102.lean`, item 102, definition, statements and probes

sha256 `29d3e27e6d0784d421de0a945a2862470bfd804cc7ab8826060c8ce740807a57`

```lean
import ClassicalLean.Statistics.Sufficiency

/-! Order LEAN-31, item 102: the definition in full, statements with `sorry`, and probes. Scratch
file, not a module. -/

open MeasureTheory ProbabilityTheory

namespace ClassicalLean.Statistics

variable {Θ Ω : Type*} {m m₀ : MeasurableSpace Ω}

/-- Item 102: bounded completeness. Only the bounded `m`-measurable functions with mean `0` under
every `P θ` must vanish, almost surely under every `P θ`. -/
def IsBoundedlyComplete (P : Θ → Measure[m₀] Ω) (m : MeasurableSpace Ω) : Prop :=
  ∀ f : Ω → ℝ, StronglyMeasurable[m] f → (∃ C, ∀ ω, |f ω| ≤ C) →
    (∀ θ, ∫ ω, f ω ∂P θ = 0) → ∀ θ, f =ᵐ[P θ] 0

/-- Completeness gives bounded completeness, for finite measures and `m ≤ m₀`. -/
theorem IsComplete.isBoundedlyComplete {P : Θ → Measure[m₀] Ω} [∀ θ, IsFiniteMeasure (P θ)]
    (hm : m ≤ m₀) (hC : IsComplete P m) : IsBoundedlyComplete P m := by
  sorry

/-- Item 102: Basu's theorem with bounded completeness. -/
theorem indep_of_isSufficient_of_isBoundedlyComplete_of_isAncillary {β : Type*}
    [MeasurableSpace β] {P : Θ → Measure[m₀] Ω} [∀ θ, IsProbabilityMeasure (P θ)]
    (hS : IsSufficient P m) (hC : IsBoundedlyComplete P m) {A : Ω → β} (hA : Measurable[m₀] A)
    (hanc : IsAncillary P A) (θ : Θ) :
    Indep m (MeasurableSpace.comap A inferInstance) (P θ) := by
  sorry

end ClassicalLean.Statistics

#check @ClassicalLean.Statistics.indep_of_isSufficient_of_isComplete_of_isAncillary
#check @ClassicalLean.Statistics.indepFun_of_isComplete_of_ancillary
#check @ClassicalLean.Statistics.isComplete_numHeads
#check @ClassicalLean.Statistics.comap_le_of_finite
#check @MeasureTheory.Integrable.of_bound
#check @MeasureTheory.StronglyMeasurable.mono
#check @MeasureTheory.condExp_nonneg
#check @MeasureTheory.condExp_mono
#check @MeasureTheory.condExp_const
#check @MeasureTheory.ae_bdd_abs_condExp_of_ae_bdd_abs
#check @MeasureTheory.StronglyMeasurable.sup
#check @MeasureTheory.StronglyMeasurable.inf
#check @MeasureTheory.integral_congr_ae
#check @MeasureTheory.Integrable.congr
#check @MeasureTheory.stronglyMeasurable_const
```

### A4: `/tmp/claude-ai-lean31/app/S105.lean`, item 105, the new module: definition, statement and probes

sha256 `48220825e08198973ce968f56dbe2751cada76b9453df03b9f7399192f303403`

```lean
import Mathlib.MeasureTheory.Measure.Real

/-! Order LEAN-31, item 105, the new module `ClassicalLean.Probability.StepDownProcedure`: the
definition in full, the statement with `sorry`, and probes. Scratch file, not a module. -/

open MeasureTheory Finset

namespace ClassicalLean.Probability

variable {ι : Type*} [Fintype ι]

/-- Item 105: Holm's step-down procedure at level `q`, for the p-values `x`. Hypothesis `i` is
rejected when every p-value `x j` at most `x i` is at most `q` divided by the number of p-values at
least `x j` (ties counted, which is Holm's rule with the p-values sorted). -/
def holmRejected (q : ℝ) (x : ι → ℝ) (i : ι) : Prop :=
  ∀ j, x j ≤ x i → x j ≤ q / (univ.filter fun l ↦ x j ≤ x l).card

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Item 105: Holm's procedure keeps the chance of rejecting any true null at most `q`, under any
dependence, when every true null's p-value is valid. -/
theorem measureReal_exists_holmRejected_true_le [IsFiniteMeasure μ] {P : ι → Ω → ℝ}
    {H : Finset ι} {q : ℝ} (hq : 0 ≤ q)
    (hP : ∀ i ∈ H, ∀ u, 0 ≤ u → μ.real {ω | P i ω ≤ u} ≤ u) :
    μ.real {ω | ∃ i ∈ H, holmRejected q (fun j ↦ P j ω) i} ≤ q := by
  sorry

end ClassicalLean.Probability

#check @MeasureTheory.measureReal_biUnion_finset_le
#check @MeasureTheory.measureReal_mono
#check @MeasureTheory.measureReal_nonneg
#check @Finset.exists_min_image
#check @Finset.card_le_card
#check @Finset.sum_le_card_nsmul
#check @Finset.sum_const
#check @div_le_div_of_nonneg_left
#check @div_le_div_iff_of_pos_left
#check @mul_div_cancel₀
#check @Finset.card_pos
#check @MeasureTheory.measure_biUnion_finset_le
```

### A5: `/tmp/claude-ai-lean31/app/count.lean`, the Lean count of the closure (cold review 1, finding 9)

sha256 `8df1a0638710551b533a4fb7f5c393a826132d3ef8af801bdaa19d7eb293a74e`

```lean
import ClassicalLean

/-! Scratch file for order LEAN-31: the number of modules `ClassicalLean` imports, as Lean counts
them, to cross-check `closure.py` (cold review 1, finding 9). Not a module. -/

open Lean in
#eval show CoreM Unit from do
  let ms := (← getEnv).header.moduleNames
  let core : Array Name := #[`Init, `Std, `Lean, `Lake]
  let rest := ms.filter fun m => !core.contains m.getRoot
  let lib := ms.filter fun m => m.getRoot == `ClassicalLean
  IO.println s!"modules {ms.size}; without Init, Std, Lean, Lake {rest.size}; ClassicalLean {lib.size}"
```

### A6: `/tmp/claude-ai-lean31/app/P104.lean`, the probe for r6's first try (cold review 2, finding N4)

sha256 `bfad6a016311e47c9450e753c9edfe55dd4841557e4e06df01b97c42ded1d06c`

```lean
import Mathlib.Probability.Moments.Variance
import ClassicalLean.Combinatorics.RecurrenceGeneratingFunction
import ClassicalLean.Probability.LinearPrediction
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Order LEAN-31, rule 2's first try for `variance_average_le_of_steady'` (cold review 2, N4):
are the infinite product's names visible from EffectiveSampleSize's own imports plus the two
import lines this order lets it gain? The first three lines are that module's imports at
`49c4c98`; the last two are the carried draft's. -/

open MeasureTheory ProbabilityTheory

#check @Measure.infinitePi
#check @iIndepFun_infinitePi
#check @Measure.infinitePi_map_eval
example {ι : Type*} (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] :
    IsProbabilityMeasure (Measure.infinitePi ν) := inferInstance
#check @gaussianReal
```
