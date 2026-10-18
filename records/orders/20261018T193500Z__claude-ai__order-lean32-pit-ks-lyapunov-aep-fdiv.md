# LEAN-32 order: batch 6 of the library's second plan (items 106 to 110), and LEAN-31's threads

Written 2026-10-18 by claude-ai for a plain Claude Code session on DSMain, as dustin, after Dustin's
"Lean-32 order is go for whenever you feel like writing it" (2026-10-18 13:06 EDT). LEAN-32 comes
after LEAN-31, whose last commit `8071e74` (`8071e74a04761d1ea0bbaac3fcabd7b1e1b6eb31`) Dustin pushed
to both remotes at 2026-10-16 19:39 EDT (lane `lean/LEAN-31-CLOSE.md`, section 1: the reflogs).
Lane files named here without a folder are in /opt/datasphere/lane/inbox/threads/staging/; files
named `lean/...` are in its subfolder /opt/datasphere/lane/inbox/threads/staging/lean/ (read
`lean/README.md`). This order is `lean/LEAN-32/order.md` and its exact checks are
`lean/LEAN-32/scripts/LEAN-32-checks.py`.

**New lane files go through `ds_file`, not `ds_write_staging`** (the lane's layout since
2026-10-16): project `lean`, job `LEAN-32`. Your plan is kind `plan` (it lands as
`lean/LEAN-32/plan.md`; a second one becomes `plan-r2.md`, never overwriting), the report kind
`report`, and the push-review file subdir `data`, name `LEAN-32-push-review.txt`. The reply's
`path` is where the file went; compare its `post_sha256` with your own. Appending to an existing
file (only the bridges file, job 4a) stays `ds_write_staging` in append mode with `expect_sha256`.

**Track the order's steps with the task tools (TaskCreate, TaskUpdate), as Dustin's standing rule
asks** (lane `lean/NOTE-20261015-task-list-rule.md`).

Review: two cold review passes on 2026-10-18 by one fresh reviewer (read-only, in the cloud, with a
read list). Pass 1: PASS WITH FIXES, no BLOCKER, 6 MAJOR and 14 MINOR, all applied in r1. Pass 2 confirmed all 20
fixed and found 3 new MINOR, applied in r2 (see Revisions); r2 itself was not reviewed again. Not reviewed: how
`ds_file` behaves; the hashes of MATH-PLAN-library-2-checks.py, LEAN-16-order.md, VACUITY-3-ruling-3.md and LEAN-31's
helpers (el.sh, probecheck.py, briefcheck.py, mkbrief.py, mkconfirm.py); `checks32-dsmain.out`; the night jobs; LEAN-31's
rules and jobs 1, 2 and 4 in full; HANDOFF.md section 1 and section 4 and ROADMAP.md beyond their headings.

It rests on:
- **LEAN-31's close note** (`lean/LEAN-31-CLOSE.md`), its report (`lean/LEAN-31-report.md`) and
  claude-ai's push review (`lean/LEAN-31/review-1.md`). Their threads, and what this order does with
  each:
  1. **The plan's checks** (close section 3.1): the plan's check script is **not** changed.
     claude-ai ran it at `8071e74` with a prediction written first (facts). Setup 5 predicts its
     62 misses label by label.
  2. **The nightly after the push** (close section 6, first doubt): answered. Line 1 of
     `/opt/datasphere/status/LEAN.md`, written 2026-10-18 03:33 EDT, reads `Lean: OK - 8071e74
     2026-10-16, 1834 theorems written, 3372 constants checked, 0 sorry, 0 axioms (none)` (claude-ai,
     `ds_read` of the status root, 2026-10-18). The nightly pulled the push. Its "1834 theorems
     written" is the nightly's own count, not the report tool's "1861 written theorems" (facts);
     the two tools count differently, and this order predicts only the report tool's.
  3. **A stale root build voided a tool run** (`misses.md` item 23): new rule 12 below (filed as
     HANDOFF.md §6 rule 38), with a machine check built and tested in Setup 2.
  4. **Gone pairs 75 against 5 to 30 predicted** (LEAN-31's report, line 242; `misses.md` item 21
     gives 71, the void run's figure): job 1 predicts them from the used table of a scratch build,
     as that item itself proposes.
  5. **Holes in the rule 10 checker** (`misses.md` items 16 and 18): LEAN-31's final checker is
     carried, and both holes become planted cases (Setup 2).
  6. **Method A low by 14** (`misses.md` item 15): rule 5 below.
  7. **Commit messages cite incomplete run lists** (close section 3.4; `misses.md` items 10 to 14,
     17 and 20): new rule 13 below (HANDOFF.md §6 rule 39), with a machine check in Setup 2.
  8. **Rows say "not pushed" after the push** (close section 4.1): Setup 3 appends LEAN-31's push to
     its INDEX and CLAIMS rows, the practice `records/README.md` now states.
  9. **Gates at `b420ff3`, not `8071e74`** (close section 6): the before-runs at the records commit
     (Setup 4) measure the pushed tree.
- **The anthropics repository review** (lane `server/ANTHROPICS-TAKEUP/notes.md`, rows 1a to 1c),
  checked by claude-ai on 2026-10-18. Row 1a, a per-theorem `#guard_msgs in #print axioms`: the
  library already does better. `tools/AxiomGate.lean`'s docstring says it replaced exactly such
  hand-listed blocks, because they gate only what was listed and reject `rfl` proofs that use no
  axiom; it walks every theorem constant and checks a subset. Row 1c, the exact strength proved
  per result: that is rule 4 below. Row 1b (a second kernel and a statement comparator) is for the
  next gate order. Nothing from the review is in this order.

**Facts at `8071e74`**, measured on DSMain by claude-ai on 2026-10-18 from 13:18 to 13:39 EDT,
with follow-up runs for the cold review on 2026-10-18 from 14:29 to 14:52 EDT (DSMain's `date`), read-only, in `~/lean/classical-lean-paper-crypto` on branch `lean-31` at
`8071e74` (`git status --porcelain` empty after every run). Outputs in `/tmp/claude-ai-lean32/` on
DSMain; the scratch files are Appendix A, with their sha256.

- **The repository.** `git ls-remote origin master` and `git ls-remote github master` both give
  `8071e74a04761d1ea0bbaac3fcabd7b1e1b6eb31` (2026-10-18 13:18:29 EDT). The main clone `~/lean/classical-lean`
  and the worktree are both clean at `8071e74`. 129 modules under `ClassicalLean/`, 44897 lines
  (`find` and `wc`; LEAN-31's report says the same).
- **The gates at `8071e74`**, from LEAN-31's report (gates at `b420ff3`; `8071e74` changes only
  `records/`, its close section 1): build 4177 jobs, 0 warnings; AxiomGate PASS 3372; VacuityGate
  PASS (1 reviewed helper, 0 VACUOUS-PENDING, 0 run-outs, no UNCHECKED); its tests 89 verdicts, 47
  flagged, 3 UNCHECKED as expected, 0 mismatches; check_sorry PASS 129; check_records PASS 129;
  gate 7 ALL PASSED (4177 jobs, 129 modules 0 failed, three standard axioms, 3372). The report
  tool after LEAN-31: 1861 written theorems; section A 1081, section B 780; section C 36 Prop-valued
  definitions, 0 recursive. The nightly's 3372 (thread 2) agrees with AxiomGate's.
- **The plan's checks** (MATH-PLAN-library-2-checks.py, `--repo ~/lean/classical-lean-paper-crypto
  --master ~/lean/vacuity2-checks/mm --lean`, Mathlib master clone at `2da3ab0a`, under the 12G cap,
  2026-10-18 13:27:45 to 13:30:00 EDT, 135.52 s, 4377612 KB peak; `checks-lean.out`, sha256
  `97ed85052c8e41b11d84bdbe92eb2140ede4f9ac1527b52727f8a92b3507ef68`; prediction `pred-pass1.txt`,
  sha256 `4c52893d7c921f4d43353a95b131ab26896b4a345290728cc9df1ceca7fbc8b4`, written before the
  run): **170 of 232** hit, rc 1. claude-ai's prediction said 167 to 172 (hit), named the new
  misses `row.L9`, `row.L14` and `row.B3` (hit: LEAN-31's docstrings now hold their words), and
  wrongly said the exact lines `L9.spectral` and `B3.holm` would miss (they compute; they do not
  read the library, so they still hit), and did not predict `bridges.minquad` (MinimumQuadraticForm
  × GaussMarkov now ranks 62, against "in the top 60"). **The 62 misses** are LEAN-31's 58 labels
  (its order's facts, listed there by label) plus `row.L9`, `row.L14`, `row.B3` and
  `bridges.minquad`; several of the 58 now print new measured values (for example `setup.modules`
  129, `setup.worktree` `8071e74`, `census.theorems` 3372, `census.written` 1861, `used.lines`
  61615, `bridges.modules` 128, `bridges.pairs` 2570).
  - **Every line of rows 106 to 110 hits:** `row.B5` (`probability integral transform`: 0 in
    Mathlib pinned and master, 0 in the library), `row.B6` (`kolmogorov.?smirnov|smirnov`: 0, 0; 1
    in the library, GlivenkoCantelli's docstring, which calls the supremum "the Kolmogorov–Smirnov
    distance"), `row.D2` (`lyapunov`: 0, 0, 0), `row.E4` (`asymptotic equipartition|typical
    set|shannon.?mcmillan`: 0, 0, 0), `row.E6` (`f-divergence|fDivergence|csisz`: pinned 3/2 and
    master 3/2, Mathlib's Kullback–Leibler docstrings; library 0), and the plan's exact lines
    `B5.pit`, `E6.fdiv` and `D2.lyapunov`. So neither Mathlib (pinned or master) nor the library
    has any of the five rows.
- **The homes** (sha256 in "Check, then read"):
  - the new module `ClassicalLean.Probability.IntegralTransform`, importing
    `Mathlib.Probability.CDF` and `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` (the second for
    106's witness: `Real.volume_Icc` is unknown under `Mathlib.Probability.CDF` alone, `e5-S106.out`;
    both are in the root's closure, `closure4.out`);
  - `ClassicalLean.Probability.GlivenkoCantelli` (320 lines, namespace `ClassicalLean.Probability`,
    imports `Mathlib.Probability.StrongLaw` and `Mathlib.Probability.CDF`): `empiricalCDF` (line
    72); `bddAbove_abs_empiricalCDF_sub` (line 249, for a probability measure on `ℝ`);
    `tendsto_sup_abs_empiricalCDF_sub` (line 261, item 60: `hX0`, pairwise independence,
    identical distribution);
  - `ClassicalLean.Analysis.LinearODE` (90 lines, namespace `ClassicalLean.Analysis`, `variable {n
    : Type*} [Fintype n] [DecidableEq n]`): `hasDerivAt_exp_smul_mulVec` (line 55),
    `eq_exp_smul_mulVec` (line 68), one witness;
  - `ClassicalLean.InformationTheory.MethodOfTypes` (270 lines, namespace
    `ClassicalLean.InformationTheory`, imports `ClassicalLean.Probability.RelativeEntropyGrowth` and
    `ClassicalLean.InformationTheory.Entropy`): `variable {α : Type*} [Fintype α] [DecidableEq α]`
    (line 82) and `variable [MeasurableSpace α] [MeasurableSingletonClass α]` (line 115). Through
    its imports Lean does not see `IndepFun`, `IdentDistrib` or `strong_law_ae` (S109's first run:
    "Unknown identifier"), so the module gains `import Mathlib.Probability.StrongLaw`;
  - `ClassicalLean.InformationTheory.Channel` (245 lines, namespace `ClassicalLean.Simplex`, `open
    scoped Matrix`): `relEntropy_vecMul_le` (line 92), with `p, q ≥ 0`, `q i = 0 → p i = 0`, `W ≥ 0`
    and row sums `1`; `shannonEntropy p = -∑ i, p i * Real.log (p i)` is in
    `InformationTheory/Entropy` (line 66).
- **Imports, measured.** LEAN-31's A1 (`~/lean/lean31-checks/appendix/closure.py`, sha256
  `a8c20424dc9e0d504a6d9a011b6fa12f4e33162ac0bcac006a21dcb6a0989a24`), run from the worktree root on
  2026-10-18 at about 13:27 EDT as
  `python3 -I closure.py ClassicalLean.Probability.IntegralTransform=Mathlib.Probability.CDF ClassicalLean.InformationTheory.MethodOfTypes=Mathlib.Probability.StrongLaw ClassicalLean=ClassicalLean.Probability.IntegralTransform`
  (`closure.out`; predicted in `pred-pass1.txt`), gives **base closure 4161, with the additions
  4162, added modules 1** (the new module), `unresolved []` on both lines; MethodOfTypes's own
  closure grows from 3073 to 3092 modules, all already in the root's. Re-run
  on 2026-10-18 at 14:32 EDT with rule 2's imports added (`Mathlib.Probability.HasLawExists` in GlivenkoCantelli and
  in MethodOfTypes; `closure2.out`, prediction `pred-pass2.txt` written first, sha256
  `15bb7ad7f835a76dedbdbd7517a87fe692b69b696b51d816353723a9d783f121`): **the same 4161, 4162 and
  one added module**, `unresolved []` on both lines; MethodOfTypes's own closure 3073 to 3123 and
  GlivenkoCantelli's 2987 to 3060, all already in the root's (HasLawExists is imported by
  EffectiveSampleSize and GamblersRuin). **Inferred: the build after the work is 4178 jobs** (4177
  plus the new module). And `ClassicalLean=Mathlib.Probability.Distributions.Exponential`
  (`closure3.out`, predicted in the same file) adds 2 modules, Exponential and Gamma: Mathlib's
  named laws with a closed-form distribution function are outside the root's closure (rule 2).
  Re-run on 2026-10-18 at 14:50:45 EDT with the new module importing `Mathlib.Probability.CDF` and
  `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` and the other lines as in `closure2.out`
  (`closure4.out`, predicted in `pred-pass4.txt`, sha256
  `71d08eb1f47bfc6f78e1024043080ad81384950fe51541a315351036c5d24b2b`): the same 4161, 4162 and
  one added module, `unresolved []`; its output is byte for byte `closure2.out`'s.
- **The statements elaborate.** S106 to S110 (Appendix A1 to A5) hold every new statement with
  `sorry` and a `#check @name` probe for every public name the routes below cite; SW (A6) holds
  only probes, for rule 2's witnesses. Elaborated from the worktree root with rule 20's four flags
  under the cap: final runs on 2026-10-18 at 13:24:38 EDT (S107, S110), on 2026-10-18 at
  13:25:45 EDT (S108), on 2026-10-18 at 14:30:25 EDT (S109, with two probes added for the cold
  review, `e4-S109.out`; and SW, `e4-SW.out`), and on 2026-10-18 at 14:50:45 EDT (S106, with the
  Lebesgue import and two probes added for the cold review, `e6-S106.out`); rc 0 each; the only warnings `declaration uses
  sorry`, 2, 2, 1, 1 and 1, and none for SW, whose twelve probes all print their types; about 3 s
  each, at most 3337752 KB (`e4-SW.out`). The first runs
  found two things the final files fix: S108 drew the linter warning that `[DecidableEq n]` is not
  used in the statement (fixed by `omit [DecidableEq n] in`) and its probe `Matrix.dotProduct_comm`
  was unknown (the name is `dotProduct_comm`); S109 failed on the three unknown names above, then,
  with the import, drew the same linter warning for `[DecidableEq α]` (fixed the same way). Logs
  `e1-S106.out` to `e1-S110.out`, `e2-S108.out`, `e2-S109.out`, `e3-S109.out` (the run before
  the two added probes), `e4-S109.out`, `e4-SW.out`, `e5-S106.out` (S106 under
  `Mathlib.Probability.CDF` alone: rc 1, `Unknown constant Real.volume_Icc`, against claude-ai's
  prediction in `pred-pass3.txt` that it would print) and `e6-S106.out`.
- **The exact checks**, `lean/LEAN-32/scripts/LEAN-32-checks.py` (standard library, `python3 -I`,
  exact fractions under `x / 0 = 0`, no floating point; predictions in its docstring before the
  first run): **14 of 14 checks hit, 10 BY HAND lines, rc 0**, as predicted; output sha256
  `0336f9dc1366b1e866f712e70a5b5d71a277d479222c4136d150a0cc65365d30` in the cloud sandbox (Python
  3.13.16). The same output on DSMain (Python 3.12.3), from a byte-identical copy in
  `/tmp/claude-ai-lean32/`, on 2026-10-18 at 13:39 EDT (`checks32-dsmain.out`). The docstring's own list names 8 of the 10 BY HAND lines (it leaves out
  `106.eq_uniform` and `110.rel.zero`); the count of 10 it predicts is right.
- **The bridge baseline** `records/bridges/LEAN-31/` (`COMMIT` `6763859`): `pairs.tsv`, 2570
  import-unrelated pairs over N = 128 modules (2572 lines with its two header lines), and
  `shapes.tsv` (620 lines). The lane's bridges file
  `lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md` is sha256 `6e36d49c…` (the value
  LEAN-31's close re-measured); its last row is 158, so a new bridge is row 159.
- **LEAN-31's numbers**, for the order table, from its report: filed `54e7528`
  2026-10-16T21:46:09Z, closed `8071e74` 23:03:07Z (1 h 17 min); 17 commits; 129 modules (one new);
  44897 lines under `ClassicalLean/` (+1179); 3372 theorem constants (+27); six gates as predicted;
  Dustin's decisions: the plan approved with its job 0 proposal, the memory cap (24G, then back to
  12G), and the push (2026-10-16 19:39 EDT).
- **The night jobs**, read 2026-10-18 13:32 EDT (daily times as of 2026-10-18): cron 02:20 restic, 03:00 `daily_verify.sh`, 03:30 `datasphere-backup.sh`, 05:40 `ds-backup sync.sh`;
  user timers (as of 2026-10-18) `memory-index` 00:00, `ds-hygiene` 02:55 (moved from 02:47 by the LAYOUT-HOMES deploy of 2026-10-18), `lean-nightly` 03:30,
  and `w29-sysmap` every 15 minutes (light).

## Goal

1. **Items 106 to 110** of MATH-PLAN-library-2.md (section 5, "Batch 6"), proved in classical-lean
   under the vacuity gate as LEAN-31 left it, by the plan's per-batch method (its section 8), with
   the statements below. **Batch 6 is the plan's last batch above its cut.** Planned wider than the
   plan's reading (claude-ai's ruling, Dustin's veto open), **five conditions**:
   - **107:** the hypothesised distribution function `F₀` is `cdf ν₀` for **any** measure `ν₀` on
     `ℝ` (Mathlib's `cdf_nonneg` and `cdf_le_one` take no instance, so `cdf ν₀` lies in `[0, 1]`
     whatever `ν₀` is), and the first theorem asks no "`F` differs from `F₀`": when they agree the
     supremum is `0` and every `c < 0` lies below the nonnegative supremum of `|F_n − F₀|`. In
     plain words: `cdf ν₀` is still a distribution function for every `ν₀` (`cdf_nonneg`,
     `cdf_le_one`, `tendsto_cdf_atBot`, `tendsto_cdf_atTop` take no instance), so the `F₀` covered
     are the same as for a probability measure; the statement is wider only in that it asks no
     instance;
   - **108:** no positive definiteness of `P`, and no symmetry of `Aᵀ P + P A + 2 c P`: the
     hypothesis is the quadratic-form inequality itself, `v ⬝ᵥ (M *ᵥ v) ≤ 0` for every `v`. The
     derivative of `x ⬝ᵥ P x` along a solution is `x ⬝ᵥ (Aᵀ P + P A) x` for any square `P`
     (`108.P_free`, by hand), so the bound needs nothing more; positive definiteness is what makes
     `x ⬝ᵥ P x` a Lyapunov function (nonnegative, zero only at `0`), and the module docstring says
     so;
   - **109:** the law is given as `μ.real {ω | X 0 ω = a} = p a` for every `a`, which carries
     `p ≥ 0` and `∑ p = 1`, and no measurability beyond what `IdentDistrib` gives (`X 0` is almost
     everywhere measurable by `IdentDistrib.aemeasurable_fst`);
   - **109, again:** pairwise independence only, where the plan's row says "independent draws":
     Mathlib's `strong_law_ae` asks no more (item 107 has the same hypothesis, carried from item
     60);
   - **110:** `q ≥ 0` with `q i = 0 → p i = 0` in place of `q > 0`: the hypothesis form of the
     library's own data-processing theorem, `relEntropy_vecMul_le`, so that relative entropy is the
     case `f x = x log x` with the same hypotheses (checks `110.le`, which includes zero entries of
     `q`, and `110.drop.supp`).
   One addition the plan's sentence asks for: item 107's second theorem, for "a test with
   thresholds `c_n → 0` rejects eventually". Nothing is meant to be narrower.

Dustin pushes after claude-ai checks the result.

The statements, as elaborated in Appendix A (the plan's section 5 table is the source for the
mathematics; the Lean form is this order's). One new module.

- **106**, the new module `ClassicalLean.Probability.IntegralTransform`: the probability integral
  transform. With `[IsProbabilityMeasure μ]`:

  ```
  theorem measureReal_cdf_le_le {X : Ω → ℝ} (hX : Measurable X) {u : ℝ} (hu : 0 ≤ u) :
      μ.real {ω | cdf (μ.map X) (X ω) ≤ u} ≤ u

  theorem measureReal_cdf_le_eq_of_continuous {X : Ω → ℝ} (hX : Measurable X)
      (hF : Continuous (cdf (μ.map X))) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
      μ.real {ω | cdf (μ.map X) (X ω) ≤ u} = u
  ```

  Route: `F = cdf (μ.map X)` is monotone (`StieltjesFunction.mono`), so `{x | F x ≤ u}` is a ray
  `(−∞, a)` or `(−∞, a]`, and its chance under the law (`map_measureReal_apply`, `measure_cdf`,
  `cdf_eq_real`) is `F(a⁻)` or `F(a)`, at most `u`. For the equality, `intermediate_value_univ`
  finds a point where `F` equals `u`; `u = 0` and `u = 1` are the edge cases (the limits
  `tendsto_cdf_atBot` and `tendsto_cdf_atTop`). Rows: `hu` and `hu0` (`106.u_neg`), `hF` (`106.eq_cont`),
  `hu1` (`106.eq_le1`); `hX` and the probability measure are yours to show or to name "not shown
  needed" (rule 3).

- **107**, in `ClassicalLean.Probability.GlivenkoCantelli`: the Kolmogorov–Smirnov test is
  consistent.

  ```
  theorem eventually_lt_sup_abs_empiricalCDF_sub {μ : Measure Ω} [IsProbabilityMeasure μ]
      {X : ℕ → Ω → ℝ} (hX0 : Measurable (X 0))
      (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) μ)
      (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (ν₀ : Measure ℝ) :
      ∀ᵐ ω ∂μ, ∀ c < ⨆ x : ℝ, |cdf (μ.map (X 0)) x - cdf ν₀ x|,
        ∀ᶠ n in atTop, c < ⨆ x : ℝ, |empiricalCDF X n ω x - cdf ν₀ x|

  theorem eventually_lt_sup_abs_empiricalCDF_sub_of_tendsto {μ : Measure Ω}
      [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} (hX0 : Measurable (X 0))
      (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) μ)
      (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (ν₀ : Measure ℝ)
      (hne : ∃ x, cdf (μ.map (X 0)) x ≠ cdf ν₀ x) {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0)) :
      ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, c n < ⨆ x : ℝ, |empiricalCDF X n ω x - cdf ν₀ x|
  ```

  Route: every function here takes values in `[0, 1]` (`empiricalCDF_nonneg`,
  `empiricalCDF_le_one`, `cdf_nonneg`, `cdf_le_one`), so each `⨆` is a true supremum
  (`le_ciSup`, `ciSup_le`; Lean's `⨆ = 0` for an unbounded family never applies, and the module
  docstring already says so for item 60's supremum). By the triangle inequality (`abs_sub_le`),
  `sup |F − F₀| ≤ sup |F_n − F| + sup |F_n − F₀|`, and `tendsto_sup_abs_empiricalCDF_sub` sends
  the middle term to `0` almost surely (`Tendsto.eventually_lt`). For the second theorem, `hne`
  makes `sup |F − F₀| > 0`; apply the first with `c` half of it. Rows: `hne` (`107.drop.hne`), `hc`
  (`107.drop.hc`), independence (`107.drop.indep`), identical distribution (`107.drop.ident`), all
  by hand; `hX0` is item 60's hypothesis, used to name the law, and its row may say "not shown
  needed": item 60's docstring says only `X 0` is assumed measurable, and only to compute its law
  (GlivenkoCantelli, lines 43 and 44).

- **108**, in `ClassicalLean.Analysis.LinearODE`: a Lyapunov bound for `x' = A x`.

  ```
  omit [DecidableEq n] in
  theorem quadForm_le_exp_mul {A P : Matrix n n ℝ} {c : ℝ}
      (hL : ∀ v : n → ℝ, v ⬝ᵥ ((Aᵀ * P + P * A + (2 * c) • P) *ᵥ v) ≤ 0)
      {x : ℝ → n → ℝ} (hx : ∀ t, HasDerivAt x (A *ᵥ x t) t) {t : ℝ} (ht : 0 ≤ t) :
      x t ⬝ᵥ (P *ᵥ x t) ≤ Real.exp (-(2 * c * t)) * (x 0 ⬝ᵥ (P *ᵥ x 0))
  ```

  Route: `V s = x s ⬝ᵥ (P *ᵥ x s)` has derivative `x s ⬝ᵥ ((Aᵀ * P + P * A) *ᵥ x s)`
  (`hasDerivAt_pi`, `HasDerivAt.sum`, `HasDerivAt.mul`, then `Matrix.dotProduct_mulVec`,
  `Matrix.vecMul_transpose`, `Matrix.mulVec_mulVec`, `Matrix.add_mulVec`, `dotProduct_comm`), so
  `g s = Real.exp (2 * c * s) * V s` (`HasDerivAt.exp`) has derivative `Real.exp (2 * c * s)`
  times the left side of `hL` at `x s`, at most `0`; `antitoneOn_of_deriv_nonpos` on `[0, ∞)`
  gives `g t ≤ g 0`, and `Real.exp_pos` divides. Rows: `ht` (`108.drop.t`), `hL` (`108.drop.hL`),
  `hx` (`108.drop.hx`), by hand.

- **109**, in `ClassicalLean.InformationTheory.MethodOfTypes` (gaining
  `import Mathlib.Probability.StrongLaw`): the asymptotic equipartition property.

  ```
  omit [DecidableEq α] in
  theorem tendsto_neg_log_div_shannonEntropy {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] {X : ℕ → Ω → α}
      (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) μ)
      (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) {p : α → ℝ}
      (hlaw : ∀ a, μ.real {ω | X 0 ω = a} = p a) :
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ -(∑ i ∈ range n, Real.log (p (X i ω))) / n) atTop
        (𝓝 (ClassicalLean.Simplex.shannonEntropy p))
  ```

  With the module's `[Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]`. Route: the
  strong law (`strong_law_ae`) for `Y i = g ∘ X i` with `g a = -Real.log (p a)`, measurable as
  every function on a finite type with measurable singletons is (`measurable_of_finite`);
  independence and identical distribution pass through `g` (`IndepFun.comp`,
  `IdentDistrib.comp`); `Y 0` is integrable (`Integrable.of_finite` for `g` on the finite type
  under the law, carried back to `μ` by `Integrable.comp_aemeasurable` or `integrable_map_measure`,
  with `IdentDistrib.aemeasurable_fst`; both probed in `e4-S109.out`); its mean is
  `∑ a, p a * (-Real.log (p a))`
  (`integral_fintype`, `Measure.map_apply_of_aemeasurable`, `hlaw`), which is
  `shannonEntropy p`. Lean's `log 0 = 0` does not matter: a letter with `p a = 0` is drawn with
  chance `0`. Rows: independence, identical distribution and the law, by hand; write them as
  dropped-hypothesis rows with exact small cases where you can. Each case needs a law `p` that is
  not uniform: when `p` is uniform, `-Real.log (p a) = log |α| = H(p)` for every letter, so the conclusion then holds whatever the draws
  are, and no counterexample exists. For the law row, the limit is `-∑ a, q a * Real.log (p a)` for the true law
  `q`, which can equal `H(p)` (with `q = (1, 0)` and `p = (1/2, 1/2)` both are `log 2`), so pick
  the case: `q = (1, 0)` and `p = (1/4, 3/4)` give the limit `log 4` against `H(p) ≈ 0.562`; and
  Lean's `log 0 = 0` makes `p = 0` no counterexample (both sides are `0`). For independence,
  `X i = X 0` for every `i` with `p = (1/4, 3/4)`: the average is `-Real.log (p (X 0 ω))`, which is
  `log 4` or `log (4/3)`, never `H(p)`.

- **110**, in `ClassicalLean.InformationTheory.Channel`: data processing for every
  f-divergence on finite sets.

  ```
  theorem sum_mul_comp_div_vecMul_le {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici 0) f)
      {p q : ι → ℝ} {W : Matrix ι κ ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
      (hpq : ∀ i, q i = 0 → p i = 0) (hW0 : ∀ i j, 0 ≤ W i j) (hW1 : ∀ i, ∑ j, W i j = 1) :
      ∑ j, (q ᵥ* W) j * f ((p ᵥ* W) j / (q ᵥ* W) j) ≤ ∑ i, q i * f (p i / q i)
  ```

  Route: column by column, Jensen (`ConvexOn.map_sum_le`) with weights `q i * W i j / (q ᵥ* W) j`
  over the `i` with `q i * W i j ≠ 0` (`Finset.sum_filter`), whose weighted mean of `p i / q i` is
  `(p ᵥ* W) j / (q ᵥ* W) j`; then swap the sums (`Finset.sum_comm`, `Matrix.vecMul_apply_eq_sum`,
  `Finset.mul_sum`, `Finset.sum_mul`) and use the row sums. A column with `(q ᵥ* W) j = 0` gives
  `0 * f 0 = 0` on the left under `x / 0 = 0` (`110.qW0`). Rows: `hf` (`110.drop.conv`), `hp`
  (`110.drop.p`), `hq` (`110.drop.q`), `hpq` (`110.drop.supp`), `hW0` (`110.drop.W0`), `hW1`
  (`110.drop.W1`). The module docstring names relative entropy as the case `f x = x log x`
  (`110.rel` checks only the algebra `q · (p / q) = p` for `q ≠ 0`; `110.rel.zero`, by hand, the
  case `q = 0 = p`) and says that `relEntropy_vecMul_le` stays as it is.

No result from below the plan's cut is pulled in.

## Scope

- **Branch.** `lean-32` from `8071e74` in `~/lean/classical-lean-paper-crypto`, made after Dustin
  approves your plan. Nothing pushed. No sudo.
- **You may change:**
  - the four homes named above (GlivenkoCantelli, LinearODE, MethodOfTypes, Channel), MethodOfTypes
    gaining `import Mathlib.Probability.StrongLaw`, GlivenkoCantelli and MethodOfTypes each gaining
    `import Mathlib.Probability.HasLawExists` for rule 2's witnesses (already in the root's closure;
    facts, `closure2.out`), and no other module gaining an import;
  - the new module `ClassicalLean.Probability.IntegralTransform`, importing
    `Mathlib.Probability.CDF` and `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` (or, if a proof
    needs more, a Mathlib module LEAN-31's A1 (`closure.py`) shows is already in the root's closure,
    said in the plan or the report), and its import line in `ClassicalLean.lean`;
  - `tools/vacuity_reviewed.txt` (job 2's 2c only), `records/`, and `HANDOFF.md` and `ROADMAP.md`
    (job 3);
  - in the lane: the three new files above through `ds_file`, and, only in job 4a and only for a
    real bridge, a new section at the end of the bridges file through `ds_write_staging` (append,
    `expect_sha256` its current value).
- **You may not change** anything else under `ClassicalLean/` or `tools/`, the plan's check
  script, or this order's check script. Needing to is a stop.
- **Off limits, the night window and the memory cap:** LEAN-31's Scope (lane
  `lean/LEAN-31-order.md`, section "Scope", its bullets "Off limits", "The night window" and "The
  memory cap", the fourth to sixth of its seven; its last bullet, "Your plan", is replaced here by
  `ds_file` above) applies word for word, with one change: the hygiene timer now runs at 02:55 EDT daily (as of 2026-10-18).
  Check `crontab -l` and both `systemctl list-timers` lists again before you start.

## Check, then read

Check these sha256s first; if any differs, stop and say which:
- this order, `lean/LEAN-32/order.md`: the value in Dustin's prompt;
- `lean/LEAN-32/scripts/LEAN-32-checks.py`
  `3cd2c30e341f6993346450f8fe936914a10133825e1d5d87695cb2718b1b7870`;
- MATH-PLAN-library-2.md `6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166`;
- MATH-PLAN-library-2-checks.py `92eedbc6598361a06a50bdf3a1b4fa1698c1d1d7a3dfe783cc79dd9c1c38307e`;
- `lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md`
  `6e36d49c5121ba21986a34edb1a0c2962489d2ef3e6f7b0038abab0e76f06721`;
- `lean/LEAN-31-order.md` `9a0df0902bab8de2d80bb2a59c872bb39b74b6657dbf1129466e5e7cfebc1242`;
- `lean/LEAN-31-report.md` `e2d18d6b6de0beb00e84c4f4e922533e3bbde9bf6a629e14f9e51339907b0797`;
- `lean/LEAN-31-CLOSE.md` `a1557bb24ef9603a255bf88608092389af50e77de11dc3557db8de7cc9aa2b26`;
- `lean/LEAN-31/review-1.md` `75fcc1e9eff0f3071fb6cdd572ad2222a462da2446321873c59e08835f3617f0`;
- `lean/VACUITY-3-ruling-3.md` `aa0d17e403031b81d0e0803c3308002ed985b416d788980de0f61cc79e13a4f2`;
- `lean/NOTE-20261015-task-list-rule.md`
  `76cfb510d0023c0c8cb2e843877417c387fe05b92f9ef5dfbe24dc18457194ef`;
- `lean/README.md` `0af69b1afed49098220cbe6b8fe69c9e766bac3054180e319fdae68b7bbbe38c` (it
  predates the per-job folders of 2026-10-16; where it and this order differ, this order's layout
  holds);
- LEAN-16-order.md `d494728c561a922b1227587395f9650f33dd3182791620e7a0d0fb6469f3120e`;
- on DSMain, LEAN-31's helpers in `~/lean/lean31-checks/scripts/`: `el.sh`
  `e2c9137e9c31a148bc79da61cbdc49a119c6d427c5504e7c4b390b222e313b37`, `probecheck.py`
  `1e082d9503633cb1bfb879ad0c49243b76b06a3fbcbdabcd69a636dee7d7e462`, `briefcheck.py`
  `aa36b5686ac507a360149c347c8f96156bbffe2abc6beca94197f727ae65d95b`, `mkbrief.py`
  `8bd502b28d276d738356024001b0aaf7562d355cb009c6c274877978094c3366`, `mkconfirm.py`
  `74e53e1015a181d70c4b6f003bc2bacb99062ff28d78626afd612ab0176d482e`; and
  `~/lean/lean31-checks/appendix/closure.py`
  `a8c20424dc9e0d504a6d9a011b6fa12f4e33162ac0bcac006a21dcb6a0989a24`; and
  `~/lean/lean31-checks/misses.md`
  `0dab1d218a05519eea693d4f499d6044f37dc430804796b5602a616c4d91fb32`;
- in the repository at `8071e74`:
  - `ClassicalLean/Probability/GlivenkoCantelli.lean`
    `3231a38da48898b4f9e5f16faa9e6f2f1942e06f95aa8f1f98f30cfcb442cc05`;
  - `ClassicalLean/Analysis/LinearODE.lean`
    `851ab656a66d710cf07f56d2694a71ae031bd7947d09800ccee8a4cd24f66583`;
  - `ClassicalLean/InformationTheory/MethodOfTypes.lean`
    `a747cf5f8dd7615c2c2a6b6231f54592e6e221b805f8e881d5b714fb990da7b5`;
  - `ClassicalLean/InformationTheory/Channel.lean`
    `7d0fed1182b96be53f8f1249c44ed9fdc9781f0b969a652cda2dae0fb9bd8bf3`;
  - `ClassicalLean.lean` `580d1d0f777abe5d31416f27d8441e06fe75db4a618b1dcb43bc68f8b8c574e3`;
  - `HANDOFF.md` `8c8335b713407e99635e933ba1c74fa4c37784c1ab776331a94edc9bd4c50e95`;
  - `ROADMAP.md` `05045a16ef9be961bceb3fa1f580a49cc81d0e747217d802974f460836795a43`;
  - `records/README.md` `b6556dee3acbd3e6b6d3174bb01b4a8ac41d3191c1aa0b695d6a34341b205123`;
  - `records/orders/INDEX.md` `f98a526fe7a96d8b0b733a7d303a2a0666d6948ff94b062c1d36b6eea70e6be7`;
  - `records/CLAIMS.md` `4f56ef9ae3736977381d59b8fcba2b5a7ffc510d4a43504df7e644921e0dc665`;
  - `tools/vacuity_reviewed.txt`
    `b5d168d4474375cbba3d5fd29948da316109b4323fa768af433b71df29fa8bde`.

Then read:
- **In the lane:** MATH-PLAN-library-2.md, section 5's "Batch 6" table, section 6's rows 106 to 110
  and section 8 in full; LEAN-31's order, sections "Scope", "Rules for this order", "Setup", "Job
  1", "Job 2" and "Job 4" (this order follows them where it does not say otherwise); LEAN-31's
  report in full (the report's model; its item 104 section says how rule 2's exception went);
  LEAN-31's close and claude-ai's review of it; VACUITY-3-ruling-3.md (the witness form and its two
  cases); the bridges file's rows 154 to 158; the "Known traps" section of LEAN-16-order.md;
  `lean/README.md`; and LEAN-32-checks.py's docstring.
- **On DSMain:** `~/lean/lean31-checks/misses.md` in full (23 items; this order answers 15, 16, 18,
  21 and 23 by name).
- **In the repository:** HANDOFF.md §4 and §6 (rules 17, 18, 20, 27, 31, 35, 36 and 37 apply),
  `records/README.md`, round 63's fragment, and the sources of the four homes.

Which steps of the plan's section 8 apply: all of them, with the gates of step 9 as LEAN-31 ran
them (six: build, AxiomGate, VacuityGate, check_sorry, check_records, gate 7) and
`banned_vocab_scan` beside them as LEAN-31 did.

## Rules for this order

LEAN-31's rules 1 to 10 apply as written in its order, with the changes below; its rule 11 (carried
drafts) has nothing to act on here. Rules 12 and 13 are new.

1. **The gate as LEAN-31 left it.** LEAN-31's rule 1, unchanged.
2. **Witnesses.** LEAN-31's rule 2's form, unchanged. **Seven are owed:** both theorems of 106, both
   of 107, and 108, 109 and 110. **The exception, claude-ai's ruling, Dustin's veto open:** the
   witnesses of 107 and 109 need an independent, identically distributed sequence that is not
   constant, and 106's second needs a law whose distribution function is continuous. Mathlib has
   named laws with a closed-form distribution function (for example `cdf_expMeasure_eq`,
   `Probability/Distributions/Exponential.lean` line 165), but that module and Gamma's are outside
   the root's closure (facts, `closure3.out`); so 106 uses the uniform law on `[0, 1]`
   (`volume.restrict (Set.Icc 0 1)`, `Real.volume_Icc`, probed under the new module's two imports
   in A1, `e6-S106.out`), read through `cdf_eq_real`. For 107 and
   109, GlivenkoCantelli and MethodOfTypes each gain `import Mathlib.Probability.HasLawExists`
   (Scope), which brings `Independence/InfinitePi` and `ProductMeasure` with it. Inferred: their
   own imports reach neither (claude-ai's cold reviewer traced the imports inside Mathlib's
   `Probability/` folder only, and S109's first run found `IndepFun` unknown there). Every name below printed its type under those imports (A6,
   `e4-SW.out`). First try, as LEAN-31's rule 2 set out for item 104: a concrete model,
   `Measure.infinitePi` with `iIndepFun_infinitePi` and `Measure.infinitePi_map_eval` (or
   `measurePreserving_eval_infinitePi`), and pairwise independence from `iIndepFun.indepFun`. If
   that does not close within one hour of attempts for a witness, fall back to LEAN-31's form for
   item 104: one `example` stating that a model exists, from Mathlib's `exists_iid` (or
   `exists_hasLaw_indepFun`) with a non-degenerate law, identical distribution from
   `HasLaw.identDistrib` and `HasLaw.map_eq`, and the theorem applied to it. The report says which
   form landed and why. Rule 7's clock starts only if the fallback fails too.
3. **A claim in the library is checkable from the library.** LEAN-31's rule 3; the labelled lines
   are those of `lean/LEAN-32/scripts/LEAN-32-checks.py` or of your own checks script.
4. **Narrowing and widening are said the same way everywhere.** LEAN-31's rule 4, with this
   order's words: narrowing "none" or each one named; the five widenings named (107 for any `ν₀`
   and no "differs" hypothesis; 108 with no positive definiteness and no symmetry; 109's law
   hypothesis; 109 with pairwise independence only; 110 with `q ≥ 0` and the support condition);
   item 107's added second theorem named
   as an addition. The same greps, on round 64's fragment, the report draft and the INDEX row
   (`| LEAN-32 |`).
5. **Method A**: LEAN-31's rule 5, and **its miss of 14** (`misses.md` item 15): count one `_simp_`
   per membership or reversed (`←`) lemma inside `simp only [...]`, as the plan's section 8, step 4
   already says, beside the `field_simp` range. Give the range both ways.
6. **A question to Dustin holds only its own outcome open.** LEAN-31's rule 6.
7. **Stops inside an item.** LEAN-31's rule 7, with rule 2's exception above.
8. **A commit message says only what the evidence log shows** (HANDOFF.md §6 rule 35), now with a
   machine check (rule 13).
9. **Every clock time carries its date** (HANDOFF.md §6 rule 36), with LEAN-31's brief builder.
10. **A name is probed before the text that uses it** (HANDOFF.md §6 rule 37), with LEAN-31's
    final checker (`probecheck.py`, sha256 above) and its planted cases, plus two more from
    `misses.md`: item 16's (a name after `rcases … with` is bound only after `with`; the term
    before `with` is not a binder, so an unprobed lemma there is refused) and item 18's (a name
    declared in the unchanged part of a module file does not clear the same name in the changed
    lines). Seed: the code of A1 to A6 (Setup 7).
11. **No carried drafts.** Nothing from `/data/api-credit/` lands in this order.
12. **A tool that imports `ClassicalLean` runs only on a fresh root build** (new; filed as
    HANDOFF.md §6 rule 38 in job 3). LEAN-31's first bridge search and report-tool run read a
    `ClassicalLean.olean` built before the new module existed, so both saw 128 modules and their
    results were void (`misses.md` item 23). So `tools/bridge_search.py`, the report tool, the
    plan's checks with `--lean`, LEAN-31's A5-style counts and any census that imports
    `ClassicalLean` run only through a wrapper,
    `rootrun.sh <command>`, that first runs `lake build` at the current HEAD under the cap, logs its
    rc, its job count and `git rev-parse HEAD`, and refuses the command (logged `NOT RUN`) unless
    that build's rc is 0. Tested before first use (Setup 2): with the build step replaced by
    `false`, the command is refused and not run; with the real build, the log shows the build line
    before the command line, at the same HEAD. The gates (AxiomGate, VacuityGate and its tests,
    gate 7) are not wrapped: they run as job 4c sets out, after gate 1's build.
13. **Run citations in commit messages are written by script** (new; filed as HANDOFF.md §6 rule
    39 in job 3). LEAN-31's commit messages named lists of runs that were not the whole list (its
    close, section 3.4; `misses.md` items 10 to 14, 17 and 20). So: after each commit you write a
    marker line `COMMIT <hash>` to `evidence.log`; a commit message that cites runs ends with one
    line written by `evcite.py`, `Evidence: evidence.log lines N to M: <every label in those
    lines>`, covering every line since the last marker; and `citecheck.py`, run in job 4e, compares
    each commit's `Evidence:` line with `evidence.log` and reports every difference. Tested before
    first use (Setup 2): a message whose label list leaves one label out is reported; the
    generated line passes.

## Before approval (read-only in the repository)

1. `git fetch origin` in the worktree. Then, each predicted and checked: origin/master and
   `git ls-remote github master` are both `8071e74a04761d1ea0bbaac3fcabd7b1e1b6eb31` (predict this
   from LEAN-31's close, section 1, the reflogs: at `8071e74`, HANDOFF.md, INDEX and CLAIMS still
   say "not pushed", so they cannot predict it);
   `git show 8071e74:lean-toolchain` and the Mathlib `rev` in `git show 8071e74:lake-manifest.json`
   are the values LEAN-31's order gives (`leanprover/lean4:v4.34.0`,
   `5ed2965256430c3649e86755f9576b54eca72435`); `git status --porcelain` is empty. If any differs,
   stop and report.
2. Check the hashes above and read the read list.
3. Check the night jobs and `free -g`.
4. Write your plan with `ds_file` (project `lean`, job `LEAN-32`, kind `plan`): the jobs in order,
   every prediction you can already make, and the order of the items; and the plan-fit check
   (HANDOFF.md §6 rule 16): for each of items 106 to 110, section 5's row of MATH-PLAN-library-2
   beside this order's statement (Appendix A), with every difference named and anything else you
   find. At least: the five widenings; item 107's added theorem; item 106's `hu : 0 ≤ u` and the
   `[0, 1]` range of its equality, both as the plan has them since its cold review; item 108's
   names (`v ⬝ᵥ (M *ᵥ v)` for the plan's `xᵀ P x`); and the method's differences carried over from
   LEAN-31 (reviewers may elaborate two small files; `banned_vocab_scan` runs beside the gates).
   Dustin's approval of the plan closes rule 16's statement review for these statements. Then stop
   and wait for his approval.

## Setup (after approval)

1. **Branch.** `git switch -c lean-32 8071e74a04761d1ea0bbaac3fcabd7b1e1b6eb31`.
2. **Evidence folder** `~/lean/lean32-checks/`, with `evidence.log` as LEAN-31's Setup 2 sets it
   out. Extract Appendix A's six files byte for byte into `~/lean/lean32-checks/appendix/` and check
   their sha256 against the appendix. Copy LEAN-31's helpers named in "Check, then read" and read
   each before use. Run rule 9's and rule 10's planted cases (LEAN-31's, and rule 10's two new
   ones), then **build rule 12's `rootrun.sh` and rule 13's `evcite.py` and `citecheck.py`** and run
   their planted cases. Log each run with its prediction. A check that does not behave as predicted
   is a stop.
3. **Records first.** The first commit on `lean-32`, with no `.lean` file:
   - this order's copy as
     `records/orders/<UTC>__claude-ai__order-lean32-pit-ks-lyapunov-aep-fdiv.md`;
   - its INDEX row and a CLAIMS row;
   - round 64's fragment, which names in full every module file this order changes, the new
     module's included, and records LEAN-31's push: both remotes at `8071e74`, re-measured by
     `git ls-remote` before you write it; who and when from LEAN-31's close, section 1 (Dustin,
     2026-10-16 19:39 EDT);
   - LEAN-31's INDEX State cell and its CLAIMS row: append
     "; pushed by Dustin to both remotes 2026-10-16 19:39 EDT (`8071e74`)"
     and change nothing else in them.
   check_records then: PASS 129 (the new module does not exist yet).
4. **The before runs, at the records commit**, predicted from the facts: build rc 0, 4177 jobs, 0
   warnings; AxiomGate PASS 3372 (the base for job 1's blind prediction); the report tool, through
   `rootrun.sh`, rc 0: 1861 written; A 1081; B 780; C 36, 0 recursive; saved as
   `report-before.out` for job 4b.
5. **The plan's checks**, with `--lean`, through `rootrun.sh` (they import `ClassicalLean`), using
   `~/lean/vacuity2-checks/mm` (at `2da3ab0a`).
   Predicted: 170 of 232, rc 1, the 62 misses of the facts (copy LEAN-31's list from its order's
   facts and add the four, line by line, into your prediction file; `setup.worktree`'s measured
   value will be your records commit), and every line of rows 106 to 110 a hit. Only a miss on a
   row 106 to 110 line means Mathlib or the library has that row by now: drop that row and say so.
   A `setup.*`, `gate.*`, `census.*`, `used.*` or `bridges.*` miss never drops a row.
6. **The exact checks:** `python3 -I` on the lane's `lean/LEAN-32/scripts/LEAN-32-checks.py`.
   Predicted: 14 of 14 checks hit, 10 BY HAND lines, rc 0, output sha256
   `0336f9dc1366b1e866f712e70a5b5d71a277d479222c4136d150a0cc65365d30`. A different output hash with
   14 of 14 is reported, not a stop.
7. **The statements:** elaborate A1 to A6 from the worktree root with rule 20's four flags.
   Predicted: rc 0 each, the only warnings `declaration uses sorry`, 2, 2, 1, 1 and 1 for A1 to A5
   and none for A6, every probe printing its type. These runs are probes, not drafts: rule 10's check does not apply to them,
   and they seed it.

## The work

Items 106 to 110 go through jobs 1 to 4 together. A suggested order: 110 and 108 (the routes are
short), 106 (a new module), 107, then 109 (the witness most likely to need rule 2's fallback).

### Job 1, predictions (section 8, step 4)

- **The job count:** 4178 (facts). Confirm by LEAN-31's A1 (`closure.py`) with the import lines as you finally write them,
  before any build, naming each module with new imports on the left of its own argument; the
  prediction holds only if both lines print `unresolved []`. With rule 2's
  `Mathlib.Probability.HasLawExists` in GlivenkoCantelli and MethodOfTypes, the facts' re-run
  (`closure2.out`) already gives 4162, so 4178 should stand; re-run it with your final import
  lines anyway.
- **The theorem constants, blind:** Method A from the source, then Method B by a census of scratch
  copies (through `rootrun.sh` where it imports the root), both before any gate; base 3372; rule 5.
- **The bridge diff** before its run (job 4a). **Gone pairs:** take the used table of a scratch
  build of your new proofs (what Lean records as used, not the names in the source; `misses.md`
  item 21 shows the source count misses structures and lemmas Lean uses implicitly), and count the
  constants in it whose module count is exactly 10: `tools/bridge_search.py`'s `df` (its line 94),
  worked out by a scratch script in the evidence folder that runs `bridge_search.py`'s `LEAN_USED`
  dump and applies its lines 82 to 94 (the same filters, `df` per kind, `obj` and `thm`), through
  `rootrun.sh` at the records commit, whose Lean tree is `8071e74`'s. `bridge_search.py` itself
  writes the used table only to a temporary folder (its line 195) and `records/bridges/LEAN-31/`
  holds only `COMMIT`, `pairs.tsv` and `shapes.tsv`, so neither gives those counts. Give the range
  from that count. **New pairs:** the new module with the modules that share its constants;
  GlivenkoCantelli likely among them (both use `cdf`), and it may be a real bridge (row 159), not
  this batch. Also GlivenkoCantelli and MethodOfTypes with EffectiveSampleSize and GamblersRuin,
  which already use `Measure.infinitePi` and `iIndepFun_infinitePi`, if the witnesses use them;
  count those constants in the gone-pair figure too.
- **The plan's checks after the work** are not re-run as a gate. If you re-run them, expect the
  library counts of `row.B5`, `row.B6`, `row.D2`, `row.E4` and `row.E6` to turn into misses as the
  new docstrings use their words; predict each by grep before the run.

### Job 2, statements, hypotheses and reviews (section 8, steps 5 to 8)

LEAN-31's job 2 (2a to 2f) as written, with: seven witnesses (rule 2); one cold review per changed
module (the new module, GlivenkoCantelli, LinearODE, MethodOfTypes, Channel); and, in every
reviewer's brief, the questions of rule 1 (no main theorem's conclusion a recursive all-`True`
predicate) and of ruling 3's two cases for the witness.

### Job 3, documents

- `HANDOFF.md`: §1, a dated LEAN-32 paragraph with the counts; §6, rules 38 and 39 from rules 12
  and 13 above, each with its source (`misses.md` item 23; LEAN-31's close section 3.4 and
  `misses.md` items 10 to 14, 17 and 20); the rules' lead-in names them.
- `ROADMAP.md`: batch 6, §1.24, after LEAN-31's §1.23, saying that batch 6 closes the six batches
  of MATH-PLAN-library-2 above its cut.
- One fresh cold reviewer reads the documents commit's diff alone (about 15 calls); its confirming
  pass closes the job.

### Job 4, the end checks, in this order

- **4a. The bridge search**, through `rootrun.sh`: `tools/bridge_search.py --diff
  records/bridges/LEAN-31/` under the cap, on a clean commit of jobs 1 to 3; as LEAN-31's 4a, with
  row 159 next and the new baseline in `records/bridges/LEAN-32/`. Say for each real bridge that it
  cannot be load-bearing for a scheduled row: batch 6 is the last.
- **4b. The report tool**, through `rootrun.sh`, on the same clean commit: a report, not a gate.
  Predicted from `report-before.out` and job 1; section C: 36 (this order adds no definition), 0
  recursive. List every `CLOSES` line that names a theorem of this order.
- **4c. Commit everything above. Then the six gates** on the clean tree, predicted first: build rc
  0, 4178 jobs (or job 1's corrected count), 0 warnings; AxiomGate PASS at job 1's count;
  VacuityGate PASS, no new flag (or job 2's listed helpers), 0 VACUOUS-PENDING, 0 run-outs, no
  UNCHECKED, its tests unchanged (89, 47 flagged, 3 UNCHECKED as expected, 0 mismatches);
  check_sorry PASS 130; check_records PASS 130; gate 7 under the cap
  (`systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0 ~/lean/recheck/run-recheck.sh <commit> ~/lean/classical-lean-paper-crypto`):
  ALL PASSED, 4178 jobs, 130 modules 0 failed, the theorem count, three standard axioms, planted
  fault named. `banned_vocab_scan` beside them. After the gates, only commits that touch nothing
  outside `records/` are allowed.
- **4d. Report** with `ds_file` (kind `report`), laid out like LEAN-31's report, including: rule 4's
  grep output; predicted beside measured; rules 12 and 13's planted cases; `citecheck.py`'s output;
  misses and not reached; LEAN-31's row of numbers for the order table (facts) and this order's own
  row; and the push command as one line, not run:
  `cd ~/lean/classical-lean-paper-crypto && git push origin lean-32:master && git push github lean-32:master`.
  Every pointer in the report points to something that is there.
- **4e. Push-review file** with `ds_file` (subdir `data`, name `LEAN-32-push-review.txt`), written
  by one script as LEAN-31's 4e sets out, from `8071e74`, and with `citecheck.py`'s output at its
  end. Report its sha256. Then stop. claude-ai reviews it before Dustin pushes.

## Done means

- Branch `lean-32` from `8071e74`, clean tree, nothing pushed; its first commit is the records
  commit and holds no `.lean` file; every prediction hashed in `evidence.log` before its run; hashes
  in records written by script; `el.sh` runs logged; the jobs tracked with the task tools.
- Rules 9, 10, 12 and 13's machine checks run on their planted cases first, as predicted.
- Items 106 to 110 proved with no `sorry` and no new axiom, as stated here, or each narrowing said
  plainly with its reason; the five widenings and item 107's added theorem said in the module
  docstrings, the report, the INDEX row and round 64; any dropped row named with the line that has
  it; any item not closed after two review rounds reported, its changes reverted.
- Seven witnesses in rule 2's form (each fallback named), each checked by its module's reviewer
  against rule 3 with ruling 3's two cases; every hypothesis has a dropped-hypothesis row whose
  evidence is an `example`, a labelled check or "by hand", or is named "not shown needed", with
  Lean's junk values where they decide the case.
- Each changed module had its cold review after its statements were final, ending with a confirming
  pass; any statement changed after its review had a statement-equivalence review.
- Every reviewer's and checker's output saved verbatim with its sha256 (HANDOFF.md §6 rule 17), and
  `~/.claude/agent-memory/` hashed before the first review and after the last.
- Every commit message that cites runs ends with `evcite.py`'s line, and `citecheck.py` reports no
  difference (or each one named in the report).
- Every tool rule 12 names (`tools/bridge_search.py`, the report tool, the plan's checks with
  `--lean`, LEAN-31's A5-style counts, any census that imports `ClassicalLean`) ran through
  `rootrun.sh`; the gates ran as job 4c sets out, after gate 1's build.
- No VACUOUS-PENDING entry and no UNCHECKED verdict in the library; every new list entry named with
  its reason and its reviewer's check.
- The job count and the constant count predicted (blind, before any census) beside measured.
- Job 3's documents changed and named, their review closed by a confirming pass; rule 4's three
  files agree and the grep is in the report; LEAN-31's push appended to its rows (Setup 3).
- The report tool's run reported (4b).
- All six gates as predicted, or each miss reported; gate 7 ALL PASSED on the last commit that
  touches anything outside `records/`, and later commits touch only `records/`.
- The bridge diff run and reported against its prediction; the new baseline committed and named.
- The plan, the report and the push-review file are in `lean/LEAN-32/` and their hashes match yours.

Then report in a few plain sentences: what was proved, any narrowing and the five widenings, the
gate results, the new list entries, the two files' hashes and the push command. Dustin reads your
replies carefully and is still learning to read code: use plain words and define a technical term
the first time you use it. When you need a decision from him, ask in one line with your recommended
answer first.

## Not in this order

- Items 111 onward. **After LEAN-32 the plan's six batches are done**; what comes next (rows below
  the cut, a third plan, or something else) is claude-ai's to propose and Dustin's to decide.
- Rows 154 to 158 of the bridges file, and any bridge job 4a finds: the lane's bridges file only.
- The carry list's rows: VACUITY-3 rows 7, 8, 9, 10, 31, 32, 67 and 70, and the anthropics review's
  row 1b (the next gate order); plan rows 119 and 120 (a later order).
- The plan's check script: not changed; its misses are predicted instead.
- Rewriting older INDEX or CLAIMS rows that say "not pushed": only LEAN-31's are amended.
- The main clone, `~/trading`, `~/lean/recheck`, `/data/api-credit/`, Dustin's `banned-terms`
  file, and any push.

## Revisions

- r0, 2026-10-18, the draft.
- r1, 2026-10-18, cold review pass 1's fixes. MAJOR: rule 2's witnesses need
  `Mathlib.Probability.HasLawExists` in GlivenkoCantelli and MethodOfTypes, now in Scope, probed (A6) and
  closure-checked (`closure2.out`); the Scope's reference to LEAN-31's bullets named by title; rule 12 covers the
  plan's checks with `--lean`, Setup 5 runs them through `rootrun.sh`, and Done-means lists rule 12's tools; the
  gone-pair count read from `bridge_search.py`'s `df`, not from the baseline files; a fifth widening (109's pairwise
  independence); every clock time dated on its line (rule 36, now asserted by the assembler). MINOR: the gone-pair
  source; item 60's docstring quoted; 106's `hu0` row; 109's law and independence cases; 109's integrability names
  (probed, `e4-S109.out`); rule 2's search sentence (Mathlib's exponential law is outside the root's closure,
  `closure3.out`); the plain words on 107's widening; what `110.rel` checks; the facts' time range; the memory figure's
  source; `misses.md`'s hash; `lean/README.md` predating the per-job folders; J1's push prediction source; the
  nightly's count beside the report tool's. A4 (S109) gained two probes; A6 (SW) is new.
- r2, 2026-10-18, cold review pass 2's three MINOR: how the gone-pair module counts are worked out (a scratch script
  on `bridge_search.py`'s filters, through `rootrun.sh` at the records commit); new pairs through the witnesses'
  `infinitePi` constants; rule 2's import trace marked inferred, and 106's witness names probed under the new module's
  own imports. That probe failed first (`e5-S106.out`: `Real.volume_Icc` unknown under `Mathlib.Probability.CDF`
  alone, against claude-ai's prediction), so the new module also imports `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`,
  in the root's closure (`closure4.out`); A1 (S106) gained that import and two probes (`e6-S106.out`). One wording
  change in 109's rows.

## Appendix A: the scratch files

Each file is given byte for byte between its fences; its sha256 is of exactly those bytes. Extract
each into `~/lean/lean32-checks/appendix/` (Setup 2). On DSMain claude-ai's copies are in
`/tmp/claude-ai-lean32/app/`.

### A1: `/tmp/claude-ai-lean32/app/S106.lean`, item 106 (the new module), statements and probes

sha256 `6af21b97cb143907b9bf3af27794cc1e6f2e5f1550ea7233e04f55db4f546953`

```lean
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory ProbabilityTheory

namespace ClassicalLean.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem measureReal_cdf_le_le [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | cdf (μ.map X) (X ω) ≤ u} ≤ u := by
  sorry

theorem measureReal_cdf_le_eq_of_continuous [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (hF : Continuous (cdf (μ.map X))) {u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) :
    μ.real {ω | cdf (μ.map X) (X ω) ≤ u} = u := by
  sorry

end ClassicalLean.Probability

#check @ProbabilityTheory.cdf
#check @ProbabilityTheory.cdf_nonneg
#check @ProbabilityTheory.cdf_le_one
#check @ProbabilityTheory.measure_cdf
#check @ProbabilityTheory.cdf_eq_real
#check @ProbabilityTheory.tendsto_cdf_atBot
#check @ProbabilityTheory.tendsto_cdf_atTop
#check @MeasureTheory.map_measureReal_apply
#check @StieltjesFunction.mono
#check @StieltjesFunction.measure_Iic
#check @StieltjesFunction.measure_Iio
#check @intermediate_value_univ
#check @Monotone.leftLim
#check @MeasureTheory.measureReal_mono
#check @MeasureTheory.Measure.restrict
#check @Real.volume_Icc
```

### A2: `/tmp/claude-ai-lean32/app/S107.lean`, item 107, statements and probes

sha256 `aa22e139c1d64b05bdc4474841fd214e3e56702855ddffd7c0c3e5d4794339c9`

```lean
import ClassicalLean.Probability.GlivenkoCantelli

open MeasureTheory ProbabilityTheory Filter Topology

namespace ClassicalLean.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

theorem eventually_lt_sup_abs_empiricalCDF_sub {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX0 : Measurable (X 0))
    (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (ν₀ : Measure ℝ) :
    ∀ᵐ ω ∂μ, ∀ c < ⨆ x : ℝ, |cdf (μ.map (X 0)) x - cdf ν₀ x|,
      ∀ᶠ n in atTop, c < ⨆ x : ℝ, |empiricalCDF X n ω x - cdf ν₀ x| := by
  sorry

theorem eventually_lt_sup_abs_empiricalCDF_sub_of_tendsto {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} (hX0 : Measurable (X 0))
    (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (ν₀ : Measure ℝ)
    (hne : ∃ x, cdf (μ.map (X 0)) x ≠ cdf ν₀ x) {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, c n < ⨆ x : ℝ, |empiricalCDF X n ω x - cdf ν₀ x| := by
  sorry

end ClassicalLean.Probability

#check @ClassicalLean.Probability.tendsto_sup_abs_empiricalCDF_sub
#check @ClassicalLean.Probability.bddAbove_abs_empiricalCDF_sub
#check @ClassicalLean.Probability.empiricalCDF_nonneg
#check @ClassicalLean.Probability.empiricalCDF_le_one
#check @ProbabilityTheory.cdf_nonneg
#check @ProbabilityTheory.cdf_le_one
#check @ciSup_le
#check @le_ciSup
#check @abs_sub_le
#check @Filter.Tendsto.eventually_lt
#check @Filter.Tendsto.eventually_gt_atTop
#check @Real.iSup_nonneg
```

### A3: `/tmp/claude-ai-lean32/app/S108.lean`, item 108, statements and probes

sha256 `8032374e24425dc9c6a094d25b4af7585df2458b9ec25984db19d3b025096d9b`

```lean
import ClassicalLean.Analysis.LinearODE

open Matrix

namespace ClassicalLean.Analysis

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem quadForm_le_exp_mul {A P : Matrix n n ℝ} {c : ℝ}
    (hL : ∀ v : n → ℝ, v ⬝ᵥ ((Aᵀ * P + P * A + (2 * c) • P) *ᵥ v) ≤ 0)
    {x : ℝ → n → ℝ} (hx : ∀ t, HasDerivAt x (A *ᵥ x t) t) {t : ℝ} (ht : 0 ≤ t) :
    x t ⬝ᵥ (P *ᵥ x t) ≤ Real.exp (-(2 * c * t)) * (x 0 ⬝ᵥ (P *ᵥ x 0)) := by
  sorry

end ClassicalLean.Analysis

#check @ClassicalLean.Analysis.eq_exp_smul_mulVec
#check @ClassicalLean.Analysis.hasDerivAt_exp_smul_mulVec
#check @antitoneOn_of_deriv_nonpos
#check @hasDerivAt_pi
#check @HasDerivAt.sum
#check @HasDerivAt.mul
#check @HasDerivAt.exp
#check @Matrix.dotProduct_mulVec
#check @Matrix.mulVec_add
#check @Matrix.add_mulVec
#check @Matrix.mulVec_mulVec
#check @Matrix.vecMul_transpose
#check @Real.exp_pos
#check @dotProduct_comm
```

### A4: `/tmp/claude-ai-lean32/app/S109.lean`, item 109, statements and probes

sha256 `3ab62a56608cfb8ef5d11a5a382a5de91f455490d98112af656807d9fca8fe94`

```lean
import ClassicalLean.InformationTheory.MethodOfTypes
import Mathlib.Probability.StrongLaw

open MeasureTheory ProbabilityTheory Filter Topology Finset

namespace ClassicalLean.InformationTheory

variable {α : Type*} [Fintype α] [DecidableEq α]

variable [MeasurableSpace α] [MeasurableSingletonClass α]

omit [DecidableEq α] in
theorem tendsto_neg_log_div_shannonEntropy {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → α}
    (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) {p : α → ℝ}
    (hlaw : ∀ a, μ.real {ω | X 0 ω = a} = p a) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ -(∑ i ∈ range n, Real.log (p (X i ω))) / n) atTop
      (𝓝 (ClassicalLean.Simplex.shannonEntropy p)) := by
  sorry

end ClassicalLean.InformationTheory

#check @ClassicalLean.Simplex.shannonEntropy
#check @ProbabilityTheory.strong_law_ae
#check @ProbabilityTheory.IdentDistrib.comp
#check @ProbabilityTheory.IndepFun.comp
#check @ProbabilityTheory.IdentDistrib.aemeasurable_fst
#check @measurable_of_finite
#check @MeasureTheory.integral_map
#check @MeasureTheory.integral_fintype
#check @MeasureTheory.Integrable.of_finite
#check @MeasureTheory.Integrable.comp_aemeasurable
#check @MeasureTheory.integrable_map_measure
#check @MeasureTheory.Measure.map_apply_of_aemeasurable
```

### A5: `/tmp/claude-ai-lean32/app/S110.lean`, item 110, statements and probes

sha256 `fbac481e094c3632b9dd11950153f31b4ec28905774ab292ad5db5473610832e`

```lean
import ClassicalLean.InformationTheory.Channel

open Finset Real
open scoped Matrix

namespace ClassicalLean.Simplex

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem sum_mul_comp_div_vecMul_le {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici 0) f)
    {p q : ι → ℝ} {W : Matrix ι κ ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpq : ∀ i, q i = 0 → p i = 0) (hW0 : ∀ i j, 0 ≤ W i j) (hW1 : ∀ i, ∑ j, W i j = 1) :
    ∑ j, (q ᵥ* W) j * f ((p ᵥ* W) j / (q ᵥ* W) j) ≤ ∑ i, q i * f (p i / q i) := by
  sorry

end ClassicalLean.Simplex

#check @ClassicalLean.Simplex.relEntropy_vecMul_le
#check @ClassicalLean.Simplex.relEntropy
#check @ConvexOn.map_sum_le
#check @Finset.sum_comm
#check @Matrix.vecMul_apply_eq_sum
#check @Finset.mul_sum
#check @Finset.sum_mul
#check @Finset.sum_div
#check @Finset.sum_filter
#check @mul_div_cancel_left₀
```

### A6: `/tmp/claude-ai-lean32/app/SW.lean`, rule 2, the witnesses of items 106, 107 and 109, probes only

sha256 `cb576ecc01bb5baa4afc54a9d31ab108416b5d66bfa903eb9b0c0c930da5e2e5`

```lean
import ClassicalLean.Probability.GlivenkoCantelli
import ClassicalLean.InformationTheory.MethodOfTypes
import Mathlib.Probability.HasLawExists

/-! Probes for rule 2's witnesses (items 106, 107 and 109) under the homes' imports plus
`Mathlib.Probability.HasLawExists`. No statements; every line is a probe. -/

#check @MeasureTheory.Measure.infinitePi
#check @ProbabilityTheory.iIndepFun_infinitePi
#check @MeasureTheory.Measure.infinitePi_map_eval
#check @measurePreserving_eval_infinitePi
#check @ProbabilityTheory.exists_hasLaw_indepFun
#check @ProbabilityTheory.exists_iid
#check @ProbabilityTheory.iIndepFun.indepFun
#check @ProbabilityTheory.HasLaw.identDistrib
#check @ProbabilityTheory.HasLaw.map_eq
#check @ProbabilityTheory.HasLaw.aemeasurable
#check @ProbabilityTheory.cdf_eq_real
#check @Real.volume_Icc
```
