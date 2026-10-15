# LEAN-29 order: batch 3 of the library's second plan (items 91 to 95), and two old docstring lines

Written 2026-10-14 by claude-ai for a plain Claude Code session on DSMain, as dustin, from step 1
of OPEN-WORK-20261011-r2.md: LEAN-29 comes after VACUITY-3, whose last commit `20303cd` is master
on both remotes. Lane files named here without a folder are in
/opt/datasphere/lane/inbox/threads/staging/; files named `lean/...` are in its subfolder
/opt/datasphere/lane/inbox/threads/staging/lean/ (read `lean/README.md`). Your plan, the report and
the push-review file go to `lean/` through ds_write_staging, since the lane is read-only on disk
for you.

Review: Two passes by one fresh cold reviewer that had not seen it written, reading the order, its
check script and claude-ai's quoted DSMain outputs in the cloud, and the cited lane files
read-only. Pass 1: PASS WITH FINDINGS (0 BLOCKER, 2 MAJOR, 15 MINOR; 23 calls); every finding
applied ("Revisions", r1). Pass 2, the same reviewer: PASS WITH FINDINGS (0 BLOCKER, 0 MAJOR,
2 MINOR), confirming all 17 of pass 1's findings fixed; both new findings applied (r2), which have
not had a third review. Not reviewed: anything that needs Lean beyond the scratch files' own
elaboration (for example whether row 51's way of getting `uniformOn`'s probability-measure
instance carries over to `Fin 3` in one inline block), and repository files the reviewer could
not reach (HANDOFF.md, the module sources), which claude-ai quoted from DSMain.

Facts measured on DSMain by claude-ai on 2026-10-14 from 20:21 to 21:14 EDT (DSMain's `date`),
read-only, in `~/lean/classical-lean-paper-crypto` on branch `vacuity-3` at `20303cd` (`git status
--porcelain` empty after every run). Outputs saved in `/tmp/claude-ai-lean29/` on DSMain; the
scratch files and the closure script are in Appendix A with their sha256.

- **The repository.** `git ls-remote origin master` and `git ls-remote github master` both give
  `20303cd4eb902e15b2d4994ea6aa2263f5146264`. `lean-toolchain` is `leanprover/lean4:v4.34.0`; the
  pinned Mathlib (`.lake/packages/mathlib`) is at `5ed2965256430c3649e86755f9576b54eca72435`.
- **The gates at `20303cd`**, from VACUITY-3's report (job 5, at `bca952e`; `20303cd` changes only
  `records/`, checked by claude-ai's push review, store row 20261014-002, and lane
  `lean/VACUITY-3-ruling-3.md`): build 4170 jobs, 0 warnings; AxiomGate PASS 3228; VacuityGate
  PASS (1 reviewed helper, 0 VACUOUS-PENDING, 0 rule-5 run-outs, no UNCHECKED); the gate's tests
  89 verdicts, 47 flagged, 3 UNCHECKED as expected, 0 mismatches; check_sorry PASS 122;
  check_records PASS 122 (1 named exemption); gate 7 ALL PASSED, 4170 jobs, 122 modules 0 failed,
  90615 declarations, three standard axioms, 3228, planted fault named. The report tool
  (`tools/UninformativeReport.lean`): 1785 written theorems; section A 1027 (0 close, 988 open, 39
  dependent); section B 758 (16 close: 15 by `simp`, 1 by `positivity`); section C 33 Prop-valued
  definitions, 0 recursive. The bridge search against `records/bridges/LEAN-28/`: 0 new, 0 gone.
- **The plan's checks** (MATH-PLAN-library-2-checks.py, with `--master ~/lean/vacuity2-checks/mm`
  at `2da3ab0a`):
  - without `--lean`: 185 of 209 hit (`checks-nolean.out`, sha256
    `93965b0328af45675d7a68e7736b36f72e3f449a6ecd182ca37758c0fb288bf1`);
  - with `--lean`, under the 12G cap (2:23 wall, 4359448 KB peak): **192 of 232** hit
    (`checks-lean.out`, sha256 `05b859fa49115a1055c8c77259628621215ed801debb45394529cf68dfcd6d26`).
    The 40 misses, by label: `setup.modules` (122), `setup.worktree` (`20303cd`), `row.A2`,
    `row.A3`, `row.F6`, `row.H6`, `row.K2` (library 13), `row.X2`, `row.X3` (both searches),
    `row.X12`, `row.X14`, `row.X15`, `trackL.L2`, `trackL.L4`, `trackL.L15`, `trackL.L18`, the
    seven `gate.*` lines (`maxUnfolds`, `macro`, `helper`, `metacheck`, `test.lim_and_hyp`,
    `test.lim_false`, `list`), and 16 `--lean` lines: `census.theorems` 3228, `census.written`
    1785, `census.hyp1` 1094, `census.hyp2` 658, `census.hyp3` 415, `census.helpers` 596,
    `census.derived` (589, 4, 593), `used.lines` 57936, `bridges.modules` 121, `bridges.pairs`
    2393, `bridges.named`, the four `bridges.rank` lines and `bridges.minquad` (61).
  - **Every line of rows 91 to 95 hits**: `row.C2` (both searches), `row.F4`, `row.F5`, `row.X4`,
    `trackL.L19`, and the exact lines `X3.X4.ruin`, `F4.richardson`, `F5.stability`, `C2.gruss`,
    `L19.exp`. So neither Mathlib (pinned or master `2da3ab0a`) nor the library has any of the
    five rows.
- **The homes.** At `20303cd` (sha256 in "Check, then read"):
  - `ClassicalLean.Probability.LongestRun` (467 lines) imports
    `Mathlib.Probability.Independence.Basic` and `Mathlib.MeasureTheory.Measure.Real`; its last
    theorem is `measureReal_no_run_le`
    (bound `(1 - q ^ r) ^ (n / r)`, hypotheses `hA : ∀ i < n, MeasurableSet (A i)`, `hind`, `hq`);
    row 81's witness (two fair flips on `Fin 2 → Bool`, `n = r = 2`) ends the file.
  - `ClassicalLean.Analysis.Simpson` (283 lines): `simpson f N a b` with step
    `(b - a) / (2 * N)`, in namespace `ClassicalLean`.
  - `ClassicalLean.Analysis.EulerMethod` (156 lines): `eulerIterate f t₀ h y₀`, in namespace
    `ClassicalLean.Analysis`.
  - `ClassicalLean.Probability.GamblersRuin` (1068 lines): `measureReal_hit_eq` (fair, item 44) and
    `measureReal_hit_eq_of_biased` (item 84, with `p ≠ 1/2`), in section `Biased` with
    `variable [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}`; the private `integral_comp_step` gives
    `∫ X n = 2 p - 1` inside the module (used by `ae_exitTime_ne_top_of_biased`).
  - `ClassicalLean.NumberTheory.LucasSequence` defines `lucasU (P Q : R)` over any commutative
    ring, with `lucasU_add_two` (true by definition) and `lucasU_of_roots`
    (`(α - β) * lucasU (α + β) (α * β) n = α ^ n - β ^ n`). It imports only Mathlib, so
    GamblersRuin importing it makes no cycle.
  - The new module `ClassicalLean.Analysis.Gruss` does not exist; there are 122 modules.
- **Imports, measured by elaboration.** `Real.exp` is not visible through LongestRun's imports and
  `trapezoidal_integral` is not visible through Simpson's (the first drafts gave "Unknown
  constant"). So LongestRun gains `import Mathlib.Analysis.Complex.Exponential` and Simpson gains
  `import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule`. Both Mathlib modules are
  already in the library's import closure. A1 (`closure.py`) was run with these added edges: the
  root to the new module; the new module to `Mathlib.Probability.Moments.Variance`,
  `Mathlib.Probability.Moments.Covariance`, `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`,
  `Mathlib.MeasureTheory.Integral.Average` and `Mathlib.Probability.ConditionalProbability`;
  Simpson to TrapezoidalRule; LongestRun to `Mathlib.Analysis.Complex.Exponential`; EulerMethod
  to `Mathlib.Analysis.SpecificLimits.Basic` (visible already, as it turned out); GamblersRuin to
  LucasSequence. The closure grew from 9031 to 9032 modules, and the one added is the new module
  itself (`closure1.out`, sha256
  `705a76714281a18b45c7e05dfd3a90e6cef86216f89276ab4c1ec8fcf9e4f8c8`). A1 counts source files
  reached through imports across the repository and `.lake/packages`, a different method from
  LEAN-28's count, so only its difference is used. **Inferred: the build after the work is 4171
  jobs.**
- **The statements elaborate.** The five scratch files A2 to A6 hold every statement of this
  order with `sorry`, and a `#check @name` probe for the public names the routes below cite (not
  the module's private `integral_comp_step`, which a scratch file cannot see, and not the library
  theorems the routes only name as neighbours). Each was elaborated from the worktree root with
  HANDOFF.md §6 rule 20's four flags (`lake env lean -Dpp.unicode.fun=true
  -DrelaxedAutoImplicit=false -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3`),
  under the 12G cap; A4 and A5 at 20:32 to 20:33 EDT, A2 at 21:03 and A6 at 21:06 after cold
  review 1, A3 at 21:14 after cold review 2 (`elab.out`, its last line per file counts): rc 0 for
  all five; the only messages are `declaration uses sorry`, 1, 2, 1, 2 and 1 of them (one per
  statement); 2.4 to 2.9 s, at most 3318500 KB; every probe printed. Logs: `S91.log` to
  `S95.log` in `/tmp/claude-ai-lean29/`.
- **How Lean reads an interval integral** (measured): `∫ x in a..b, f x - C` is
  `∫ x in a..b, (f x - C)`: the body runs on (Mathlib's notation reads it at precedence 60, below
  subtraction's 65), and A3's `example … := rfl` stating that elaborates. Cold review 1 caught that
  the first draft of item 92's second statement left its first integral unbracketed, so Lean read
  the whole left side as one integral; the statement below brackets every integral.
- **The exact checks**, `lean/LEAN-29-checks.py` (standard library, `python3 -I`, exact
  fractions under Lean's conventions; predictions written in its docstring before its first run).
  claude-ai's first run gave 24 of 25: the miss was the script's own cell count (396 predicted,
  330 measured; the bounds held in every cell), a miss of claude-ai's arithmetic. After cold
  review 1 (revision 2) the cases worked by hand print as `BY HAND` lines and are not counted, and
  `92.drop.fbnd` computes its value. Revision 2's run: **23 of 23 checks hit, rc 0, and 3 BY HAND
  lines**, output sha256 `599b0099294fbeb01c748825e452a051dbe64a093afa1418c7c8c61d3933e3e1`, the
  same in the cloud sandbox (Python 3.13) and on DSMain from the lane copy (Python 3.12.3, 21:05
  EDT, `checks29-dsmain.out`). Its docstring's count of BY HAND lines was first written as 4; the
  run printed 3, which is right (claude-ai's miss in writing the prediction, noted there).
- **Two older docstring lines.** The ruling of 2026-10-13 (store row 20261013-017, item 2) sent
  them to "the next order as a small job"; VACUITY-3 did not take them (its report names neither):
  - `ClassicalLean/Analysis/ConvexConjugate.lean` line 34 says its junk values "are checked in Lean
    in order LEAN-27's checks (`~/lean/lean27-checks/dev/Junk79.lean`, outside the repository,
    rc 0)". That file exists (1462 bytes, sha256
    `676715efb060e3ac1b21d45e97e58423b627aa776760272617de7840f70a6a32`, 7 `example`s; it imports
    the module and `Mathlib.Order.CompleteLattice.Basic`). A copy elaborated at `20303cd` with the
    four flags: rc 0, no message (2.17 s).
  - `ClassicalLean/NumberTheory/PrimitiveDivisor.lean` lines 284 to 288 say, in full: "`2 ≤ a`
    is not removable — but it *is* weakenable to `0 < a` by a case split, since the radical
    hypothesis is itself false at `a = 1` once `1 < n`; the stronger form was elaborated, rc 0,
    and `2 ≤ a` is kept because it matches what `sub_one_lt_natAbs_cyclotomic_eval` wants and the
    case split buys one vacuous value of `a`." No file is named. `git log -S` finds the text first
    in `333b69a`, the library's initial commit (2026-10-07), so the records do not say who
    elaborated it or where.
  - Not this order's: `ClassicalLean/Analysis/FiniteGame.lean` line 856 ("worked by hand, not
    checked in Lean") is row 70's witness, which VACUITY-3's ruling 3 sends to the next gate order.
- **The bridge baseline** `records/bridges/LEAN-28/` (`COMMIT` `1032cd3`): `pairs.tsv`, 2393
  import-unrelated pairs over N = 121 modules, and `shapes.tsv`, 535 shape candidates (406 of them
  import-unrelated). Only the root file imports GamblersRuin (grep), so the new edge GamblersRuin
  to LucasSequence makes exactly one new import-related pair, GamblersRuin × LucasSequence, and
  that pair is not in `pairs.tsv` and no line of `shapes.tsv` names both modules (grep, 21:14
  EDT; GamblersRuin's six shape lines pair it with FairGame, LikelihoodScore, MaximalInequality
  and NoEdgeWealth). The only listed pair of GamblersRuin with a Lucas module
  is rank 1160, `NumberTheory.LucasSequenceCases × Probability.GamblersRuin` (score 5.6, two shared
  constants); neither imports the other, so it should stay listed (inferred). LEAN-28's one real
  bridge, row 154, came from a new shape, not a new pair.
- **The night jobs and memory** (`crontab -l`, `systemctl --user list-timers --all`, `free -g`,
  20:28 EDT): user timer 00:00 `memory-index`; cron 02:20 `~/restic-kingston/nightly.sh`; cron
  03:00 `daily_verify.sh`; cron 03:30 `datasphere-backup.sh`; user timer 03:30 `lean-nightly`; cron
  05:40 `ds-backup sync.sh`; also a cron every 15 minutes and two user timers that run every few
  minutes (`w29-tracker`, `w29-sysmap`), not measured further. 62 GiB total, 56 available.

## Goal

1. **Items 91 to 95** of MATH-PLAN-library-2.md (section 5, "Batch 3"), proved in classical-lean
   under the vacuity gate as VACUITY-3 left it, by the plan's per-batch method (its section 8),
   with the statements below. Item 95's statement is wider than the plan's reading (no
   `p ≠ 1/2`); nothing is meant to be narrower.
2. **Job 0, the two older docstring lines** above: each claim is made checkable from the library
   or says plainly that it is not.

Dustin pushes after claude-ai checks the result.

The statements, as elaborated in A2 to A6 (the plan's section 5 table is the source for the
mathematics; the Lean form is this order's):

- **91**, in `ClassicalLean.Probability.LongestRun`: in `n` independent trials that each lose with
  chance `q`, no run of `r` losses has chance at most `exp(−⌊n/r⌋ q^r)`.

  ```
  theorem measureReal_no_run_le_exp {P : Measure Ω} {A : ℕ → Set Ω}
      {n r : ℕ} {q : ℝ} (hA : ∀ i < n, MeasurableSet (A i))
      (hind : iIndepSet (fun i : Fin n ↦ A i) P) (hq : ∀ i < n, P.real (A i) = q) :
      P.real (runEvent A n r)ᶜ ≤ Real.exp (-(((n / r : ℕ) : ℝ) * q ^ r))
  ```

- **92**, in the new module `ClassicalLean.Analysis.Gruss` (its file goes in
  `ClassicalLean/Analysis/`, named after the module): Grüss's inequality, for random variables and
  for averages on `[a, b]`.

  ```
  theorem abs_covariance_le_mul_div_four {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
      [IsProbabilityMeasure μ] {X Y : Ω → ℝ} {m M n N : ℝ}
      (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
      (hXb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc m M) (hYb : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc n N) :
      |cov[X, Y; μ]| ≤ (M - m) * (N - n) / 4

  theorem abs_average_mul_sub_le {f g : ℝ → ℝ} {a b m M n N : ℝ} (hab : a < b)
      (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
      (hfb : ∀ x ∈ Set.Icc a b, f x ∈ Set.Icc m M) (hgb : ∀ x ∈ Set.Icc a b, g x ∈ Set.Icc n N) :
      |(b - a)⁻¹ * (∫ x in a..b, f x * g x) -
          ((b - a)⁻¹ * (∫ x in a..b, f x)) * ((b - a)⁻¹ * (∫ x in a..b, g x))| ≤
        (M - m) * (N - n) / 4
  ```

  Every integral is in brackets: without them Lean reads `∫ x in a..b, f x * g x - …` as one
  integral of the whole difference (facts, "How Lean reads an interval integral"). Keep the
  brackets in the module.

- **93**, in `ClassicalLean.Analysis.Simpson`: Richardson extrapolation, exactly; the library's
  Simpson rule with `N` panels (each two steps wide) is `(4 T(2N) − T(N))/3`, `T` Mathlib's
  trapezoidal rule.

  ```
  theorem simpson_eq_trapezoidal (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) :
      simpson f N a b =
        (4 * trapezoidal_integral f (2 * N) a b - trapezoidal_integral f N a b) / 3
  ```

- **94**, in `ClassicalLean.Analysis.EulerMethod`: stability for `y' = −c y`, `c > 0` (the plan's
  `λ`; `λ` is not a Lean name), step `h > 0`.

  ```
  theorem tendsto_implicitEuler {c h : ℝ} {u : ℕ → ℝ} (hc : 0 < c) (hh : 0 < h)
      (hu : ∀ k, u (k + 1) = u k / (1 + h * c)) : Tendsto u atTop (𝓝 0)

  theorem tendsto_explicitEuler_iff {c h t₀ y₀ : ℝ} (hc : 0 < c) (hh : 0 < h) (hy₀ : y₀ ≠ 0) :
      Tendsto (eulerIterate (fun _ y ↦ -c * y) t₀ h y₀) atTop (𝓝 0) ↔ h * c < 2
  ```

- **95**, in `ClassicalLean.Probability.GamblersRuin`, which gains
  `import ClassicalLean.NumberTheory.LucasSequence`: the walk's chance of reaching `a` first is a
  ratio of Lucas numbers, `U b / U (a + b)` with `U = lucasU (1 + r) r`, `r = (1 − p)/p`.

  ```
  theorem measureReal_hit_eq_lucasU (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
      (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ)
      (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
      (hp : ∀ n, μ.real {ω | X n ω = 1} = p) (a b : ℕ) :
      μ.real {ω | ∃ n, walk X n ω = a ∧ ∀ k ≤ n, -(b : ℝ) < walk X k ω} =
        lucasU (1 + (1 - p) / p) ((1 - p) / p) b /
          lucasU (1 + (1 - p) / p) ((1 - p) / p) (a + b)
  ```

  **Wider than item 84** (claude-ai's ruling, Dustin's veto open): there is no `p ≠ 1/2`. At
  `p = 1/2`, `r = 1`, `lucasU 2 1 n = n` and the formula is `b / (a + b)`, the fair walk's chance
  (item 44), so one formula covers the fair and the biased walk; that is the point of the Lucas
  form (check `95.grid`, every cell with `p = 1/2` included).

No result from below the plan's cut is pulled in.

## Scope

- **Branch.** `lean-29` from `20303cd` in `~/lean/classical-lean-paper-crypto`, made after Dustin
  approves your plan. Nothing pushed. No sudo.
- **You may change:**
  - the four modules named above (LongestRun, Simpson, EulerMethod, GamblersRuin), and make the new
    module `ClassicalLean.Analysis.Gruss`;
  - `ClassicalLean.lean`, only to add the new module's import line;
  - for job 0, `ClassicalLean/Analysis/ConvexConjugate.lean` and
    `ClassicalLean/NumberTheory/PrimitiveDivisor.lean`: docstring lines, `example`s appended after
    the module's last line (each with an optional `open … in` line of its own, as in rule 2's
    form), and at most one import line in ConvexConjugate if the moved examples need a module that
    is already in the library's import closure (A1 tells); no theorem, definition or proof there
    changes;
  - `tools/vacuity_reviewed.txt` (job 2's 2c only), `records/`, and `HANDOFF.md` and `ROADMAP.md`
    (job 3).
- **You may not change** anything else under `ClassicalLean/` or `tools/`. Needing to is a stop.
- **Off limits:** the main clone's working tree `~/lean/classical-lean` and its `master` (the
  nightly's clone). The worktree shares the main clone's `.git`, so `git fetch`, your branch and
  your commits are written there; that is expected. Also off limits: anything under `~/trading`
  or `~/lean/recheck` (`run-recheck.sh` is run, as gate 7, not edited).
  `~/.config/classical-lean/banned-terms` is Dustin's: never edit it, never copy its patterns.
- **The night window.**
  - Start nothing that loads the library and could still be running at 02:00 EDT.
  - Start nothing that loads the library between 02:00 and 05:45 EDT (the night jobs in the facts;
    gate 7 takes about 20 minutes).
  - Do not start a whole-library run in the 15 minutes before the 00:00 `memory-index` timer.
  - Check `crontab -l` and both `systemctl list-timers` lists again before you start.
  - Reading, hash checks and records commits may run inside the window.
  - If a step that loads Lean comes due inside the window, stop and tell Dustin in one line
    (LEAN-28's session waited instead of stopping; the order asks you to stop).
- **The memory cap.**
  - Every run that loads the whole library goes under
    `systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0 <command>`: a full build, the
    gate, a whole-library census, the plan's checks with `--lean`, the report tool,
    `tools/bridge_search.py` and gate 7. VACUITY-3 ran two development runs of the report tool
    without it; do not.
  - A run the cap kills is a stop.
  - Never run two whole-library runs at once, a reviewer's included.
  - A non-interactive shell on DSMain may lack `~/.elan/bin` in `PATH` (measured over ssh: "Failed
    to find executable lake"); put it there or call `~/.elan/bin/lake`.
- **Your plan** goes to `lean/LEAN-29-PLAN.md` (then -PLAN-2, never overwriting). Report its
  sha256.

## Check, then read

Check these sha256s first; if any differs, stop and say which:
- this order, `lean/LEAN-29-order.md`: the value in Dustin's prompt;
- `lean/LEAN-29-checks.py` `8e82051348b8e71e67636322dd406d0f791c319d9313e9b993acf578ad023dc5`;
- MATH-PLAN-library-2.md `6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166`;
- MATH-PLAN-library-2-checks.py `92eedbc6598361a06a50bdf3a1b4fa1698c1d1d7a3dfe783cc79dd9c1c38307e`;
- MATH-PLAN-library-2-bridges.md `afd11b318fcf1f7e547ba611127529d9228691e3d4c93c4b5af2febf0ad81772`;
- `lean/LEAN-28-order.md` `65e13493df7cd07962fe559f79419a6f05f09c1505b9217e8e0f211ffcd2c8e6`;
- `lean/LEAN-28-report.md` `9e10dcf0a3a4d6ca7957204074cd3cec53b1a22cbfc6a89a730316b345a93ccb`;
- `lean/VACUITY-3-order.md` `fdbc708c94a9590073d3fa8007072952bb820ef813e1423d10455a4bf29e1617`;
- `lean/VACUITY-3-report.md` `f5a685bfa47740b8c9d6534f7db58ef7dfafb1f6e483a8e11a82ee20445ab106`;
- `lean/VACUITY-3-ruling-3.md` `aa0d17e403031b81d0e0803c3308002ed985b416d788980de0f61cc79e13a4f2`;
- LEAN-16-order.md `d494728c561a922b1227587395f9650f33dd3182791620e7a0d0fb6469f3120e`;
- `~/lean/lean27-checks/dev/Junk79.lean`
  `676715efb060e3ac1b21d45e97e58423b627aa776760272617de7840f70a6a32`;
- in the repository at `20303cd`:
  - `ClassicalLean/Probability/LongestRun.lean`
    `23c55aa186a79f5baf7f2bf0f99ffede1c5f3af0acd0d2f086dc3403acfaf220`;
  - `ClassicalLean/Analysis/Simpson.lean`
    `eb3d8b1011169de5adee42ed201a825e349b5c808686faeec01d20bd6e4c8d7a`;
  - `ClassicalLean/Analysis/EulerMethod.lean`
    `9598133982f4bbcb02e635c4d3e9f5108b260453f74e238df28caf6a1899ab2a`;
  - `ClassicalLean/Probability/GamblersRuin.lean`
    `d83350169ced679ea127f0897b367b953b5a9c181499963614949576564c582e`;
  - `ClassicalLean/NumberTheory/LucasSequence.lean`
    `64df293000495c27b83e9ed14bb16f64bb8bebb006b2daf03c481ca0af45095c`;
  - `ClassicalLean/Analysis/ConvexConjugate.lean`
    `8b6eac39c6a402a8b0a5c751d1de1919c4f0d89cadcd37b823ca244a0f174731`;
  - `ClassicalLean/NumberTheory/PrimitiveDivisor.lean`
    `024ba69968d35f5579796c6428e9af798f3c2c4afb2aca93defb61ebb7be35f2`;
  - `ClassicalLean.lean` `c6930cca282aaea7054829be76bfa6cc5479301820a07c3a5aa476c5d2e426af`;
  - `HANDOFF.md` `de8d17dc9798cd9e6ec1b2912ba7b17d0053c835a0083f55f140cc6d762217a5`;
  - `tools/vacuity_reviewed.txt`
    `b5d168d4474375cbba3d5fd29948da316109b4323fa768af433b71df29fa8bde`.

Then read:
- **In the lane:**
  - MATH-PLAN-library-2.md: section 5's "Batch 3" table, section 6's rows 91 to 95, section 7's
    table header, and section 8 in full;
  - LEAN-28-order.md's sections "Scope", "Setup", "Job 2" and "Job 4" (this order follows them
    where it does not say otherwise), and LEAN-28-report.md in full (the report's model; its
    "Item 84" table is item 95's source of rows);
  - VACUITY-3-order.md's "Rules for this order", rules 2 and 3 (the witness form, now standing);
    VACUITY-3-report.md's "In short" and "Ruling 2"; VACUITY-3-ruling-3.md in full;
  - MATH-PLAN-library-2-bridges.md (row 154, the last bridge found);
  - the "Known traps" section of LEAN-16-order.md;
  - `lean/README.md`;
  - `lean/LEAN-29-checks.py`'s docstring (its predictions are this order's exact rows).
- **In the repository:** HANDOFF.md §4 and §6 (rules 17, 20, 27 and 31 apply: reviewer outputs
  saved verbatim with their sha256; scratch files elaborated with the lakefile's options; a count
  Lean generates predicted by a Lean measurement; no statement drafted before its searches and
  cells, which this order and its checks supply), records/README.md, round 58's fragment, the
  sources of the four modules, of LucasSequence, ConvexConjugate and PrimitiveDivisor, and
  `~/lean/lean27-checks/dev/Junk79.lean`.

Which steps of the plan's section 8 apply: all of them, with the gates of step 9 as LEAN-28 and
VACUITY-3 ran them (six: build, AxiomGate, VacuityGate, check_sorry, check_records, gate 7; the
banned-vocabulary scan is retired, as in LEAN-28).

## Rules for this order

1. **The gate as VACUITY-3 left it** (HANDOFF.md §4). A flag or an UNCHECKED verdict on a main
   theorem is a stop. On a helper: rewrite it, remove it if Mathlib or `simp` already does its job,
   or list it in `tools/vacuity_reviewed.txt` as HELPER with a one-line reason its module's cold
   reviewer checks (2c). A VACUOUS-PENDING entry is a stop. The known gap stays: a recursive
   all-`True` predicate (`NatT2`) passes silently; each module's cold reviewer checks that no main
   theorem's conclusion is such a predicate and says so, and the report tool's section C after the
   work still shows 0 recursive.
2. **Witnesses, in round 58's standing form.** Every new main theorem with a hypothesis gets a
   witness: VACUITY-3's rule 2 (an `example` after the module's last line that applies the theorem
   itself, `example := Full.name (x := …) h₁ h₂ …`, every chosen argument by name, an optional
   `open … in` line of its own, the docstring "The hypotheses of `name` hold together: …", no
   `sorry`, `admit`, `native_decide`, `implemented_by`, `axiom` or `set_option`, and one inline
   block with no helper declarations, as VACUITY-3's ruling 3, item 2, keeps it) and VACUITY-3's
   rule 3 (not degenerate), with the two cases VACUITY-3's ruling 3 adds: no hypothesis may be met
   only because a function is identically `0` past some point, and no kernel or observation may
   fail to depend on the parameter it is about. Six witnesses are owed: 91, both of 92, both of 94,
   and 95 (93 has no hypothesis). The `∃` form of LEAN-27 and LEAN-28 is not used. Ruling 3 gave
   the filing of those two cases to the next gate order; this order files them in HANDOFF.md §4
   instead (job 3), because it is the first to write witnesses under them, and the gate order keeps
   only their use on rows 7, 8 and 70 (claude-ai's ruling, Dustin's veto open).
3. **A claim in the library is checkable from the library** (the ruling of 2026-10-13, store row
   20261013-014). No docstring, record or report line says a case was "checked in Lean" unless the
   check is an `example` in the module. A dropped-hypothesis row's evidence is one of: an `example`
   in the module; a labelled line of `lean/LEAN-29-checks.py` or of your own checks script, named
   by label; or "by hand", said so.
4. **Narrowing and widening are said the same way everywhere** (LEAN-28's rule 4). Before the last
   records commit, the INDEX row, round 59's completed section and the report's "In short" each
   name every narrowing of this order, or say "none", and each names item 95's widening. Check it
   on the report's draft: `grep -n -i -E 'narrow|wider' <round 59 fragment> <report draft>` and
   `grep -n -i -E 'narrow|wider' records/orders/INDEX.md | grep 'LEAN-29'`; paste the output into
   the report. INDEX rows start `| LEAN-NN |`.
5. **Method A carries LEAN-28's lesson:** one `field_simp` made 8 `_simp_` helpers where 2 were
   guessed (LEAN-28's miss of 5). Count the old import closure with every module VACUITY-3 left.
6. **A question to Dustin holds only its own outcome open** (LEAN-28's rule 2). Don't apply your
   own answer before he replies; the work it does not touch goes on.
7. **Stops inside an item.** A witness still missing after about 30 minutes of attempts, or a
   module not clean after two fix-and-confirm review rounds, makes that item not closed: its
   changes are reverted before job 3 and the other items go on (LEAN-28's 2d). Never weaken,
   restate or add a hypothesis to get a witness; item 95's stop rule below is the one planned
   restatement.

## Before approval (read-only in the repository)

1. `git fetch origin` in the worktree. origin/master and `git ls-remote github master` must both be
   `20303cd` (`20303cd4eb902e15b2d4994ea6aa2263f5146264`), and `git status --porcelain` must be
   empty. If not, stop and report.
2. Check the hashes above and read the read list.
3. Check the night jobs and `free -g`.
4. Write your plan to `lean/LEAN-29-PLAN.md`: the jobs in order, every prediction you can already
   make, and the order of the items. Then stop and wait for Dustin's approval.

## Setup (after approval)

1. **Branch.** `git switch -c lean-29 20303cd`.
2. **Evidence folder** `~/lean/lean29-checks/`, with `evidence.log` (time, label, rc, prediction,
   command). Every prediction file is hashed into the log before the run it predicts; hashes go
   into records and the report by script, never typed; every compile-fix run through `el.sh` is
   logged; every refused or not-run call is logged `NOT RUN` (HANDOFF.md §6 rule 30). Extract
   Appendix A's six files byte for byte into `~/lean/lean29-checks/appendix/` and check their
   sha256 against the appendix.
3. **Records first.** The first commit on `lean-29`, with no `.lean` file:
   - this order's copy as
     `records/orders/<UTC>__claude-ai__order-lean29-runs-exp-gruss-richardson-euler-stability-ruin-lucas.md`;
   - its INDEX row and a CLAIMS row;
   - round 59's fragment, which names in full every module file this order changes, the new
     module's file by its full path (written there for the first time: this order does not write
     it, so that check_records cannot pass on the order's copy alone), and `ClassicalLean.lean`.
   check_records then: PASS 122 (the new module does not exist yet).
4. **The before runs, at the records commit**, predicted from the facts:
   - build rc 0, 4170 jobs, 0 warnings;
   - AxiomGate PASS 3228: the base for job 1's blind prediction;
   - the report tool, rc 0: 1785 written; A 1027 (0 / 988 / 39); B 758 (16 close); C 33, 0
     recursive; saved as `report-before.out` for job 4b.
5. **The plan's checks**, with `--lean`, using `~/lean/vacuity2-checks/mm` (at `2da3ab0a`).
   Predicted: 192 of 232, the 40 misses exactly those in the facts (copy the list into your
   prediction file line by line; `setup.worktree`'s measured value will be your records commit,
   not `20303cd`), and every line of rows 91 to 95 a hit. Only a miss on a row 91
   to 95 line means Mathlib or the library has that row by now: drop that row and say so. A
   `setup.*`, `gate.*`, `census.*`, `used.*` or `bridges.*` miss never drops a row.
6. **The exact checks:** `python3 -I` on the lane's `lean/LEAN-29-checks.py`. Predicted: 23 of 23
   checks hit, 3 BY HAND lines, rc 0, output sha256
   `599b0099294fbeb01c748825e452a051dbe64a093afa1418c7c8c61d3933e3e1` (claude-ai's run on DSMain
   gave exactly that). A different output hash with 23 of 23 is reported, not a stop.
7. **The statements:** elaborate A2 to A6 from the worktree root with rule 20's four flags
   (`-Dpp.unicode.fun=true -DrelaxedAutoImplicit=false -Dweak.linter.mathlibStandardSet=true
   -DmaxSynthPendingDepth=3`). Predicted: rc 0 each, and only `declaration uses sorry` warnings,
   1, 2, 1, 2, 1.

## The work

Job 0 comes first; it touches no statement of items 91 to 95. Items 91 to 95 then go through jobs
1 to 4 together.

### Job 0: the two older docstring lines (store row 20261013-017, item 2)

- **ConvexConjugate, line 34.** Move the 7 examples of `~/lean/lean27-checks/dev/Junk79.lean` into
  the module, after its last line, each with a one-line docstring saying what it shows; keep each
  statement as it is, and the module's own names. If an example needs a module the file does not
  import, add that import only if the module is already in the library's import closure (A1 tells);
  otherwise leave that one example out and say so in the docstring. Then rewrite line 34 and the
  sentences after it to name the examples at the end of the file instead of the scratch file.
- **PrimitiveDivisor, line 286.** Either state the stronger form (`0 < a` in place of `2 ≤ a`) as
  an `example` at the end of the module, applying the theorem to the case split the line describes,
  if it closes within about 30 minutes; or reword the line to say who elaborated the stronger form
  and where, as far as the records show (they show only that the text is in the initial commit
  `333b69a`, with no file kept), and that it is not stated in the library. Say which in the
  report.
- Neither module's theorems, definitions, proofs or count of theorem constants changes; check that
  by a census of the two modules before and after (LEAN-28's `census3_*` method), predicted equal.
- One fresh cold reviewer reads the diff of the two files only, with this section as its brief,
  about 15 calls; its confirming pass closes the job.

### Item 91, `ClassicalLean.Probability.LongestRun`

- **Import:** add `import Mathlib.Analysis.Complex.Exponential` (facts).
- **Route** (A2 probes every name): when `n / r = 0` the bound is `exp 0 = 1` and the chance is at
  most `1` (`iIndepSet.isProbabilityMeasure`, `measureReal_le_one`). Otherwise `r ≥ 1` and
  `n ≥ r ≥ 1`, so `q = P.real (A 0)` lies in `[0, 1]` (`measureReal_nonneg`, `measureReal_le_one`);
  then `measureReal_no_run_le`, `0 ≤ 1 - q ^ r ≤ exp (-(q ^ r))` (`Real.one_sub_le_exp_neg`),
  `pow_le_pow_left₀`, and `Real.exp_nat_mul` to turn `exp (-(q ^ r)) ^ m` into the stated form.
- **Rows** (`lean/LEAN-29-checks.py` labels): `hA`, by hand, LEAN-28's case for the old bound
  (`Bool` with the σ-algebra `⊥`, the point mass at `true`, `A 0 = {true}`, `n = r = 1`, `q = 1`):
  chance `1` (Lean's `P.real` of a non-measurable set is its outer measure) against `exp (-1)`
  (`91.drop.hA`; the module's second `example` already shows the chance is `1`). `hind`:
  `91.drop.hind`, first failing cell `(n, r, q) = (2, 1, 1/10)`, every trial the same event.
  `hq`: `91.drop.hq`, first failing cell `(1, 1, 1/10)`, every event empty with `q` stated.
  Junk values that decide nothing but must be named: `n / r` in `ℕ` (`n / 0 = 0`, the bound is
  then `1`), `q ^ 0 = 1`.
- **Witness:** row 81's model (two fair flips on `Fin 2 → Bool`, `P = (1/4) • count`,
  `A i = {ω | ∃ h : i < 2, ω ⟨i, h⟩ = true}`, `q = 1/2`) with `n = 2`, `r = 1`, so that `n / r = 2`
  blocks and not one (the reviewers of VACUITY-3 called `n = r = 2` weak).
- **Docstring:** state the reading for fair trials (`q = 1/2`: the chance of no run of `r` losses
  is at most `exp(−⌊n/r⌋ / 2^r)`, small once `n/r` is large compared with `2^r`) as a reading of
  the theorem, not as a second theorem.

### Item 92, the new module `ClassicalLean.Analysis.Gruss`

- **The module.** Namespace `ClassicalLean.Analysis`; copyright header and module docstring as the
  library's other modules have them; the name in ASCII, "Grüss" in prose. Drafted imports (A3):
  `Mathlib.Probability.Moments.Variance` and
  `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`.
  Any other import must already be in the closure (run A1 with it); one that is not changes job
  1's job count and is said. `ClassicalLean.lean` gains `import ClassicalLean.Analysis.Gruss`.
- **Route for the first theorem.** Mathlib v4.34.0 has no Cauchy–Schwarz inequality for the
  covariance (`row.C2`'s second search, 0 lines; none of the lemmas in
  `Mathlib/Probability/Moments/Covariance.lean`, listed by claude-ai's grep of its `lemma` lines,
  is such a bound). Two routes, both from Popoviciu's inequality `variance_le_sq_of_bounded`
  (`Var X ≤ ((M - m) / 2) ^ 2`):
  - (a) the textbook one: `|cov| ≤ ∫ |X − EX| |Y − EY| ≤ √Var X · √Var Y` by
    `integral_mul_le_Lp_mul_Lq_of_nonneg` with `p = q = 2` (`memLp_of_bounded` gives the
    integrability), then Popoviciu on both;
  - (b) derived here, without square roots: for `t > 0`, `2 |u v| ≤ t u² + v² / t`; integrate, use
    Popoviciu on both, and take `t = (N − n) / (M − m)` when `M > m` and `N > n`. When `M = m` or
    `N = n`, that variable is almost everywhere constant, the covariance is `0` and so is the
    bound. Route (b) also needs the variance written as an integral, `|∫ φ| ≤ ∫ |φ|`, and the
    covariance of an almost-everywhere-constant variable; none of these is probed in A3: find and
    probe each first.
  Use either; say which.
- **Route for the second theorem.** The uniform probability on `[a, b]`,
  `ProbabilityTheory.cond volume (Set.Icc a b)`, which Mathlib defines as
  `(volume (Icc a b))⁻¹ • volume.restrict (Icc a b)`
  (`Mathlib/Probability/ConditionalProbability.lean` line 76). It is a probability measure by
  `cond_isProbabilityMeasure_of_finite` (both `≠ 0` and `≠ ∞` needed: Lebesgue measure is not
  finite, so `cond_isProbabilityMeasure`, which asks `[IsFiniteMeasure μ]`, does not apply; cold
  review 1), with `Real.volume_Icc`
  (`volume (Icc a b) = ofReal (b − a)`). Apply the first theorem with `X = f`, `Y = g`; then turn
  its covariance into the statement's left side: `covariance_eq_sub` (`cov[X, Y; μ] =
  ∫ (X * Y) − (∫ X) * ∫ Y` for a probability measure, given `MemLp X 2 μ` and `MemLp Y 2 μ`, which
  `memLp_of_bounded` supplies), then `integral_smul_measure`
  (`∫ x, f x ∂(c • μ) = c.toReal • ∫ x, f x ∂μ`), `ENNReal.toReal_inv` and `ENNReal.toReal_ofReal`
  (so `((ofReal (b − a))⁻¹).toReal = (b − a)⁻¹`), `integral_Icc_eq_integral_Ioc` and
  `intervalIntegral.integral_of_le`. All of these are probed in A3 (cold review 2 found the
  covariance step missing).
- **Rows, first theorem:** the probability measure, `92.drop.prob` (mass `0`, where the bound
  hypotheses are empty, so `M < m` is allowed: `0` against `−1/4`; masses `1/2` and `2` with
  `X = Y = 1`: Lean's covariance `c (1 − c)²` against `0`); the bound on `X`, `92.drop.bnd` (and on
  `Y`, the same with the roles swapped); measurability: `92.drop.meas`, by hand (`Bool` with `⊥`,
  the point mass at `true`, `X` = `1` or `2`, `Y = 2 / X`: Lean's integrals of `X` and `Y` are `0`,
  `X Y = 2` is measurable, covariance `2` against `1/4`). That case drops both measurability
  hypotheses at once. With only `hX` dropped there is no case (cold review 1, by hand; check it):
  if `X (Y − E Y)` is not integrable, Lean's covariance is `0`, within the bound; otherwise let
  `X'` be `X` where `Y ≠ E Y` and `m` elsewhere; `X'` is almost everywhere measurable, lies in
  `[m, M]`, and `cov[X', Y] = ∫ X (Y − E Y) = cov[X, Y]`, so the theorem for `X'` gives the bound.
  The same holds with `hY` alone. So the row says "needed together", with that argument.
- **Rows, second theorem:** `hab`, `92.drop.hab` (`a = 1`, `b = 0`: the interval is empty, the
  bound `−1/4`, the left side `0`; and at `a = b` every interval integral is `0`, so the left side
  is `0` whatever `0⁻¹` is and the statement holds: say so in the row); the bound on `f`,
  `92.drop.fbnd` (`f = g = x` on `[0, 1]`, `m = M = 0`: `1/12` against `0`), and on `g` likewise;
  integrability, each alone, `92.drop.fmeas`, by hand: on `[0, 1]`, `f = 1 + 1_V` with `V` a subset
  of `(1/2, 1]` that is not Lebesgue measurable, `g = 1_[0, 1/2]`; Lean's integral of `f` is `0`,
  of `f g` and of `g` `1/2`, so the left side is `1/2` against `1/4` (and `g`'s likewise, the
  roles swapped).
- **Exact cases:** `92.prob` (200 finite laws), `92.equal` (equality at a fair two-point law on
  `{m, M}`), `92.fun` (200 step functions, and `f = g = x` on `[0, 1]`).
- **Witnesses:** for the first theorem a space of at least two points with `X` and `Y` not
  constant; for the second, continuous `f` and `g` on an interval of positive length (for example
  `f = g = id` on `[0, 1]`), neither constant.

### Item 93, `ClassicalLean.Analysis.Simpson`

- **Import:** add `import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule` (facts).
- **Route:** `N = 0`: both sides are Lean's `0` (`(b − a)/0 = 0` in both definitions). `N ≥ 1`:
  unfold both; the nodes agree as reals (`a + 2 k ((b − a)/(2N))` is Mathlib's
  `a + (2k) (b − a) / (2N)`); split the trapezoidal rule's interior sum for `2N` steps into its odd
  nodes `2k + 1` (`k < N`) and its even nodes `2k + 2` (`k < N − 1`), the latter being the interior
  nodes of the rule for `N` steps. The identity holds for every `a`, `b` (`93.richardson`: 360
  exact cases with `f` arbitrary at every node, `a > b` and `a = b` included).
- No hypothesis, so no rows and no witness. The docstring says the rule is Richardson
  extrapolation of the trapezoidal rule: it removes the `h²` term of the trapezoidal error.

### Item 94, `ClassicalLean.Analysis.EulerMethod`

- **Route:** implicit: by induction `u k = u 0 * ((1 + h c)⁻¹) ^ k`, `0 < (1 + h c)⁻¹ < 1`, then
  `tendsto_pow_atTop_nhds_zero_of_lt_one` and `Tendsto.const_mul`. Explicit: by induction
  `eulerIterate (fun _ y ↦ -c * y) t₀ h y₀ k = (1 - h * c) ^ k * y₀` (`94.closed`, exact for
  `k ≤ 12`); forward, divide by `y₀` (`Tendsto.div_const`) and use
  `tendsto_pow_atTop_nhds_zero_iff` and `abs_sub_lt_iff`; backward, `0 < h c < 2` gives
  `|1 − h c| < 1`. The module has no `open Filter Topology`; put `open Filter Topology in` before
  each theorem's docstring.
- **Rows:** explicit: `hc`, `94.drop.ehc` (first failing `(c, h, y₀) = (−1, 1/2, 1)`); `hh`,
  `94.drop.ehh` (`(1/2, −1, 1)`); `hy₀`, `94.drop.ey0` (`(1, 3, 0)`). Implicit: `hc`,
  `94.drop.ihc` (`(c, h) = (−1, 1/2)`, factor `2`); `hh`, `94.drop.ihh` (`(h, c) = (−1, 1/2)`);
  `hu`, by hand: `u k = 1` for every `k`, with `c = h = 1`, tends to `1`, not `0`. Junk
  value to name in both implicit rows: when `1 + h c = 0` Lean's `x / 0 = 0` makes `u 1 = 0`, and
  the sequence then tends to `0` (the cells `(−1, 1)` of both checks).
- **Witnesses:** implicit `c = 1`, `h = 1`, `u k = (1/2) ^ k`; explicit `c = 1`, `h = 1/2`,
  `y₀ = 1`, `t₀ = 0` (factor `1/2`; with `h = 1` the factor is `0` and the iterate is `0` from
  step 1 on, the degenerate case ruling 3 names; cold review 1).

### Item 95, `ClassicalLean.Probability.GamblersRuin`

- **Import:** add `import ClassicalLean.NumberTheory.LucasSequence` (no cycle; already built). The
  theorem goes in section `Biased`, after `measureReal_exists_ge_le_of_biased`.
- **Route:** write `r = (1 − p) / p`.
  - `p ≠ 1/2`: `measureReal_hit_eq_of_biased`, and `lucasU_of_roots` at `α = r`, `β = 1`
    (`(r − 1) * lucasU (r + 1) (r * 1) n = r ^ n − 1`; rewrite `r + 1` and `r * 1` to the
    statement's `1 + r` and `r`), with `r ≠ 1`.
  - `p = 1/2`: `r = 1`; `lucasU 2 1 n = n` by `Nat.twoStepInduction` and `lucasU_add_two`; the
    chance is `b / (a + b)` by `measureReal_hit_eq`, whose `∫ X n = 0` comes from `hp` through the
    module's private `integral_comp_step` (`∫ X n = 2 p − 1`), as `ae_exitTime_ne_top_of_biased`
    does.
  - **Stop rule:** if the `p = 1/2` case does not close within about 30 minutes, add
    `(hp2 : p ≠ 1 / 2)`, which is item 84's reading, say so as a narrowing of this order's
    statement (not of the plan's), and go on.
  - `measureReal_hit_eq`'s full statement, as A6's probe prints it: hypotheses `hX`, `hind`, `hpm`
    as here and `(∀ n, ∫ ω, X n ω ∂μ = 0)`, for all `a b : ℕ`, the same event, equal to
    `↑b / (↑a + ↑b)`.
- **Rows:** `hp0`, `95.drop.hp0` (`p = 0`, `a = b = 1`: chance `0` against `U 1 / U 2 = 1`; junk:
  `r = 1/0 = 0`; the same cell as item 84's row). `hp1`: not needed (`95.p1`: at `p = 1` the
  formula is right in every cell; `p > 1` cannot happen, since `hp` makes `p` a probability),
  kept because the route goes through item 84, as item 84's row says. No `p ≠ 1/2` (`95.grid`'s
  `p = 1/2` cells). The others carry over from the rows of item 84's **second** theorem in
  LEAN-28's report (its table mixes the three theorems), since for `p ≠ 1/2` the right side is item
  84's (`95.item84`). claude-ai's cells, by hand, at `p = 1/3` (`r = 2`, `U = lucasU 3 2`):
  - `hX`: the filtration that knows nothing (`⊥`), with every step equal to the first: `hind`
    holds, `hX` fails; at `(a, b) = (1, 2)` the chance is `1/3` against `U 2 / U 3 = 3/7`;
  - `hind`: the steps' natural filtration with every step equal to the first: `1/3` against `3/7`;
  - `hpm`: steps `+1` with chance `1/3` and `−2` otherwise, `(a, b) = (1, 2)`: `1/3` against `3/7`;
  - `hp`: fair steps with `p = 1/3` stated, `(a, b) = (1, 1)`: `1/2` against `U 1 / U 2 = 1/3`;
  - the probability measure (an instance of the section): follows from the others, by hand, as
    LEAN-28 says for item 84's second theorem.
  Check each cell in your own checks script before you write the row.
- **Witness:** preferably a biased model (`p = 1/3`), adapted from row 51's witness of
  `measureReal_hit_eq` at the end of the module (`Measure.infinitePi` of `uniformOn Set.univ`,
  `Filtration.natural`, `iIndepFun_infinitePi`): take the coins in `Fin 3` instead of `Bool`
  (`Ω := ℕ → Fin 3`) and the step `+1` when the coin is `0`, so `p = 1/3` with a law Lean already
  knows is a probability measure. (`PMF.bernoulli` is not visible through the module's imports,
  measured.) Item 84's own `∃` example at `p = 1/3` (from `exists_iid`) shows the hypotheses hold
  but cannot be a rule-2 witness, which names every argument. If the biased model does not close
  within the 30 minutes, row 51's fair model at `p = 1/2` is allowed (the theorem covers it), and
  the docstring says why it was used.

### Job 1, predictions (section 8, step 4)

- **The job count:** inferred 4171 (the facts: one new module, no new Mathlib module). Confirm by
  A1 with the import lines as you finally write them, before any build.
- **The theorem constants, blind:** Method A from the source, then Method B by a census of scratch
  copies, both before any gate; base 3228; rule 5. Job 0 adds none (examples).
- **The bridge diff** before its run (job 4a): the new module's pairs and its shapes (the shape
  candidates of `shapes.tsv`, 535 at the baseline); whether the new GamblersRuin–LucasSequence edge
  removes any listed pair or shape (measured: neither file names both modules, and only the root
  imports GamblersRuin, so none); pairs gone because shared constants cross the document-frequency
  cut (LEAN-28's miss: 41 such).
- **The plan's checks after the work** are not re-run as a gate. If you re-run them, expect these
  to turn into misses as the work lands: `trackL.L19` (LongestRun gains an `exp` bound), and the
  library counts of `row.C2`, `row.F4`, `row.F5` and `row.X4` once the new docstrings use their
  words.

### Job 2, statements, hypotheses and reviews (section 8, steps 5 to 8)

Start from A2 to A6 (the statements are final there unless a review changes them). With:
- **2a.** Every new main theorem with a hypothesis gets its witness (rule 2), checked by its
  module's cold reviewer against rule 3.
- **2b.** Lean's junk values named in every row where they decide the case (the rows above name
  them).
- **2c.** A vacuity flag on a short helper that only restates a definition is not a stop: remove
  it, or list it as HELPER (rule 1). A flag or UNCHECKED on a main theorem, or a VACUOUS-PENDING
  entry, is a stop.
- **2d.** Every review ends with a confirming pass on the fix diff only; at most two
  fix-and-confirm rounds (rule 7). A reviewer may elaborate at most two small Lean files, each
  under `systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=0`. A witness or a docstring
  that comes from a reviewer gets its confirming pass from a different, fresh reviewer (VACUITY-3's
  ruling 2).
- **2e.** A narrower statement than this order's is said plainly in the module docstring, the
  report's item line and the hypothesis table, and rule 4 holds. A row whose statement turns out
  false is reported with its counterexample and narrowed, never dropped silently.
- **2f.** Each new theorem's docstring names the plan's item, and each module docstring's list of
  results gains the new theorems.

### Job 3, documents

- `HANDOFF.md`: §1, a dated LEAN-29 paragraph with the counts; the module lists where they list
  modules (the new module); §4's witness paragraph, ruling 3's two rule-3 cases and its "one inline
  block, no helper declarations" (rule 2 here), dated, citing `lean/VACUITY-3-ruling-3.md` and
  saying that LEAN-29 filed them in place of the next gate order.
- `ROADMAP.md`: batch 3, after LEAN-28's batch 2 section.

### Job 4, the end checks, in this order

- **4a. The bridge search:** `tools/bridge_search.py --diff records/bridges/LEAN-28/` under the
  cap, on a clean commit of jobs 0 to 3; rc 1 means candidates to review. Report NEW and GONE keys
  against job 1's prediction, pairs and shapes; check each NEW import-unrelated pair and each NEW
  shape by hand for a theorem whose proof needs both sides (LEAN-28's real bridge, row 154, was a
  new shape); a real one gets an item number from 155 on and goes into a new lane file,
  `MATH-PLAN-library-2-bridges-2.md` (row 154 copied in first, then the new rows, the plan's section
  7 columns); it never enters this batch. Say for each whether it is load-bearing for a scheduled
  row (items 96 to 110); only that re-draws the cut, at a batch boundary. Write the new baseline to
  `records/bridges/LEAN-29/`; its commit touches only `records/`.
- **4b. The report tool**, under the cap, on the same clean commit: a report, not a gate. Predicted
  from `report-before.out` and job 1: written theorems 1785 plus the hand-written theorems this
  order adds; section C still 0 recursive. List every `CLOSES` line that names a theorem of this
  order, for Dustin to read; none is expected for a main theorem.
- **4c. Commit everything above. Then the six gates** on the clean tree, predicted first: build rc
  0, 4171 jobs (or job 1's corrected count), 0 warnings; AxiomGate PASS at job 1's count;
  VacuityGate PASS, no new flag (or job 2's listed helpers), 0 VACUOUS-PENDING, 0 run-outs, no
  UNCHECKED, and its tests unchanged (89, 47 flagged, 3 UNCHECKED as expected, 0 mismatches);
  check_sorry PASS 123; check_records PASS 123; gate 7 under the cap
  (`systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0 ~/lean/recheck/run-recheck.sh <commit> ~/lean/classical-lean-paper-crypto`):
  ALL PASSED, 4171 jobs, 123 modules 0 failed, the theorem count, three standard axioms, planted
  fault named. After the gates, only commits that touch nothing outside `records/` are allowed.
- **4d. Report** `lean/LEAN-29-report.md` through ds_write_staging, post_sha256 compared with your
  own sha256sum, laid out like LEAN-28-report.md: in short; setup; job 0; each item with its
  statements, hypothesis table, witness, review and any narrowing or widening; rule 4's grep
  output; predicted beside measured for jobs, constants, the report tool and every gate; list
  entries with reasons; the bridge diff and the baseline; documents changed; commits; misses and
  not reached; the push command as one line, not run:
  `cd ~/lean/classical-lean-paper-crypto && git push origin lean-29:master && git push github lean-29:master`.
- **4e. Push-review file** `lean/LEAN-29-push-review.txt` through ds_write_staging, written by one
  script from the repository as it is after the last commit, each command followed by its full
  output: `git rev-parse HEAD`, `git status --porcelain`, `git ls-remote origin master`,
  `git ls-remote github master`, `git merge-base --is-ancestor 20303cd HEAD` with its exit code,
  `git rev-list --count 20303cd..HEAD`, `git log --name-only --format='== %h %cI %s' 20303cd..HEAD`,
  and `git show` of every commit after the last confirming review, and of every commit that touches
  a module after that module's own last confirming pass (files under `records/bridges/` as
  `--stat` only). Report its sha256. Then stop. claude-ai reviews it before Dustin pushes.

## Done means

- Branch `lean-29` from `20303cd`, clean tree, nothing pushed; its first commit is the records
  commit and holds no `.lean` file; every prediction hashed in `evidence.log` before its run;
  hashes in records written by script; `el.sh` runs logged.
- Job 0: ConvexConjugate's line names checks that are `example`s in the module (or says plainly
  which are not, and why); PrimitiveDivisor's line is either an `example` or a plain statement
  that the scratch check was not kept; both modules' theorem constants unchanged, by census; the
  job's review closed by a confirming pass.
- Items 91 to 95 proved with no `sorry` and no new axiom, as stated here, or each narrowing said
  plainly with its reason; item 95's widening said in the module docstring, the report, the INDEX
  row and round 59; any dropped row named with the line that has it; any item not closed after two
  review rounds reported, its changes reverted.
- Six witnesses in rule 2's form, each checked by its module's reviewer against rule 3 with ruling
  3's two cases; every hypothesis has a dropped-hypothesis row whose evidence is an `example`, a
  labelled check or "by hand" (rule 3), with Lean's junk values where they decide the case.
- Each changed module had its cold review after its statements were final, ending with a
  confirming pass, and each review answered rule 1's check; any statement changed after its review
  had a statement-equivalence review.
- Every reviewer's and checker's output saved verbatim with its sha256 in the evidence folder
  (HANDOFF.md §6 rule 17), and `~/.claude/agent-memory/` hashed before the first review and after
  the last.
- Every new vacuity-list entry named in the report with its reason and its reviewer's check; no
  VACUOUS-PENDING entry and no UNCHECKED verdict in the library.
- The job count and the constant count predicted (blind, before any census) beside measured.
- Job 3's documents changed and named; rule 4's three files agree and the grep is in the report.
- The report tool's run reported (4b).
- All six gates as predicted, or each miss reported; gate 7 ALL PASSED on the last commit that
  touches anything outside `records/`, and later commits touch only `records/`.
- The bridge diff run and reported against its prediction; the new baseline committed and named.
- The report and the push-review file are in `lean/` and their hashes match yours.

Then report in a few plain sentences: what was proved, any narrowing and the widening, the gate
results, the new list entries, the two files' hashes and the push command. Dustin reads your
replies carefully and is still learning to read code: use plain words and define a technical term
the first time you use it. When you need a decision from him, ask in one line with your recommended
answer first.

## Not in this order

- Rows 7, 8 and 70's witnesses, the report tool's outer heartbeat budget, and the gate's FAIL text
  (case 5, the meaning of UNCHECKED and KERNEL-REJECTED): the next gate order (VACUITY-3's ruling
  3). This order applies ruling 3's two rule-3 cases to its own new witnesses and files them in
  HANDOFF.md §4 (rule 2); it does not revisit old witnesses.
- Rows 9, 10, 67, 31 and 32 (the infinite independent family and the AR(2) process): the later
  order ruling 3 names.
- EffectiveSampleSize's line on order LEAN-16's identity (reworded by LEAN-28; not one of the two
  lines of store row 20261013-017).
- Items 96 to 110 (LEAN-30 to LEAN-32), and row 154 of the bridges file.
- The main clone, `~/trading`, `~/lean/recheck`, Dustin's `banned-terms` file, and any push.

## Revisions

- r1 (cold review 1, PASS WITH FINDINGS, 0 BLOCKER, 2 MAJOR, 15 MINOR; all applied):
  - MAJOR: item 92's second statement left its first integral unbracketed, so Lean read the whole
    left side as one integral; every integral is now bracketed, and A3 holds an `example … := rfl`
    showing how Lean reads `∫ x in a..b, f x - C` (elaborated, rc 0). A falsified claim of
    claude-ai's draft, logged in the store (row 20261014-008).
  - MAJOR: item 92's second route cited `cond_isProbabilityMeasure`, which needs a finite measure;
    now `cond_isProbabilityMeasure_of_finite`, `integral_smul_measure` and `Real.volume_Icc`, all
    probed in A3, with Mathlib's definition of `cond` quoted.
  - MINOR: rows added or settled: item 94's `hu`; item 92's measurability (needed together, with
    the reviewer's argument) and integrability (each alone, `92.drop.fmeas`); item 95's rows
    narrowed to item 84's second theorem, with a cell for each and `p > 1` excluded by `hp`;
    item 92's `a = b` reason corrected.
  - MINOR: the check script's by-hand cases print `BY HAND` and are not counted; `92.drop.fbnd`
    computes its value (now 23 checks; output hash the same on DSMain and in the cloud).
  - MINOR: item 94's explicit witness moved to `h = 1/2` (factor `0` at `h = 1`); item 95's
    witness points to a `Fin 3` model (`PMF.bernoulli` measured not visible); rule 2 gains "one
    inline block, no helper declarations"; item 95's `p = 1/2` case time-boxed.
  - MINOR: the probe sentence, route (b)'s `N = n` case, `measureReal_hit_eq`'s statement, the
    unattributed lemma count, job 0's scope ("the library's import closure", `open … in`),
    PrimitiveDivisor's sentence quoted in full with "who and where", the bridge prediction's
    shapes and the measured importers of GamblersRuin, Done-means' rule 17 line, setup 5, 6 and 7's
    predictions, ruling 3's filing taken over (said in rule 2), "N panels", A2's comment.
- r2 (cold review 2, PASS WITH FINDINGS, 0 BLOCKER, 0 MAJOR, 2 MINOR; all 17 of r1's fixes
  confirmed; both new findings applied, not re-reviewed):
  - item 92's second route gains the step from the covariance to `E[f g] − E f · E g`
    (`covariance_eq_sub`, with `memLp_of_bounded`) and the two `ENNReal` steps, all now probed in
    A3 (re-elaborated, rc 0, 2 `sorry` warnings);
  - the new GamblersRuin–LucasSequence edge checked against `shapes.tsv` as well as `pairs.tsv`
    (grep: no line names both), and job 1 says "pair or shape".

## Appendix A: the measurement files

Each block below is the file byte for byte, between its fence lines; the file ends with a newline
after its last line. `closure.py` is run from the worktree root with `python3 -I`; the `.lean`
files are elaborated from the worktree root with rule 20's four flags. On DSMain all six are in
`/tmp/claude-ai-lean29/`.

### A1: `/tmp/claude-ai-lean29/closure.py`, the import closure (facts, "Imports")

sha256 `10c080f1cfbbf470cfd5c5cda3745155e55a1a882b568af444b0a1984736df95`

```python
"""Import closure of the classical-lean library, for order LEAN-29's job prediction.

Run from the worktree root: python3 -I closure.py [Module.Name=Extra.Import,...] ...
Each argument adds imports to a module (simulating the order's new import lines); a module named
on the left that does not exist is a new module (its file is not read). Prints the size of the
closure of ClassicalLean.lean (the root) over modules found as source files in the repository or
in .lake/packages/*, core modules (Init, Std, Lean, Lake) excluded, and lists the modules the
additions bring in.
"""
import os, re, sys
ROOTS = ['.'] + sorted(os.path.join('.lake/packages', d) for d in os.listdir('.lake/packages'))
IMP = re.compile(r'^\s*(?:public\s+)?(?:private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z_][\w.]*)')
CORE = ('Init', 'Std', 'Lean', 'Lake')

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
            for line in fh:
                m = IMP.match(line)
                if m:
                    out.append(m.group(1))
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

if __name__ == '__main__':
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

### A2: `/tmp/claude-ai-lean29/S91.lean`, item 91, statement and probes

sha256 `346ac339e9d026ffd40cb6f0e59e4bd743662b0e10f88f2581c6d6b10f5734a7`

```lean
import ClassicalLean.Probability.LongestRun
import Mathlib.Analysis.Complex.Exponential

/-! Order LEAN-29, item 91: the statement with `sorry`, and the names its route cites.
`Real.exp` is not visible through `ClassicalLean.Probability.LongestRun`'s imports (measured), so
the module gains the import above; that Mathlib module is already in the library's import
closure. -/

open MeasureTheory ProbabilityTheory Finset

#check @Real.one_sub_le_exp_neg
#check @Real.exp_nat_mul
#check @pow_le_pow_left₀
#check @ProbabilityTheory.iIndepSet.isProbabilityMeasure
#check @MeasureTheory.measureReal_le_one
#check @MeasureTheory.measureReal_nonneg
#check @ClassicalLean.Probability.LongestRun.measureReal_no_run_le

namespace ClassicalLean.Probability.LongestRun

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

theorem measureReal_no_run_le_exp {P : Measure Ω} {A : ℕ → Set Ω}
    {n r : ℕ} {q : ℝ} (hA : ∀ i < n, MeasurableSet (A i))
    (hind : iIndepSet (fun i : Fin n ↦ A i) P) (hq : ∀ i < n, P.real (A i) = q) :
    P.real (runEvent A n r)ᶜ ≤ Real.exp (-(((n / r : ℕ) : ℝ) * q ^ r)) := by
  sorry

end ClassicalLean.Probability.LongestRun
```

### A3: `/tmp/claude-ai-lean29/S92.lean`, item 92, statements and probes (the new module)

sha256 `0017125cdba9e55c4e1b14ec09976c251ca3b0294a45045c5f4a7afaa981995b`

```lean
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Order LEAN-29, item 92: the statements with `sorry`, and the names their route cites. The
module is new; these are the imports it is drafted with. -/

open MeasureTheory ProbabilityTheory

#check @ProbabilityTheory.variance_le_sq_of_bounded
#check @ProbabilityTheory.variance_le_sub_mul_sub
#check @ProbabilityTheory.covariance
#check @ProbabilityTheory.covariance_self
#check @ProbabilityTheory.covariance_eq_sub
#check @ENNReal.toReal_inv
#check @ENNReal.toReal_ofReal
#check @ProbabilityTheory.variance_nonneg
#check @MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
#check @MeasureTheory.memLp_of_bounded
#check @two_mul_le_add_sq
#check @ProbabilityTheory.cond
#check @ProbabilityTheory.cond_isProbabilityMeasure_of_finite
#check @MeasureTheory.integral_smul_measure
#check @Real.volume_Icc
#check @intervalIntegral.integral_of_le
#check @MeasureTheory.integral_Icc_eq_integral_Ioc
#check @IntervalIntegrable

/-- How Lean reads `∫ x in a..b, …`: the body runs to the end of the expression, so a
subtraction after it is inside the integral. The statements below bracket each integral. -/
example (f : ℝ → ℝ) (a b C : ℝ) : (∫ x in a..b, f x - C) = ∫ x in a..b, (f x - C) := rfl

namespace ClassicalLean.Analysis

theorem abs_covariance_le_mul_div_four {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y : Ω → ℝ} {m M n N : ℝ}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hXb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc m M) (hYb : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc n N) :
    |cov[X, Y; μ]| ≤ (M - m) * (N - n) / 4 := by
  sorry

theorem abs_average_mul_sub_le {f g : ℝ → ℝ} {a b m M n N : ℝ} (hab : a < b)
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (hfb : ∀ x ∈ Set.Icc a b, f x ∈ Set.Icc m M) (hgb : ∀ x ∈ Set.Icc a b, g x ∈ Set.Icc n N) :
    |(b - a)⁻¹ * (∫ x in a..b, f x * g x) -
        ((b - a)⁻¹ * (∫ x in a..b, f x)) * ((b - a)⁻¹ * (∫ x in a..b, g x))| ≤
      (M - m) * (N - n) / 4 := by
  sorry

end ClassicalLean.Analysis
```

### A4: `/tmp/claude-ai-lean29/S93.lean`, item 93, statement and probes

sha256 `827d97d96fc5003939ead1f75533a9c63767265705b30d075122cd1c4e4b9301`

```lean
import ClassicalLean.Analysis.Simpson
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule

/-! Order LEAN-29, item 93: the statement with `sorry`, and the names its route cites.
`trapezoidal_integral` is not visible through the imports of `ClassicalLean.Analysis.Simpson`
(measured), so the module gains the import above; that Mathlib module is already in the
library's import closure. -/

open Finset

#check @trapezoidal_integral
#check @ClassicalLean.simpson
#check @Finset.sum_range_succ
#check @Finset.sum_range_succ'
#check @Finset.sum_range_succ_comm
#check @Finset.sum_add_distrib
#check @Finset.mul_sum

namespace ClassicalLean

theorem simpson_eq_trapezoidal (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) :
    simpson f N a b =
      (4 * trapezoidal_integral f (2 * N) a b - trapezoidal_integral f N a b) / 3 := by
  sorry

end ClassicalLean
```

### A5: `/tmp/claude-ai-lean29/S94.lean`, item 94, statements and probes

sha256 `35833582ebbbded8f1b5ea89938c5bffe52bc839c7778adaa89bb2b8dfb5589e`

```lean
import ClassicalLean.Analysis.EulerMethod

/-! Order LEAN-29, item 94: the statements with `sorry`, and the names their route cites. -/

open Filter Topology

#check @tendsto_pow_atTop_nhds_zero_iff
#check @tendsto_pow_atTop_nhds_zero_of_lt_one
#check @Filter.Tendsto.const_mul
#check @Filter.Tendsto.mul_const
#check @Filter.Tendsto.div_const
#check @abs_sub_lt_iff
#check @ClassicalLean.Analysis.eulerIterate

namespace ClassicalLean.Analysis

theorem tendsto_implicitEuler {c h : ℝ} {u : ℕ → ℝ} (hc : 0 < c) (hh : 0 < h)
    (hu : ∀ k, u (k + 1) = u k / (1 + h * c)) : Tendsto u atTop (𝓝 0) := by
  sorry

theorem tendsto_explicitEuler_iff {c h t₀ y₀ : ℝ} (hc : 0 < c) (hh : 0 < h) (hy₀ : y₀ ≠ 0) :
    Tendsto (eulerIterate (fun _ y ↦ -c * y) t₀ h y₀) atTop (𝓝 0) ↔ h * c < 2 := by
  sorry

end ClassicalLean.Analysis
```

### A6: `/tmp/claude-ai-lean29/S95.lean`, item 95, statement and probes

sha256 `f838677e7a2ddad5a8a47f354f274224f8b831f9928ec7f0197b2c8242975ad6`

```lean
import ClassicalLean.Probability.GamblersRuin
import ClassicalLean.NumberTheory.LucasSequence

/-! Order LEAN-29, item 95: the statement with `sorry`, and the names its route cites. -/

open MeasureTheory ProbabilityTheory Finset Filter Topology

#check @ClassicalLean.lucasU_of_roots
#check @ClassicalLean.lucasU_add_two
#check @ClassicalLean.lucasU_zero
#check @ClassicalLean.lucasU_one
#check @Nat.twoStepInduction
#check @ClassicalLean.Probability.GamblersRuin.measureReal_hit_eq_of_biased
#check @ClassicalLean.Probability.GamblersRuin.measureReal_hit_eq
#check @ProbabilityTheory.uniformOn
#check @MeasureTheory.Measure.infinitePi
#check @ProbabilityTheory.iIndepFun_infinitePi
#check @MeasureTheory.Filtration.natural

namespace ClassicalLean.Probability.GamblersRuin

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}
variable [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}

theorem measureReal_hit_eq_lucasU (hX : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (X n))
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (𝒢 n) μ)
    (hpm : ∀ n ω, X n ω = 1 ∨ X n ω = -1) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hp : ∀ n, μ.real {ω | X n ω = 1} = p) (a b : ℕ) :
    μ.real {ω | ∃ n, walk X n ω = a ∧ ∀ k ≤ n, -(b : ℝ) < walk X k ω} =
      lucasU (1 + (1 - p) / p) ((1 - p) / p) b /
        lucasU (1 + (1 - p) / p) ((1 - p) / p) (a + b) := by
  sorry

end ClassicalLean.Probability.GamblersRuin
```
