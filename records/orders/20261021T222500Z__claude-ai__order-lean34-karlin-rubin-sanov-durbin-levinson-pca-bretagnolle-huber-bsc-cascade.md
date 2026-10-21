# LEAN-34 order: batch 4 of the API-credit drafts (items 118, 122, 140, 142, 144), the witness of VACUITY-3 row 70, and bridge row 163

For a plain Claude Code session on DSMain, as dustin, in tmux `cc`. Written by claude-ai on
2026-10-20 under lean/CLOUD-LANDING-PLAN-2.md ruling 2 (batches 3 to 7 land on DSMain as LEAN-33 to
LEAN-37; this is batch 4 plus row 70), after Dustin asked on 2026-10-20 at 21:26 EDT whether it was safe to write
it while LEAN-33 runs. claude-ai wrote it then with no Lean run on DSMain (LEAN-33 has the
machine's Lean runs); every number that needs Lean, and every fact about the master it starts from,
was measured at the cut, after LEAN-33 and MERGE-3 had landed (section "Measured at the cut"). At the cut (2026-10-21) it gained a last job, at Dustin's
question of 2026-10-21 15:53 EDT: bridge row 163 of the bridges file (binary symmetric channels in
series, found by MERGE-3's bridge search), proved in `ClassicalLean/InformationTheory/ChannelCapacity.lean`
in its own commit (claude-ai's ruling, store row 20261021-015; without it the row would have waited
for LEAN-38 with bridges 160 to 162, by analogy with lean/CLOUD-LANDING-PLAN-2.md ruling 5, which names
those three, and store row 20261021-001, which gives LEAN-38 MERGE-3's unread pairs). Dustin may veto:
his veto drops every part of this order marked "row 163", and every count that includes row 163 drops
its share: import lines three to two, witnesses nine to six (new ones eight to five), cold reviews six
to five (no (f)), module files six to five, the records file names without `-bsc-cascade`, and 5g's
predictions without ChannelCapacity; the row then stays with LEAN-38.
Lane files named `lean/...` are under /opt/datasphere/lane/inbox/threads/staging/lean/ (ds_* tools:
root `lane`, path `inbox/threads/staging/lean/...`). This order is `lean/LEAN-34/order.md`; its
inputs are `lean/LEAN-34/data/` and LEAN-33's two type-dump scripts in `lean/LEAN-33/scripts/`.

**New lane files go through `ds_file`** (project `lean`, job `LEAN-34`): your plan is kind `plan`
(it lands as `lean/LEAN-34/plan.md`; a second becomes `plan-r2.md`, never overwriting), the report
kind `report`, the push-review file subdir `data`, name `LEAN-34-push-review.txt`. Compare each
reply's `post_sha256` with your own. Appending to the bridges file (job 5b) is `ds_write_staging`
in append mode with `expect_sha256`. **Track the order's steps with the task tools** (lane
`lean/NOTE-20261015-task-list-rule.md`).

Review: three passes on 2026-10-20 by one fresh subagent that had not seen the order being written (read-only; a read list in /tmp/claude-ai-l34/review/ on helios and the body in claude-ai's workspace). Pass 1: PASS WITH FINDINGS, 0 BLOCKER, 4 MAJOR, 15 MINOR, all applied (r1). Pass 2: 15 fixed, 3 in part, 1 moot, and 1 new MAJOR and 8 new MINOR, all applied (r2). A confirming pass on those: all 9 fixed, 2 new MINOR, applied (r3); r3 itself was not reviewed again. The cut (section "Measured at the cut", filled by script after LEAN-33 and MERGE-3 landed, and row 163's job) was reviewed on 2026-10-21: pass 1 by a fresh subagent, PASS WITH FINDINGS, 0 BLOCKER, 1 MAJOR, 12 MINOR, all applied (r5); a confirming pass by another fresh subagent, every finding fixed and 6 new MINOR, applied (r6); r6 itself was not reviewed again. Not reviewed: any Lean (the hints, w70's elaboration and instance search, 122's `omit` list are measured at the cut); MERGE-2's order, `records/README.md` and the helpers' code.

## What is already true

### Measured by claude-ai on 2026-10-20 from 21:29 to 21:45 EDT, at `04e4a38`, reading files only

On DSMain over ssh from helios, in claude-ai's own clone `~/api-credit/cl-04e4a38` of master
`04e4a3842055026616256cf549ded9bf4bcfdd96` (MERGE-2's last commit); no Lean process was started.
Outputs in `/tmp/claude-ai-l34/` on DSMain and helios, gathered in `lean/LEAN-34/data/facts.txt`
(sha256 `0f4482006a8d8943ee81e51653b84564dd9d94e3960470073a9ff379c79444f6`).

- **The six drafts** (in `/data/api-credit/20261019/carry/`, read-only, whose `SHA256SUMS` is
  a2f5e552; the same bytes in `~/api-credit/drafts/`, `cmp`). Each imports only library modules
  (and d140 two Mathlib tactic files); each declares at the root namespace, d142 one helper in its
  own `namespace PrincipalComponentsAux`. None holds `sorry`, `admit`, `native_decide`,
  `implemented_by`, `axiom` or `set_option` (grep). All six last passed the API-credit pipeline's
  scorer at `a6d5c0f` (lean/API-CREDIT-CARRY-1.md, "Recheck at master a6d5c0f", 53 of 53); claude-ai's
  recheck at `04e4a38` covered only LEAN-33's and CLOUD-MATH-3's drafts, so these six are compiled
  again at the cut.

  | item | draft | sha256 | home module | its declarations | last review (lean/API-CREDIT-CARRY-1.md, work/api-credit/API-CREDIT-1/API-CREDIT-1.md) |
  |---|---|---|---|---|---|
  | 118 | d118-r1-s1 | `ac3f6ecea232b26d335083d171e6e21f0a678d28d8092e8ac3970ede49cd3094` | Statistics.NeymanPearson | the def `HasMonotoneLikelihoodRatio'`, the private `isLRTest_thresholdTest'` and `thresholdTest_mul_eq_zero'`, the theorem `isUniformlyMostPowerful_of_monotoneLikelihoodRatio'` | round 1's cold review: carry s1 |
  | 122 | d122-r5-s1 | `9bb9a6c6a466f65a05d824820e5a6f23854871faf2881819359fac9b64cfe8c6` | InformationTheory.MethodOfTypes | the private defs `cnt` and `consEquiv'`, seven private theorems (`typeCount_cons`, `prod_eq_prod_pow_typeCount_nat`, `prod_le_prod_nat`, `pow_mul_factorial_le`, `cnt_mul_prod_factorial`, `cnt_mul_le`, `pow_le_card_types`), the theorem `le_measureReal_empirical_eq`; a `variable {α : Type*} [Fintype α] [DecidableEq α]` line (line 7) | review r3: GENERALIZED, "needs only p >= 0, not a probability vector"; carry |
  | 140 | d140-r1-s2 | `225f46a8ad450ccb837f4b0b5066ecb00ea402aef26e385c6ed05ea004d4cd67` | Probability.YuleWalker | the private `pos_of_pred`, the theorem `durbinLevinson_spec`; `import Mathlib.Tactic.LinearCombination` and `import Mathlib.Tactic.Ring` | review r6: FAITHFUL; carry s2 |
  | 142 | d142-r1-s2 | `4a6b213eadc22c33d0cbed11262254e590fac516d047b22f314902fe2c500b4c` | Probability.CovarianceDirections | `PrincipalComponentsAux.isSymmetric_covLin` (public), the theorem `sum_variance_mix_le_sum_eigenvalues`; `import ClassicalLean.Algebra.MinMax` | review r6: GENERALIZED; carry s2 (its MAJOR against s1: "its public statement goes through a private lemma") |
  | 144 | d144-r1-s1 | `6bff0907f164fe49de3eb1b0eac206c41901ee12f676e137f6db849ca7358655` | Statistics.NeymanPearson | the theorem `size_add_one_sub_power_ge`; `import ClassicalLean.InformationTheory.Entropy` | review r6: FAITHFUL; carry s1 |
  | row 70 | d2006-r2-s1 | `a56cce37e98713396361efbf2a96316d55dbf9df059e8a8b05b4fcc1e54c5926` | Analysis.FiniteGame | two examples: a witness with `P := Kernel.id` and an `example : minimaxRisk … Kernel.id = 0` | carry, "model, one repair round"; **not used** (Goal list, row 70) |

  Their plan rows (MATH-PLAN-library-2.md section 7, lines 427, 431, 449, 451 and 453): 118
  Karlin–Rubin in the textbook form, the monotone likelihood ratio allowed to be `+∞` where
  `f θ = 0`, "which takes in uniform laws on `[0, θ]`"; 122 the lower half of Sanov's theorem, a
  type `q` has chance at least `(n + 1)^(−K) exp(−n D(q ‖ p))`; 140 the Durbin–Levinson recursion
  solves the order-`k` prediction equations from the order-`(k − 1)` solution, with error variance
  `v_k = v_{k−1}(1 − φ_kk²) > 0`; 142 (bridge, imports Algebra.MinMax, rests on item 83) for
  orthonormal weight vectors `w₁, …, w_k` the variances of the mixes add up to at most the sum of the
  `k` largest eigenvalues of the covariance matrix, with equality at its eigenvectors; 144 (bridge,
  imports InformationTheory.Entropy) the Bretagnolle–Huber bound, on a finite set every test has size
  plus missed-detection chance at least `exp(−D(p₁ ‖ p₀))/2`.
- **The reviews' minor findings for these drafts** (API-CREDIT-1.md lines 59, 92 and 148), and what
  this order does with each: every draft at the root namespace goes into its module's namespace
  (taken); 122 "drop the draft's `variable` line if MethodOfTypes already declares it" (taken: it
  does, line 108); 142 s2 "move `w` inside the first conjunct" (not taken: `w` and `hw` are bound
  for both clauses but used only by the first, and the drafted statement instantiated at `w :=` the
  first `k` eigenvectors, an orthonormal family, yields the equality clause, so the moved form is
  equivalent; reviews passes 1 and 2 of this order); 140 "`hpos` as `Matrix.PosDef`" (not taken: it restates a hypothesis and needs a new
  bridging proof, which plan 1 leaves out; the docstring says the hypothesis is the positive
  definiteness of the Toeplitz matrix, written out); 144: the review's minor to drop
  `[MeasurableSpace ι]` was not taken by the pipeline (line 148, "One minor not taken"), because the
  library's `IsTest` includes `Measurable φ`, and it stays; 118's optional strengthening,
  "existence of c and gamma for a given alpha" (not taken: the module already proves
  `exists_thresholdTest_size_eq`, line 437).
- **Names.** No name the drafts declare, `PrincipalComponentsAux` included, occurs anywhere under
  `ClassicalLean/` (`grep -w`, gather2.out); the unprimed `HasMonotoneLikelihoodRatio` (NeymanPearson
  line 366) and the private `isLikelihoodRatioTest_thresholdTest` (line 381) exist and stay. The
  library names the drafts use exist where expected: `IsTest` (NeymanPearson line 105),
  `IsLikelihoodRatioTest` (111), `thresholdTest` (157), `isTest_thresholdTest` (160),
  `power_le_of_likelihoodRatioTest` (126), `IsUniformlyMostPowerful` (372); `typeCount` (MethodOfTypes
  111), `empirical` (115), `typeCount_le` (118), `sum_typeCount` (121), `prod_eq_prod_pow_typeCount`
  (127), `draws` (145), `measureReal_draws` (159); `covOp` (CovarianceDirections 239), `covLin` (244),
  `isSelfAdjoint_covOp` (248), `reApplyInnerSelf_covOp` (251), `mix` (143); MinMax's
  `sum_re_inner_le_sum_eigenvalues` (379) and `sum_re_inner_eigenvectorBasis` (402); Entropy's
  `relEntropy` (74) and `mul_log_le_relEntropy` (146).
- **Imports, by a text parse of every `import` line** (gather2.out; a parse, not Lean; the cut
  confirms with Lean): NeymanPearson imports only Mathlib, and InformationTheory.Entropy's import
  closure does not hold NeymanPearson; Algebra.MinMax imports only
  `Mathlib.Analysis.InnerProductSpace.Spectrum`, and its closure does not hold CovarianceDirections;
  so neither new import line makes a cycle. `Mathlib.Tactic.LinearCombination` and
  `Mathlib.Tactic.Ring` are already in YuleWalker's closure, so d140's two import lines are not
  added. Importers: of the five home modules only CovarianceDirections has one,
  Statistics.ResidualVariance (direct; nothing imports ResidualVariance), besides the root file.
- **The five home modules at `04e4a38`** (sha256; namespace; where its block ends; what follows):
  - `ClassicalLean/Statistics/NeymanPearson.lean` `eeefe79a881ce840f436d75e7ef3e5f20172c7dfa03741673d7eb4a78905e221`, 484 lines; `namespace ClassicalLean.Statistics` (line 98) to its `end` at line 447; `variable {Ω : Type*} [MeasurableSpace Ω]` (line 100); `open MeasureTheory ProbabilityTheory Set Filter Topology` and `open scoped ENNReal NNReal` (lines 95 and 96); two witnesses after the block (lines 449 to 484), the second of the unprimed Karlin–Rubin theorem on two points.
  - `ClassicalLean/InformationTheory/MethodOfTypes.lean` `3fa1e428e3825fad39f004f97e29e12de4791b57a5e1aea5854557e09fb2d627`, 362 lines; `namespace ClassicalLean.InformationTheory` (line 106) to line 320; `variable {α : Type*} [Fintype α] [DecidableEq α]` (line 108, the same as d122's line 7) and, after `sum_empirical` (lines 137 to 139), `variable [MeasurableSpace α] [MeasurableSingletonClass α]` (line 141) for the rest of the block; `open MeasureTheory Real Finset` and `open ClassicalLean.Simplex ClassicalLean.Probability.RelativeEntropyGrowth` (lines 103 and 104, d122's first two `open` lines); the upper half `measureReal_empirical_eq_le` at line 168; two witnesses after the block (lines 322 to 362).
  - `ClassicalLean/Probability/YuleWalker.lean` `c127a9a8d14407faff9c6207e815605572ebd526ffcefcf06949a44e0ed8b7c2`, 150 lines; `namespace ClassicalLean.Probability` (line 74) to its `end` at line 150, the last line; `variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]` (line 76); `open MeasureTheory ProbabilityTheory` (line 72), no `open Finset`; no example (its theorems `covariance_eq_sum` and `isSolution_autocovariance` are VACUITY-3 rows 31 and 32, not witnessed, LEAN-36's).
  - `ClassicalLean/Probability/CovarianceDirections.lean` `bd548eace7e6bdef501ebf39615fb290ceb28afd00c589f7ddc1a9b4c354f8db`, 601 lines; `namespace ClassicalLean.Probability.CovarianceDirections` (line 134) to line 548; `variable {ι Ω : Type*} [Fintype ι] {m0 : MeasurableSpace Ω} {μ : Measure Ω}` (line 136) and `variable {X : ι → Ω → ℝ}` (line 145); `section Directions` (line 234) with `variable [DecidableEq ι]` (line 236) to `end Directions` (line 336), holding `covOp`, `covLin` and the directions of largest and least variance; three witnesses after the block (lines 550 to 601), the last on three points with `X` the indicators of the points `0` and `1`.
  - `ClassicalLean/Analysis/FiniteGame.lean` `0df148d618f1a63f4ca2a94fd5f0dda3a1e962c2cbe19b45838ea292f27f37e4`, 996 lines; `namespace ClassicalLean.Analysis` (line 134) to line 968; three examples after it: row 70's witness of `iSup_bayesRisk_eq_minimaxRisk_of_finite` at lines 970 to 979 (its `open MeasureTheory ProbabilityTheory in` line, a docstring at lines 971 to 975, the example at 976 to 979; line 980 is blank), then item 66's (981 to 986) and item 103's (988 to 996).
- **VACUITY-3 row 70** (lean/VACUITY-3-report.md finding 2 and line 196; lean/VACUITY-3-ruling-3.md
  ruling 1). Its witness at lines 970 to 979 uses `Kernel.const (Fin 2) (Measure.dirac 0)`, which
  "tells nothing", and its docstring says "the game's value is `1/2` … worked by hand, not checked in
  Lean". Ruling 1 sent it to the next gate order: "a kernel that depends on the parameter, and the
  parenthesis … either checked by an `example` or removed". Its first kernel, the noiseless
  `Kernel.deterministic (fun θ ↦ θ)`, was moved away from because the game's value there is `0` on
  both sides (review r-g10, finding 1, MINOR: "the theorem's conclusion at this witness is
  `0 = 0`", `~/lean/vacuity3-checks/reviews/g10/review.md` lines 19 to 26). d2006-r2-s1 goes back to
  that kernel (`Kernel.id`) and checks the value `0` with an `example`. claude-ai's block
  `lean/LEAN-34/data/w70.lean` (sha256 `30f683a1bd0fb72b6d2ec4a3305e638cb33133ec22361eadfaa9c07fa7743a97`) takes instead VACUITY-3's fresh reviewer's first
  fix, `P := Kernel.const (Fin 2) (Measure.dirac 0) + Kernel.id` (`P 0 = 2 · dirac 0`,
  `P 1 = dirac 0 + dirac 1`): it depends on the parameter, and it is finite but not Markov, which
  uses the theorem's "finite kernel" generality. Its docstring states no value (claude-ai's grid
  check gives `2/3`, in `hints.out`; not checked in Lean, so not in the library). Mathlib's instances it
  rests on (the pinned Mathlib's `Kernel/Defs.lean` lines 190 to 240 and `Kernel/Basic.lean` lines
  105 to 120 and 190 to 205, in facts.txt): `IsFiniteKernel.add` (`Mathlib/Probability/Kernel/Defs.lean:201`),
  the constant kernel's (`Mathlib/Probability/Kernel/Basic.lean:197`), `Kernel.id`'s Markov
  instance (`Mathlib/Probability/Kernel/Basic.lean:113`) and Markov kernels as finite
  (`Mathlib/Probability/Kernel/Defs.lean:218` and `:231`). Its elaboration is at the cut.
- **Witness hints, worked by claude-ai in exact arithmetic** (`lean/LEAN-34/data/hints.py` and its
  output `lean/LEAN-34/data/hints.out`; not elaborated in Lean; check them):
  - 118: `Θ := Fin 2`, `Ω := Fin 2`, `ν := Measure.count`, `f 0 = (1, 0)` and `f 1 = (1/2, 1/2)`,
    `S ω = ω`:
    the ratio `f 1 / f 0` is `1/2` at `ω = 0` and `+∞` at `ω = 1` (the textbook case the unprimed
    theorem cannot take), `g t = 1/2` for `t ≤ 0` and `∞` otherwise, monotone; `θ₀ = 0`, `c = 0`,
    `γ = 1/2`: the threshold test is `(1/2, 1)`, size `1/2 > 0`, power `3/4` (a grid of all tests of
    size at most `1/2` reaches no more).
  - 122: `α = Fin 3`, `p = (1/3, 2/3, 0)`, `n = 2`, `ω₀ = (0, 1)`, so `q = (1/2, 1/2, 0)`, and `hpq`
    is met at the point `2` where both are `0`, not only because `p` has no zero (the theorem allows
    `p` not summing to `1`, review r3's GENERALIZED; `p = (1/2, 1, 0)` also works).
  - 140: `n = 2`, `γ 0 = 1` and `γ z = 1/2` for every `z ≠ 0` (not `0` past some lag, which
    VACUITY-3's ruling 3 rules out; `hγ` holds because `γ` depends only on whether `z = 0`): the
    quadratic form is `½ ∑ xᵢ² + ½ (∑ xᵢ)²`, positive for `x ≠ 0` (the `4 × 4` matrix's leading
    minors are `1`, `3/4`, `1/2`, `5/16`); `a = fun _ ↦ 1/3` solves both order-2 equations, `v₂ = 2/3`;
    then `φ = 1/4`, `b = fun _ ↦ 1/4` meets `hb` and `hbn` and solves all three order-3 equations,
    `v₃ = 5/8 = v₂ (1 − φ²)` (reviews passes 1 and 2; with `n = 1`, `a` has one entry). An AR(1)
    covariance such as `γ z = 2^(−|z|)` gives `φ = 0`, the factor `1 − φ² = 1`: avoid it.
  - 142: `ι := Fin 3`, `Ω := Fin 4`, `μ := uniformOn Set.univ`, `X i` the indicator of the point `i`
    (`X := fun i ω ↦ if ω = Fin.castSucc i then 1 else 0`):
    covariance `3/16` on the diagonal and `−1/16` off it, eigenvalues `1/4`, `1/4` and `1/16`;
    `k = 2` (`hk : 2 ≤ 3`), so the family has size 2 and the bound, `1/2`, is not the trace;
    `w := ![EuclideanSpace.single 0 1, EuclideanSpace.single 1 1]`, orthonormal, whose mixes'
    variances add to `3/8 < 1/2` (review pass 2; with `card ι = 2` the only `k ≥ 2` is the trace,
    and `k = 1` is a family of size 1).
  - 144: `ι = Fin 3`, `p₀ = (1/2, 1/2, 0)`, `p₁ = (1/4, 3/4, 0)`, so `hsupp` acts at the point `2`;
    the test `φ = (0, 1, 0)`: the bound `exp(−D)/2 ≈ 0.439` against size plus missed detection
    `3/4`.
- **Rows 7, 8, 9, 10 and 67** are LEAN-33's. With row 70's new block, no witness uses the older rows'
  forbidden-word exception of HANDOFF section 4 (LEAN-33 measured rows 7 and 8; w70 holds none of the
  six words, grep).
- **The type dump (rule 14):** LEAN-33's lane copies of rule 14's pair, `lean/LEAN-33/scripts/TypeDumpPI.lean`
  (`1fcb69f41ddbd35f84862521d2ead5946a0bd52caf5f60b6d10e966cfd9776ff`) and
  `lean/LEAN-33/scripts/g8-typediff.py` (`371eda9a2e5065abaa8f36bac9872d0f15e7bade72a248d5f0f88f20b4eacb71`;
  copy it back as `g8_typediff.py`).
- **Timers on DSMain** (read on 2026-10-20 for LEAN-33 with `systemctl --user list-timers` and
  `crontab -l`): memory-index at midnight; restic, ds-hygiene, the daily verify, lean-nightly and the
  backup bundle between 2 and 4 in the morning; the store sync before 6; w29-tracker and w29-sysmap
  every few minutes (they load no Lean).

### Measured at the cut (claude-ai, on 2026-10-21 from 15:59:13 to 16:48:32 EDT, at `02ac649`)

In claude-ai's own clone `~/api-credit/cl-02ac649` of the master this order starts from, its own
build; outputs in `/tmp/claude-ai-l34/cut/` on DSMain, gathered in `lean/LEAN-34/data/cut-facts.txt`
(sha256 `0d7ef8d48aac219d34436942b0c9ee5c6486cf45344078531c133a4ee545baa9`; the Lean runs on 2026-10-21 from 15:59:13 to
16:08:38 EDT, the file facts that day at 16:04:05 EDT) and `lean/LEAN-34/data/cut-facts-2.txt` (sha256
`7b04c054b89b39bb6983160225cb352296f7ae220782d10fa3ac8ce589b3a608`, written on 2026-10-21 at 16:48:32 EDT:
MERGE-3's gate 7 time and report-tool output, MERGE-3's push-note anchors, the CI run, row 163's import
line alone, run on 2026-10-21 from 16:17:31 to 16:18:49 EDT, its prediction written first, and row 163's
two modules and Mathlib names, read by `grep`). No order's session ran on DSMain
then; `pgrep -ax lean` was empty before each Lean run.

- **Master.** Both remotes (`/data/git/classical-lean.git` and GitHub) at `02ac649b17f66e39327022462ee4d3d9a73b62d4`, MERGE-3's
  last commit, pushed by Dustin (DSMain's bare master ref written 2026-10-21 15:42:20 EDT; store row
  20261021-012); its GitHub CI run 39663962493 (workflow CI, job build) ended `success` at
  2026-10-21T20:01:37Z. At it: `lake build` 4193 jobs, 0 warnings; AxiomGate PASS 3527;
  VacuityGate PASS with 1 reviewed helper and 0 VACUOUS-PENDING; check_sorry PASS 140; check_records PASS
  140 (104 records files, 1 named exemption, `Simplex/Hessian.lean`); `compile_rules.py drift` PASS; rule 27's
  module count (`env.header.moduleNames.size` of a scratch file importing `ClassicalLean`)
  5729 (it counts Mathlib's modules too; claude-ai's hand guess near the job count missed, store
  row 20261021-014).
- **Records at it:** the last round is 70 (MERGE-3,
  `records/rounds/20261021T152700Z__round-70-merge-cloud-math-3.md`), so this order's is 71.
  MERGE-3's push, for your records commit (records/README.md rule 2), is the text
  ``; pushed by Dustin: DSMain's master ref written 2026-10-21 15:42:20 EDT, GitHub master equal (`02ac649`)``
  (from its `;` to its `)`) inserted at one anchor in each of two rows, both their files' last lines at `02ac649`
  (cut-facts-2.txt): in `records/orders/INDEX.md` (71 lines) MERGE-3's row, right after
  ``one bridge found (row 163, lane `MATH-PLAN-library-2-bridges-2.md`)`` (once in the file; followed there by the text the
  block below asserts); in `records/CLAIMS.md` (63 lines) MERGE-3's row, right after
  `after claude-ai's push review` (twice in the file, once in its last line; followed there by a
  space and `|`, the row's end). Do it by a script that finds each row as its file's last line and checks its start
  (INDEX: `| MERGE-3 |`; CLAIMS: `| 2026-10-21` and, since LEAN-33's CLAIMS row starts the same way,
  that the line contains ``executing order `MERGE-3` ``), refuses unless the anchor occurs once in
  that line, inserts before anything is appended, and asserts, before inserting, exactly this (a
  fenced block, so spaces count; `A1` is the INDEX anchor and `A2` the CLAIMS anchor above, `i` where
  each starts in its line, `line` the file's last line without its newline):

  ```
  INDEX:  after = line[i + len(A1):]; assert after.startswith(" | `6e79630` (records), ")
  CLAIMS: after = line[i + len(A2):]; assert after == " |"
  ```

  The latest bridge baseline is `records/bridges/MERGE-3/` (`COMMIT` names
  `ed177e9d8bb17c1221a9a713168ccd57f3ee5547`, MERGE-3's G; `pairs.tsv` 3031 lines, `shapes.tsv` 760);
  `tools/vacuity_reviewed.txt` holds 1 entry; ROADMAP.md's last section is 1.27 (line
  812), so yours is 1.28; HANDOFF.md section 4's "Satisfiability witnesses" paragraph as MERGE-3 left it
  (unchanged since LEAN-33: lines 932 to 980, 49 lines, the text's sha256 beginning `ecb72ac5546a1944`;
  its last dated line is LEAN-33's, line 973, which after two spaces of indentation starts
  `**Dated 2026-10-21 UTC (order LEAN-33):**`).
- **The worktree** `~/lean/classical-lean-paper-crypto` is on branch `merge-3` at `02ac649`,
  clean. Remotes: `origin` the bare repo, `github` GitHub.
- **The five home modules at `02ac649`:** all five byte for byte as at `04e4a38`, each sha256 equal
  (as predicted: LEAN-33 and CLOUD-MATH-3 change none of them); their importers as at `04e4a38`: only
  CovarianceDirections has one besides the root file, Statistics.ResidualVariance.
- **The drafts at `02ac649`:** the API-credit pipeline's scorer (each draft with `#print axioms` lines
  appended, `-DmaxHeartbeats=400000`) rc 0 for all six, every named theorem depending only on `propext`,
  `Classical.choice` and `Quot.sound`; with rule 20's four flags, rc 0 and these warnings: d118 two
  `if_neg` deprecations (line 75); d122 15 warning lines: five unused-section-variable and
  unused-instance lines of `typeCount_cons` and `prod_le_prod_nat`, eight `if_pos` and `if_neg`
  deprecations and two `show` linter lines (lines 107 and 205; cut-facts.txt lists the first 12 of
  the 15, the whole is `/tmp/claude-ai-l34/cut/out/f4-d122-r5-s1.out` on DSMain); d140 two unused `simp` arguments (lines 19 and 22) and one
  `show` line (99); d142 "this tactic is never executed" and the unused-tactic linter at line 16, the
  second branch of its `first`; d144 one `push_neg` deprecation (line 80); d2006 one unused `simp`
  argument. No error anywhere. claude-ai's predictions of these warnings missed (store row
  20261021-014; the cut text's own d122 count slip, 20261021-016). 122's helpers placed as the Goal list says, in a
  copy of MethodOfTypes, with the four flags: two helpers warn for unused section
  variables or instances (the copy's other ten warnings are the draft's own deprecation and `show`
  lines): `typeCount_cons` needs `omit [Fintype α] in`, and `prod_le_prod_nat` needs `omit [Fintype α] [DecidableEq α] in` with `classical` as its proof's first tactic (there the section-variable linter lists only `[Fintype α]`, so its proof uses `[DecidableEq α]`, which another linter flags as unused in its type). Names: a Lean `env.contains` check of every name the
  drafts declare, under its home namespace and at the root, with row 163's three: 46 checked, 0 exist.
- **Lean checks of the Goal list:** 140's draft with its two Mathlib import lines removed, importing
  only YuleWalker: rc 0 with the draft's three warnings and no new one. 142's `first | … | …`: each
  branch alone (d142_b1, d142_b2) rc 0 with no warning, and the draft's linter says the second never
  executes, so the first is kept. The two import
  lines alone, added in claude-ai's clone and then restored: build rc 0, 4193 jobs, 4 modules rebuilt
  (NeymanPearson, CovarianceDirections, ResidualVariance and the root `ClassicalLean`), the type dump
  against the base's `DIFF removed=0 added=0 changed=0 proof_only=0`, as predicted; after the restore
  porcelain 0 and the build rc 0. Row 70: a copy of FiniteGame
  with lines 970 to 979 replaced by w70's block, elaborated with the four flags: rc 0, no warning.
- **The type dump at `02ac649`:** 4009 records (3527 thm, 482 def), none dropped; `check`: elided 0, missing_fields 0; the dump against
  itself all zeros.
- **Helpers:** LEAN-33's, in `~/lean/lean33-checks/scripts/` and `~/lean/lean33-checks/census/`, with
  each file's sha256, the path lines Setup 1 changes and their counts: 29 files (27 scripts and the
  two census tails `census-all-tail-lean28.lean` and `census-tail-lean28.lean`), their full sha256s in
  cut-facts.txt (section "helpers (LEAN-33's)"); lines naming `lean33-checks`: `commit.sh` 1,
  `docs-insert.py` 1, `el.sh` 1, `evcite.py` 2, `ev.sh` 1, `hl.sh` 1, `mkcensus.sh` 1, `probecheck.py` 1
  (its line 27, `D = '/home/dustin/lean/lean33-checks'`), `records2.py` 1, `rootrun.sh` 1, the other 19
  none; one `BASE = ` line, `probecheck.py`'s line 29, `BASE = '04e4a38'`; `allowlist.txt` sha256
  `ccccc3c50700c03e167489d03cd7e05682f69de0b2e03fd67aee3445a76a21f3`; no `seed.txt`.
- **MERGE-3's runs, the pattern for your gates:** the vacuity tests 89 verdicts, 47 flagged, 3 UNCHECKED,
  0 mismatches, rc 0 (as MERGE-3 predicted them); gate 7 ALL PASSED for `ed177e9` in 23:01.63 wall
  clock, 1381.63 seconds (`g7.out` line 40); the report tool's output `~/lean/merge3-checks/report.out`
  (sha256 `f6c3973876478bf02361b806829e332fc477ba41ee5103d3e1f1c74d29f12b70`, 1244 lines): 1961
  written theorems; A, with a hypothesis, 1164 (CLOSES 0, OPEN 1120, DEPENDENT 44); B, with none, 797
  (CLOSES `simp` 15 and `positivity` 1, OPEN 781); C, Prop-valued definitions, 36 (0 recursive);
  self-test mismatches 0 (cut-facts-2.txt).
- **The bridges file** `lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md` is `494bf24dd51961c835bb4df8d4f7c8fa2c61ea58ece0b66ae7d5bc434bb0523f`;
  its last row is 163 (MERGE-3's, the row of this order's last job), so new rows start at 164.
- **LEAN-33's report** (`lean/LEAN-33/report.md`, `11c7482a69fea652d39ad0cb91c5a3cd0fe3b71c3f853649a6c94446f2187b5b`): what this order takes from it:
  `pgrep -ax lean`, not `pgrep -a lean` (which matched a Samba process, one of LEAN-33's misses);
  scripts run from files, never `python3 -I -` (it had three empty stdin runs); no clock time in a
  prediction's header that was not read from a clock (two were wrong); its quote checker for rule 22;
  its `allowlist.txt` as it is (two option tokens were added there after ten refused runs). And from MERGE-3's run: a lane append in pieces cuts no piece after a blank
  line, and each reply's `post_sha256` is compared with your own prefix's hash before the next piece.
- **Row 163** (the bridges file's row 163, found by MERGE-3's search; it would have waited for
  LEAN-38 with bridges 160 to 162, by analogy with plan 2's ruling 5 and store row 20261021-001). Its home `ClassicalLean/InformationTheory/ChannelCapacity.lean` (item 130, landed by
  CLOUD-MATH-3 and merged by MERGE-3) at `02ac649`: sha256
  `71e589a534c1a47460c012e3a4c8b59e8826468faa1451a2c31e975e32963d72`, 174 lines; imports
  `ClassicalLean.InformationTheory.MutualInformation` and `Mathlib.Analysis.SpecialFunctions.BinaryEntropy`
  (lines 7 and 8); top-level `open ClassicalLean.Simplex` (line 45); `namespace
  ClassicalLean.InformationTheory.ChannelCapacity` (line 47) to its `end` at line 162, holding the
  private def `bscJoint` (line 50), five private theorems (lines 53 to 124), `mutualInfo_bsc_le` (line
  130) and `mutualInfo_bsc_half` (line 152); two witnesses after it (lines 164 to 174); its only
  importer is the root file. `ClassicalLean/Probability/TwoStateChain.lean` (sha256
  `9b64e894166d042e98991bcc86cb8b1f347ccdd1f24829fdd2f2ce452a4c038c`, 127 lines) imports only
  Mathlib (lines 7 to 9), so the import line `import ClassicalLean.Probability.TwoStateChain` in
  ChannelCapacity makes no cycle, and both modules are already in the root's closure; its
  `twoStateMatrix` (line 39), `twoStateMatrix_mem_rowStochastic` (line 42), `vecMul_pow_apply_one`
  (line 80) and `tendsto_vecMul_pow_apply_one` (line 103) are the row's tools. `vecMul_pow_apply_one`
  gives only the column-1 entry of a row of the `n`-th power; the column-0 entry follows from the
  rows' sums (Mathlib's `Matrix.rowStochastic`, `Mathlib/LinearAlgebra/Matrix/Stochastic.lean` line 46,
  and `mem_rowStochastic`, line 55: probe whether `pow_mem` gives `M ^ n` in it). For the limit:
  Mathlib's `Real.binEntropy_two_inv` and `Real.binEntropy_continuous`
  (`Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean` lines 69 and 167) and
  `tendsto_pow_atTop_nhds_zero_of_abs_lt_one` (`Mathlib/Analysis/SpecificLimits/Normed.lean` line 229),
  the direct route; Mathlib's `sum_row_of_mem_rowStochastic` may give a row's sum directly (probe
  it). These module facts and names: cut-facts-2.txt (its grep of each Mathlib file prints no file
  name; the paths are the grep's arguments). claude-ai's statements, `lean/LEAN-34/data/r163.lean` (sha256
  `ed34dcf920ccbddae6cab0d5e236ff072fb69f7296045fd07ca1e56ad0f8883e`): `mutualInfo_bsc_pow_le`,
  `mutualInfo_bsc_pow_half` and `tendsto_capacity_bsc_pow`, as the row states them, inside
  ChannelCapacity's namespace with `sorry` proofs, then three trial witnesses at `ε = 1/4`, `n = 3` and
  `p = ![1/3, 2/3]` (not yet in rule 2's form): with the four flags rc 0, exactly the three `sorry`
  warnings, no error (`c-r163`). The import line alone, added in claude-ai's clone and then restored:
  build rc 0, 4193 jobs, 2 modules rebuilt (ChannelCapacity and the root `ClassicalLean`), the type dump
  against the base's `DIFF removed=0 added=0 changed=0 proof_only=0`, as predicted; after the restore
  porcelain 0 and the build rc 0, 4193 jobs (cut-facts-2.txt).

## Goal

The five items proved in their home modules, each inside its module's namespace, with witnesses,
reviews and records; VACUITY-3 row 70 re-witnessed with a kernel that depends on the parameter; bridge row
163's three theorems proved in ChannelCapacity, the last job; no existing declaration changed (the type dump shows it); every gate passing, gate 7 included; the
bridge search and the report tool run; HANDOFF.md and ROADMAP.md saying what changed. Dustin pushes
after claude-ai checks the push-review file.

The changes asked of each draft (from the measurements above):
- **Every item:** its declarations go inside its home module's namespace block, before that block's
  `end` (122's helpers excepted, below), reusing the module's own `variable` line where it is the
  draft's (MethodOfTypes' line 108 is d122's line 7: drop the draft's copy); a draft that binds its
  types in its own signature (118, 140, 142, 144) keeps them; the draft's `open` lines the module
  lacks become `open … in` on the declarations that need them; references the namespace makes
  ambiguous or wrong are written in full (job 1's type comparison decides); each main theorem's
  docstring names its item ("Item 118 of MATH-PLAN-library-2") and its draft; the module docstring
  lists the new result; a step whose effect is not determined is cut to what fires; a private
  helper whose statement Mathlib or the module already proves is replaced by that name (the module
  review asks it of each helper); every warning the four flags or `lake build` report is fixed in
  the proof only, except a warning that a section variable is unused, or that a section variable's instance is
  unused in the type (Mathlib's `linter.unusedDecidableInType` and `linter.unusedFintypeInType`), which
  is fixed by `omit … in`
  before the declaration's docstring (the same warning on a declaration's own binder is reported and
  its statement kept, rule 1; MethodOfTypes uses `omit` at lines 117 and 133; the cut lists which
  of 122's helpers need it, `typeCount_cons` needs `omit [Fintype α] in`, and `prod_le_prod_nat` needs `omit [Fintype α] [DecidableEq α] in` with `classical` as its proof's first tactic (there the section-variable linter lists only `[Fintype α]`, so its proof uses `[DecidableEq α]`, which another linter flags as unused in its type)); each fix listed in round 71.
- **118:** the def, the two private helpers and the theorem after the proof of the module's unprimed
  Karlin–Rubin theorem (it starts at line 407) and before `end` (line 447); the def's docstring says it is the textbook form of the
  module's `HasMonotoneLikelihoodRatio`.
- **122:** the two private defs and seven private theorems between `sum_empirical` (line 139) and the
  `variable [MeasurableSpace α] [MeasurableSingletonClass α]` line (line 141), so that line does not
  reach them (it would add an unused instance argument to each); the main theorem after
  `measureReal_empirical_eq_le` and before `end`, without its own
  `[MeasurableSpace α] [MeasurableSingletonClass α]` binders, which line 141 supplies in the same
  order; the draft's `open ClassicalLean.InformationTheory` dropped (the namespace). Verdict
  GENERALIZED (review r3), said in the docstring.
- **140:** `open Finset in` on both declarations; the draft's two Mathlib import lines not added (the
  cut measured the draft without them); `show` lines that change the goal become `change` if the four
  flags warn; `hpos` kept as drafted, its docstring saying it is the positive definiteness of the
  Toeplitz matrix `(γ (i − j))_{i, j < n + 2}`, written out.
- **142:** CovarianceDirections gains `import ClassicalLean.Algebra.MinMax`. `isSymmetric_covLin`
  becomes a public theorem of the module, inside `section Directions`, beside `covOp` and `covLin`, with the `PrincipalComponentsAux` namespace dropped and every reference
  shortened; it stays public because the main theorem's statement names it (review r6's MAJOR
  against s1); it keeps its own binders, which shadow the section's (as every 142 declaration does);
  its `first | … | …` is cut to the branch that fires alone (the cut measured each; if both do, the
  first); it has no hypothesis, so no witness. The main theorem follows it in the same section,
  keeping its own binders and its statement as drafted; review r6's verdict GENERALIZED against the
  plan row is said in the docstring, round 71 and the report, and job 1's statement review
  judges it again. The two `Fin.castLE hk` index the `k` largest eigenvalues, Mathlib's eigenvalues being
  sorted largest first (`eigenvalues_antitone`, as API-CREDIT-1.md line 149 records it checked).
- **144:** NeymanPearson gains `import ClassicalLean.InformationTheory.Entropy`; `open
  ClassicalLean.Simplex in` on the theorem (for `relEntropy` and `mul_log_le_relEntropy`); after the
  118 block, before `end`.
- **Row 70:** FiniteGame's lines 970 to 979 (the `open … in` line, the docstring and the example) are
  replaced by `lean/LEAN-34/data/w70.lean`'s block, line 980 kept blank; d2006-r2-s1 is not used
  (claude-ai's ruling; Dustin may veto: his veto puts d2006-r2-s1's two examples, its lines 6 to 28,
  in place of lines 970 to 979 instead, in place of the draft's top-level `open` lines 3 and 4 the
  first behind `open MeasureTheory ProbabilityTheory in` and the second behind that line and
  `open scoped ENNReal in`, the first docstring put in rule 2's form ("The hypotheses of `name` hold
  together: …"; the draft says "hold together for a kernel …"), and review (e) judges them). No other line of FiniteGame changes.
- **Row 163** (last, in its own commit, after row 70): ChannelCapacity gains
  `import ClassicalLean.Probability.TwoStateChain` after its last import line (line 8); the three
  theorems of `lean/LEAN-34/data/r163.lean`, their statements and `open … in` lines as there, go inside
  the namespace after `mutualInfo_bsc_half` and before `end` (line 162); their proofs are this
  session's (the row's route: `vecMul_pow_apply_one` at `s = t = ε`, started at each symbol, for the
  column-1 entry of row `a` of the `n`-th power, and the rows' sums for its column-0 entry (the cut's
  list of tools); then `mutualInfo_bsc_le` and `mutualInfo_bsc_half` at `εₙ`, which lies in
  `[0, 1]`; `tendsto_vecMul_pow_apply_one` and the continuity of `Real.binEntropy` for the limit), with
  private helpers as the "Every item" bullet allows; three witnesses after line 174 (rule 5). Each
  docstring names the row ("Row 163 of MATH-PLAN-library-2's bridges file") and says the statement is
  claude-ai's; the module docstring lists the new results, credits row 163's statements to
  claude-ai and its proofs to this session, and its line 42 ("The two witnesses at the end of the
  file …") counts the five witnesses. No other line of ChannelCapacity changes.

## Scope

- **Branch.** `lean-34` from `02ac649` in `~/lean/classical-lean-paper-crypto`, made after Dustin
  approves your plan. Nothing pushed. No sudo.
- **You may change in the repository:** the five home modules above and ChannelCapacity (row
  163), and in them only: new declarations inside the namespace block (the Goal list); the three import
  lines named; the module docstrings' lists of results (and in ChannelCapacity's docstring its
  sentence on the witnesses, line 42, brought up to date, with one sentence crediting row
  163's statements to claude-ai and its proofs to this session); witnesses after the last line (rule 5); in FiniteGame, lines 970 to 979 replaced by row 70's block (w70's,
  or under Dustin's veto d2006's two examples, or under rule 9's undo the old block without the
  parenthesis of lines 974 and 975). Also
  `tools/vacuity_reviewed.txt` (rule 4 only), `records/`, and `HANDOFF.md` sections 1 and 4 and
  `ROADMAP.md` (job 4).
- **You may not change:** any other module, any existing declaration of the six (the type dump
  checks it), any other import line, `ClassicalLean.lean`, anything else under `tools/`, `.github/`,
  `records/rules.toml`, the lake files, `HANDOFF.md` section 6 (its drift check hashes the text
  outside the generated block too). Needing to is a stop: report it.
- **You may write in the lane:** the plan, the report and the push-review file through `ds_file`;
  rows from 164 in the bridges file (job 5b). Nothing else.
- **Off limits:** the main clone `~/lean/classical-lean` and its `master`; `~/break-it-5`;
  `~/trading`; `~/lean/recheck` (`run-recheck.sh` is run as gate 7, not edited); every earlier
  order's folder under `~/lean/` (read only; `~/lean/lean33-checks/` is the source of your helpers);
  Dustin's `~/.config/classical-lean/banned-terms` (the scanner reads it; never print or copy it);
  every GitHub branch (no push, no delete); `/data/api-credit/` (read only); `~/api-credit/` and
  `/tmp/claude-ai-*/` (claude-ai's).
- **The night window and the memory cap,** as `ev.sh` enforces them (its header names the window;
  rule 36: name the window, do not copy its times). Before each whole-library run, log `pgrep -ax
  lean` through `ev.sh --nolean` (rc 1 when none runs) and wait while another Lean process runs;
  reviewers run no Lean while you do; claude-ai starts no Lean run on DSMain while this session
  runs, unless Dustin says so. Start gate 7 only when it can finish before the midnight timer (its
  duration in MERGE-3's run is in the cut's list). Every whole-library run under `ev.sh --cap` or
  `rootrun.sh`; never two Lean runs at once; read `crontab -l` and `systemctl --user list-timers`
  before you start; `~/.elan/bin` on `PATH`.

## Check, then read

Check these sha256s first; if any differs, stop and say which:
- this order, `lean/LEAN-34/order.md`: the value in Dustin's prompt;
- `lean/LEAN-34/data/w70.lean`, `lean/LEAN-34/data/facts.txt`, `lean/LEAN-34/data/cut-facts.txt`,
  `lean/LEAN-34/data/cut-facts-2.txt`, `lean/LEAN-34/data/r163.lean`,
  `lean/LEAN-34/data/hints.py` (`73258ea6eeb10e84c0173f7ae137dcc2d9d2114997203adb8ee4cc9e4586ec88`),
  `lean/LEAN-34/data/hints.out` (`b9c525da5ca6388c81da8c15fd6bf4aa7d6187554a99d1f5c3a16398e6343533`),
  `lean/LEAN-33/scripts/TypeDumpPI.lean`, `lean/LEAN-33/scripts/g8-typediff.py`: the values above;
- `lean/LEAN-33/order.md` `65337229ae40c151ebb60e9693125162e5db9defeaef80a1d4bfe72c850ae4c3` (the
  pattern this order follows) and `lean/LEAN-33/report.md` `11c7482a69fea652d39ad0cb91c5a3cd0fe3b71c3f853649a6c94446f2187b5b`;
- `lean/MERGE-2-order.md` `81894b5bc85a6ee6858f7a1d8b065ee17ff5034f21df9ef68803cded13e4251a` (setup,
  gates and push review on DSMain);
- `lean/VACUITY-3-ruling-3.md` `aa0d17e403031b81d0e0803c3308002ed985b416d788980de0f61cc79e13a4f2` and
  `lean/VACUITY-3-report.md` `f5a685bfa47740b8c9d6534f7db58ef7dfafb1f6e483a8e11a82ee20445ab106`;
- `lean/CLOUD-LANDING-PLAN-2.md` `26da22cef5604286b2b4b8fdfed4ec9fd70fb5c8520cb5dbfcd7b5c8411051a5`;
- MATH-PLAN-library-2.md `6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166`;
- `lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md`: `494bf24dd51961c835bb4df8d4f7c8fa2c61ea58ece0b66ae7d5bc434bb0523f`;
- the six carry files in `/data/api-credit/20261019/carry/`: the values above;
- the helpers and census tails (Setup 1); and the five modules at `02ac649`, which must have the
  `04e4a38` sha256s above (the cut: all five equal), and ChannelCapacity and TwoStateChain, which must have their
  `02ac649` sha256s above: a difference is a stop, since every line number this order gives in them is `04e4a38`'s
  (ChannelCapacity's and TwoStateChain's are `02ac649`'s).

Then read: in the repository `records/README.md`, `HANDOFF.md` sections 1, 4 and 6 (all 21 rules),
the five home modules and ChannelCapacity in full, TwoStateChain's statements, the last round's fragment, and MERGE-3's and LEAN-33's INDEX and
CLAIMS rows (the pattern for yours); in the lane the orders named above (LEAN-33's in full; MERGE-2's
Setup and Job 4), LEAN-33's report, VACUITY-3-ruling-3.md, the VACUITY-3 report's finding 2,
CLOUD-LANDING-PLAN-2.md rulings 2 and 5, MATH-PLAN-library-2.md section 7's rows 118, 122, 140, 142
and 144, and the bridges file's last section; the six carry files, `lean/LEAN-34/data/w70.lean` and
`lean/LEAN-34/data/r163.lean` in full.

## Rules of this order

1. **Statements as drafted.** Each main theorem keeps its draft's statement, apart from the Goal
   list's changes and the move into its namespace; row 163's three keep the statements of
   `lean/LEAN-34/data/r163.lean` (claude-ai's, from the bridges file's row). Never weaken, restate or add a hypothesis to make
   anything easier. A statement you find false is reported with its counterexample and narrowed,
   said plainly in its docstring, round 71 and the report; never dropped silently.
2. **Namespaces and imports.** Every new declaration, private ones included, sits inside its home
   module's namespace block; the axiom gate checks only constants under `ClassicalLean`. Only the
   three import lines named in the Goal list are added; no other import line anywhere changes.
3. **No existing declaration changes** (HANDOFF rule 14). A type dump of the whole library
   (`TypeDumpPI.lean`, through `rootrun.sh`, because it imports `ClassicalLean`) at the records
   commit and again at G (rule 7), compared by `g8_typediff.py diff`, read by its `DIFF` line (its
   exit code is 0 whenever nothing is CHANGED, even with REMOVED lines): predicted `removed=0
   changed=0 proof_only=0`, and `added=` the new constants (job 3). A `REMOVED` or `CHANGED` line is a
   stop. A `PROOF-ONLY` line is listed and explained as rule 14 says, and reported as a miss of this
   prediction: claude-ai measured the import lines alone at the cut (above: the two of
   items 142 and 144 together, then row 163's). A difference
   between `added=` and job 3's list confined to auxiliary names is listed and explained, not a
   stop. A new warning in an existing declaration is a stop (Scope). Row 70's swap removes one
   `example` and adds one, which are not constants, so it does not show.
4. **The vacuity gate as the repository has it.** A flag or an UNCHECKED verdict on a main theorem
   makes that item not closed (rule 9); row 163's three theorems count as main theorems. On a helper: rewrite it, remove it if Mathlib or `simp`
   already does its job, or list it in `tools/vacuity_reviewed.txt` as HELPER with a one-line reason
   its module's reviewer checks. A VACUOUS-PENDING entry makes the item not closed.
5. **Witnesses** in HANDOFF section 4's form (rule 2's form: `example := Full.name (x := …) h₁ h₂ …`,
   every chosen argument by name, optional `open … in` lines of their own and no other `open` than
   the module's top-level ones, the docstring "The hypotheses of `name` hold together: …", none of
   the six forbidden words, one inline block with no helper declarations; not degenerate as rule 3
   and VACUITY-3's ruling 3 say). Nine blocks in all, each after its module's last line:
   - five new ones, one for each item's main theorem (118's and 144's in NeymanPearson after its two
     witnesses), starting from the hints above;
   - three for row 163, one for each of its theorems, in ChannelCapacity after its two witnesses,
     starting from r163.lean's trial witnesses (`ε = 1/4`, `n = 3`, `p = ![1/3, 2/3]`), put in rule 2's form;
   - row 70: `lean/LEAN-34/data/w70.lean`'s block in place of FiniteGame's lines 970 to 979 (Goal
     list).
   Log `date +%s` through `ev.sh` when you start each of the eight new witnesses; one still missing
   1800 seconds later makes its item, or row 163, not closed. The supplied block is checked like any witness: it
   is starting material, not exempt.
6. **Records.** As `records/README.md` says. The records-first commit: this order's copy, its INDEX
   row (`| LEAN-34 |`) and CLAIMS row at the bottom, the push of MERGE-3 appended to MERGE-3's
   INDEX and CLAIMS rows (records/README.md rule 2: the next order's records commit records the
   push, as the cut gives it above), and round 71's fragment naming the six module files by full path.
   Round 71's fragment gives each module's theorem-constant count from the census (rule 27)
   and gets its commit hashes in a follow-up edit once they exist, never predicted.
7. **Predict, then measure; the tree that counts.** As LEAN-33's rule 7: an evidence folder
   `~/lean/lean34-checks/` with `evidence.log`; every prediction file hashed into the log (`hl.sh`)
   before its run; hashes in records and the report by script, never typed; git, hash and records
   commands as `ev.sh --nolean`; every commit through `ev.sh --nolean` as `git commit -F <message
   file>` with a label starting `commit-`, then `COMMIT <hash>` appended to `evidence.log`; a helper
   you must run after generating a message's `Evidence:` line, and before its commit, takes a label
   starting `commit-`. Every gate runs on the clean tree of the last commit that touches anything
   outside `records/` (call it G); later commits touch only `records/`.
8. **Reviews.** Job 1's statement review, then six cold reviews once their text is final: (a)
   NeymanPearson (118 and 144), (b) MethodOfTypes (122), (c) YuleWalker (140), (d)
   CovarianceDirections (142), (e) FiniteGame's row-70 witness, (f) ChannelCapacity (row 163), each by a fresh subagent that has not
   seen your work, with a brief built by script as rule 26 says. Each brief caps its reviewer at 40
   tool calls; at the cap it writes what it has and lists what it did not check, and anything listed
   as not checked gets a fresh reviewer for those parts only before the commit. A module review
   checks each statement against its plan row (row 163's against the bridges file's row) (FAITHFUL, GENERALIZED or WEAKER; WEAKER is a finding),
   every hypothesis used, each witness against rule 5, every new declaration in the namespace, the
   import lines, every private helper's statement and whether Mathlib or the module already has it,
   and no main theorem whose conclusion is a recursive predicate that is `True` everywhere. A review
   with findings ends with a confirming pass on the fix only, by a fresh reviewer. At most two
   fix-and-confirm rounds; an item not clean after two is not closed.
9. **Not closed.** An item not closed is undone by a new commit (never a reset): its declarations,
   witness, import line, module-docstring entries and vacuity-list entries removed, and round 71, the CLAIMS row and the
   report saying which item and why. The others go on. Row 70's witness not clean after two rounds is
   undone the same way, by restoring lines 970 to 979 as they are at `02ac649` with the docstring's
   parenthesis at lines 974 and 975 removed (Dustin's ruling of 2026-10-13: a claim in the library
   must be checkable from the library), a docstring-only change; round 71, the section 4 line
   (job 4) and the report say so. Row 163 not proved, or not clean after two rounds, is undone the
   same way (its theorems, private helpers, witnesses and import line removed, and its module docstring
   restored to its `02ac649` text, by a new commit) and
   returns to LEAN-38 with rows 160 to 162; round 71, the CLAIMS row and the report say so.
10. **Master does not move under you.** If `origin/master` or GitHub's `master` is not `02ac649` at
    "Before approval" or when you write the push-review file, stop and report: claude-ai then writes
    the merge step. Never merge or rebase anything yourself.

## HANDOFF's rules in this session

Every rule of `HANDOFF.md` section 6 applies. How, for this order:

| rule | here |
|---|---|
| 1, 2, 3, 10, 15, 18, 19, 22, 28 | as written. Rule 19: credit each proof to its draft (the API-credit pipeline's Claude Opus 5.5 through the Anthropic Batch API, lean/API-CREDIT-CARRY-1.md), adapted by this session; row 70's block to claude-ai, after VACUITY-3's fresh reviewer's suggested fix (lean/VACUITY-3-report.md, finding 2); row 163's statements to claude-ai (from the bridges file's row, found by MERGE-3's search), its proofs to this session. Rule 22: every quote in round 71's fragment is checked by a script with a planted misquote (the quote checker LEAN-33 used may be adapted). |
| 12 | Reviewers work in `~/lean/lean34-checks/reviews/<label>/`, outside the repository, with `PYTHONDONTWRITEBYTECODE=1`, copy any repository script before importing it; `git status --porcelain` unchanged after each review; the tree is not touched while a reviewer runs. |
| 14 | Rule 3 above: the type dump at the records commit and at G, by the lane pair, after its controls (Setup 5). |
| 17 | Each reviewer writes its report to a file and returns only its sha256; you hash the file with `hl.sh` and compare before you open it. |
| 20 | Scratch files and modules are elaborated by `el.sh` (it carries the four flags); linter results count only from `lake build`. |
| 23 | `ev.sh` and `hl.sh`, tested in Setup 2. Every write, hash and edit of an evidence or records file runs through them, or is listed in the plan and round 71's fragment before the commit that carries it (records files written with Write or Edit are hashed with `hl.sh` before their commit); a commit runs only when its gates exited 0 in the same run. |
| 26 | Every review brief is built by a script from `HANDOFF.md`, saved with its sha256 before it is sent, and quotes verbatim rules 14, 17, 18, 19, 20, 22, 23, 26 and 31, cut only with `[...]`; briefs (a) to (f) also quote HANDOFF section 4's "Satisfiability witnesses" paragraph verbatim. Use the brief builder LEAN-33 used (Setup 1), tested in Setup 2. |
| 27 | Theorem-constant counts, total and per module, from `mkcensus.sh` with the census tails on scratch copies of each final module, before any gate; the module count from `env.header.moduleNames` of a scratch file importing `ClassicalLean`, run through `rootrun.sh`, at the records commit and at G (predicted equal: no module is added; a scratch file importing only the five modules would grow by Algebra.MinMax, which 142's import line brings into CovarianceDirections' closure, so it is not the measure; row 163's import line brings TwoStateChain, already in the root's closure), and the build's job count (predicted 4193 at both). |
| 31 | Job 1's statement review is in before any landing; every new declaration, private helpers included, gets its module's cold review before its commit; a review fix that touches a proof line gets its delta check (re-elaborated with `el.sh` and the module rebuilt through `ev.sh`) before its commit. |
| 36 | Briefs and predictions carry a date beside every clock time; each brief gives the dated end of its own run; `briefcheck.py` passes every brief before it is sent. Witness time limits in epoch seconds. |
| 37 | `el.sh` refuses a run while a name is not probed: one probe file per draft, one for row 163's statements and one for the witness blocks, `#check @Name` lines for every Mathlib and library name in the text as it will land, run with `EL_PROBE=1`. |
| 38 | `rootrun.sh` for the type dumps, the bridge search, the report tool and any census that imports `ClassicalLean`; tested before first use (Setup 2). The gates are not wrapped. |
| 39 | Stage by path. A commit message is written after its gates ran, says only what `evidence.log` shows, names in its first paragraph any linter or option switched off or on, and ends with the line `evcite.py` prints, generated last, followed only by the session's attribution trailers. Job 5e runs `citecheck.py`. |

## Before approval (read-only in the repository)

1. `git fetch origin` in the worktree. Then, each predicted and checked: `origin/master` and
   `git ls-remote github master` both `02ac649b17f66e39327022462ee4d3d9a73b62d4`; `git status --porcelain` empty. If not, stop (rule
   10).
2. Check the hashes and read the read list.
3. Check `crontab -l`, `systemctl --user list-timers` and `free -g`.
4. Write your plan with `ds_file` (project `lean`, job `LEAN-34`, kind `plan`): the jobs in order,
   every prediction you can make now, the order of the items (a suggestion: 140, the most
   self-contained; then 118 and 144 together; then 142; then 122, the longest; then row 70; row 163 last, in its own commit), and the
   plan-fit check: for each item its plan row beside the draft's statement, every difference named
   (at least: 118's `hsize : 0 < …` hypothesis and its ratio in `[0, ∞]`; 122's `p ≥ 0` in place of a
   probability vector, its `hq` and `hpq`; 140's order `n` to `n + 1` with `φ` and `b` given, and
   `hpos` written out; 142's eigenvalues read through `isSymmetric_covLin`, with `k ≤ card ι`, and `w`
   and `hw` bound for both clauses, used only by the first (r6's minor, not taken); 144's `hsupp`; row 163's three statements beside the bridges
   file's row 163: at least `hε0 : 0 < ε` as the row has it, where `0 ≤ ε` would also do for the first
   two, and the input law's `hp0` and `hp1`). Then stop and wait for Dustin's approval.

## Setup (after approval)

1. **The helpers.** Make `~/lean/lean34-checks/scripts/` and `~/lean/lean34-checks/census/`. One
   script copies LEAN-33's helpers and census tails (the cut's list above; their full sha256s are in cut-facts.txt)
   after comparing all 64 characters of each source hash, and changes only the path lines the cut
   lists (each `lean33-checks` to `lean34-checks`) and `probecheck.py`'s one `BASE = ` line to
   `BASE = '02ac649'`, each refused unless the file has exactly that many such lines. LEAN-33's
   `allowlist.txt` is copied into `~/lean/lean34-checks/` byte for byte; its `seed.txt`, if any, is
   not (your own probes seed the check). You may add to `allowlist.txt` a tactic name `el.sh` refuses
   (a token that is not a constant), with a reason; `el.sh` logs the list's new hash. Copy the lane's
   two type-dump files, `lean/LEAN-34/data/w70.lean` and `lean/LEAN-34/data/r163.lean` into
   `~/lean/lean34-checks/inputs/` (`g8-typediff.py` as
   `g8_typediff.py`) and check their sha256. Log every new sha256 with `hl.sh`. Then write
   `pred-setup.md` and hash it.
2. **Tests before first use,** each logged and predicted, as LEAN-33's Setup 2: the empty-prediction
   refusal, exit 97; `ROOTRUN_BUILD=false rootrun.sh` refused, exit 95, the command not run; the
   real-build `rootrun.sh` test, its build line before its command line at the same head; the
   citecheck planted pair on a scratch copy of the log, plus a third case with a `commit-…` helper
   line between the `evcite.py` run and the `COMMIT` line, predicted `OK`; `el.sh` refusing a
   scratch file that uses an unprobed name (logged `NOT RUN`), then running it after its probe, and
   the allowlist's hash logged on its first run and not again on its second; `briefcheck.py`
   refusing a planted brief line with a time and no date; the brief builder printing a brief that
   quotes the nine rules of rule 26 verbatim and passes `briefcheck.py`. A test that does not behave
   as predicted is a stop.
3. **Branch.** First, through `ev.sh --nolean setup1 …`: `git fetch origin`; `origin/master` and
   `git ls-remote github master` both `02ac649…`; `git status --porcelain` empty (rule 10). Then
   `git switch -c lean-34 02ac649b17f66e39327022462ee4d3d9a73b62d4`.
4. **Records first,** one commit, no `.lean` file (rule 6):
   `records/orders/<UTC>__claude-ai__order-lean34-karlin-rubin-sanov-durbin-levinson-pca-bretagnolle-huber-bsc-cascade.md`,
   the INDEX and CLAIMS rows, MERGE-3's push, and round 71's fragment
   `records/rounds/<UTC>__round-71-karlin-rubin-sanov-durbin-levinson-pca-bretagnolle-huber-bsc-cascade.md`.
   check_records then: PASS 140.
5. **Before runs at the records commit,** predicted from the facts: build rc 0, 4193 jobs, 0
   warnings; AxiomGate PASS 3527; rule 27's module count (a scratch file importing `ClassicalLean`,
   printing `env.header.moduleNames.size`, through `rootrun.sh` while HEAD is the records commit):
   5729; the type dump,
   `rootrun.sh td-before "<pred>" lake env lean ~/lean/lean34-checks/inputs/TypeDumpPI.lean`, whose
   `td-before.out` ends with `/usr/bin/time -v`'s report: keep its lines that start with `{` in
   `td-before.jsonl` by a script run through `ev.sh --nolean`, and check that every dropped line is
   time's report; then `g8_typediff.py check td-before.jsonl`: rc 0, 4009 records (3527 thm, 482 def), elided 0,
   missing_fields 0. Then the diff tool's controls on copies of `td-before.jsonl`, each predicted and
   read by its `DIFF` line: the file against itself, all zeros, rc 0; one record's `ppPI` edited,
   `changed=1`, rc 1; only its `pp` edited, `proof_only=1`, rc 0; one record deleted, `removed=1`, rc
   0 (the exit code does not catch it; the `DIFF` line does).

## The work

### Job 1: statements and their review

1. Probes (rule 37): one file per draft, one for row 163's statements and one for the witness blocks; each new witness's names are
   probed before it is written.
2. For each draft, a scratch statement file outside the repository that imports its home module (and
   Entropy for 144, MinMax for 142; for row 163 the same from `r163.lean` without its trial witnesses,
   importing ChannelCapacity and TwoStateChain), repeats the module's top-level `open` lines, and holds
   `namespace <home namespace>`, the draft's declarations as they will land with every theorem's and
   lemma's proof `sorry` (defs keep their bodies), and `end`; the statement file for 122 keeps the
   draft's `variable` line and puts a copy of MethodOfTypes' line 141 just before the main theorem,
   since a module's `variable` lines do not reach a file that imports it (the files for 118, 140,
   142 and 144 need none: those drafts bind their own types). So `el.sh` reads
   only the new text (it reads a scratch file whole), and the full names are the ones the module
   will have. The 122 statement file carries the same `omit … in` lines as the landing will (the
   cut's list). Elaborate each with `el.sh`, predicted rc 0 with `sorry` warnings and any other
   warning you expect (such as an unused section variable that only a `sorry` proof leaves unused)
   listed in job 1's prediction file, hashed before the run; an unlisted warning is a miss, checked
   again when the proof is in. Hash the statement files. Scratch files for
   work on a witness likewise import the module and hold only the block.
3. A mechanical check that the move changed no meaning: for each main theorem, its type printed
   with `set_option pp.fullNames true in #check @name` from the draft (a scratch copy with the line
   appended) and from the statement file, compared by a script (the type comparer LEAN-33 used may be
   adapted): only the namespace prefix may differ (for 142 also the helper's name inside the
   statement, `PrincipalComponentsAux.` becoming the module's namespace; for row 163 `r163.lean` stands
   for the draft and nothing may differ). Log the result.
4. One statement review of the five and of row 163's three, by one fresh subagent (each statement
   against its plan row, row 163's against the bridges file's row 163, and against its draft or
   `r163.lean`; the Goal list's changes, the namespaces, the three import lines). Its verdict is in
   before job 2.

### Job 2: land, one commit per module

In the plan's order, per module: the declarations in place (the Goal list), the import line if any,
the witness; `el.sh` on the module (rc 0); `lake build` of the module and of every module that
imports it (the cut's list; at `04e4a38` only CovarianceDirections had one, Statistics.ResidualVariance)
through `ev.sh` (0 errors, 0 warnings); `python3 -I tools/banned_vocab_scan.py ClassicalLean` (the
form every earlier order used; the credit wording as LEAN-33's and CLOUD-MATH-2's landed modules have
it, which passed the scan); the vacuity gate and the check scripts (a copy of the vacuity gate whose only change is
its import line may run on one module while the root is not rebuilt; the real gate runs in job 5a);
the module's cold review (rule 8) with any fix and its confirming pass; one commit staged by path,
then its `COMMIT` line. Then row 70 in FiniteGame the same way, with review (e), in its own commit. Last, row 163 in
ChannelCapacity the same way, with review (f), in its own commit (`lake build
ClassicalLean.InformationTheory.ChannelCapacity`; nothing imports it but the root file, which 5a
builds).

### Job 3: predictions

Once every module's text is final (after the reviews) and before job 5: a prediction file, hashed,
with the module count and job count (rule 27's measurements); the theorem constants by census (base 3527
plus the census of each final module's new constants, per module: `mkcensus.sh` on a copy of each
changed module at `02ac649` and on its final copy, the new constants being the difference of the
two `.names` lists); the type dump's `added=` list, the difference of the two census-all lists for
the changed modules (the dump keeps only `thm` and `def` constants, so a name of another kind in that
difference is listed as an expected absence, and private names are compared by their user-facing
names, `privateToUserName`, because the census runs on copy files whose module name differs) (rule
3); check_sorry and check_records PASS 140; the vacuity gate's verdicts and reviewed-helper
count, and its tests (89 verdicts, 47 flagged, 3 UNCHECKED, 0 mismatches); `banned_vocab_scan.py ClassicalLean` PASS, 140 files and
the root file, 0 hits; gate 7 ALL PASSED, 4193 jobs, 140 modules 0 failed, 3527 plus the
census count, the three standard axioms, the planted fault named; the drift check PASS; the bridge
search's and report tool's numbers by hand from MERGE-3's runs (say they are hand predictions); the
records-file count. Until then do not run the axiom gate on the changed modules. A miss is reported,
never fixed by changing what was measured.

### Job 4: documents

- `HANDOFF.md` section 1: after MERGE-3's paragraph, a dated LEAN-34 paragraph (round 71):
  the five items by name, module and item number, one line each, 122's and 142's GENERALIZED
  verdicts said; row 70 re-witnessed; bridge row 163's three theorems in ChannelCapacity; the counts predicted by job 3, to be re-measured by job 5a.
- `HANDOFF.md` section 4, the "Satisfiability witnesses" paragraph: a dated line (the day you write
  it, UTC) saying row 70 is re-witnessed by this order with a kernel that depends on the parameter
  (the hand-worked value removed from the docstring, or, under Dustin's veto, checked by an
  `example`), and that with LEAN-33's rows 7 and 8 no row uses the
  older rows' forbidden-word exception any more. Change nothing else in section 4. Section 6: no
  change at all.
- `ROADMAP.md`: after section 1.27, a section 1.28 for items 118, 122, 140, 142 and 144,
  row 70 and bridge row 163, landed from below the plan's cut by order LEAN-34, in section 1.27's form.
- One fresh cold reviewer reads the documents commit's diff alone (about 15 calls); a review with
  findings ends with a confirming pass on the fix only (rule 8).

### Job 5: the end checks, in this order

- **5a. The gates,** on the clean tree at G, each through `ev.sh` with its prediction, in MERGE-2's
  forms (its job 4a): build, AxiomGate, VacuityGate, the vacuity tests, check_sorry, check_records,
  the drift check, `banned_vocab_scan.py ClassicalLean`, and gate 7. Then rule 27's module count at G
  through `rootrun.sh`, predicted equal to Setup 5's. Then the type dump at G through
  `rootrun.sh` as in Setup 5, its `{` lines kept in `td-after.jsonl` and the dropped lines checked,
  `g8_typediff.py check td-after.jsonl`, then `g8_typediff.py diff td-before.jsonl td-after.jsonl`
  (rule 3). A gate that fails is a stop: 5b and 5c do not run.
- **5b. The bridge search,** through `rootrun.sh`, at G:
  `python3 -I tools/bridge_search.py --diff records/bridges/MERGE-3/ --out ~/lean/lean34-checks/bridges/LEAN-34`;
  rc 1 means candidates to review. Report NEW and GONE pairs and shapes. Check each NEW
  import-unrelated pair and each NEW shape for a theorem whose proof needs both sides; a real one is
  appended to the bridges file from row 164, through `ds_write_staging` in append mode with
  `expect_sha256` its value above (if the write is refused, stop and report), in the file's columns.
  Say in the file and the report exactly how the pairs were checked: which were read statement by
  statement, and how the rest were judged (plan 2's ruling 5). The three new import edges
  (CovarianceDirections imports MinMax, NeymanPearson imports Entropy, ChannelCapacity imports
  TwoStateChain) can make pairs the baseline listed as import-unrelated related: list each such GONE
  pair or shape with that reason (MERGE-3's shape key `stochastic matrix:
  InformationTheory.ChannelCapacity × Probability.TwoStateChain`, row 163's own, may be one). Items
  142 and 144 are the plan's own bridge rows, and row 163 is already the file's row 163, all landed
  here; none is a new row of the bridges file. Write the
  new baseline to `records/bridges/LEAN-34/`; its commit touches only `records/`.
- **5c. The report tool,** through `rootrun.sh`, at G, once; a report, not a gate; predicted by hand
  from MERGE-3's `report.out`. List every `CLOSES` line that names a theorem of this order.
- **5d. Close the records:** round 71's follow-up edit with the commit hashes and the measured
  counts, its quotes checked by script (rule 22); the CLAIMS row closed and the INDEX row's state set;
  one records-only commit. Then check_records again at the final HEAD, predicted PASS 140.
- **5e. citecheck:** every commit of this order, `git rev-list 02ac649..HEAD`, by
  `citecheck.py ~/lean/lean34-checks/evidence.log --message <its message file> <hash>` in one loop (the
  message from `git log -1 --format=%B <hash>`; each `OK`), and the repository run `citecheck.py
  ~/lean/lean34-checks/evidence.log ~/lean/classical-lean-paper-crypto 02ac649` (predicted rc 0,
  every commit `OK`).
- **5f. Report** with `ds_file` (kind `report`), laid out like LEAN-33's report: in short; setup and
  the helper tests; for each item its final statement, witness and review verdicts; row 70's
  witness; row 163's three theorems, witnesses and review; the type-dump diff; predicted beside measured for every gate and count; the bridge diff
  and how it was checked; 5c's `CLOSES` lines for this order (or "none"); the commits; 5e's output;
  misses and anything not closed; and the push command as one line, not run:
  `cd ~/lean/classical-lean-paper-crypto && git push origin lean-34:master && git push github lean-34:master`.
  Say that the GitHub push starts a CI run on `master`, and that Dustin runs it only after claude-ai
  has checked the push-review file.
- **5g. Push-review file** with `ds_file` (subdir `data`, name `LEAN-34-push-review.txt`), by one
  script, each command followed by its full output: `git rev-parse HEAD`, `git status --porcelain`,
  `git ls-remote origin master`, `git ls-remote github master` (both must still be `02ac649`, rule
  10), `git merge-base --is-ancestor 02ac649 HEAD` with its exit code, `git rev-list --count
  02ac649..HEAD`, `git log --name-status --format='== %h %cI %s' 02ac649..HEAD` (files under
  `records/bridges/` as a count), `git diff --stat 02ac649 HEAD`, `git diff --name-only 02ac649 <G>
  -- ClassicalLean.lean tools .github ':(glob)lakefile*' lake-manifest.json lean-toolchain
  records/rules.toml` (predicted: only `tools/vacuity_reviewed.txt`, if a helper was listed), `git
  diff --name-only 02ac649 <G> -- ClassicalLean` (predicted: exactly the five modules and ChannelCapacity), `git diff -U0
  02ac649 <G> -- ClassicalLean | grep '^[-+]import'` (predicted: exactly the three import lines, each `+`), `git
  diff -U0 02ac649 <G> -- ClassicalLean/Analysis/FiniteGame.lean` (predicted: every hunk within old
  lines 970 to 979, the new lines being the w70 block, which has no trailing blank line, so old
  line 980 stays the one blank line before item 66's example; under the veto, d2006's two examples as
  the Goal list adapts them; under rule 9's undo, only lines 974 and 975 changed), `git diff -U0 02ac649 <G> --
  ClassicalLean/InformationTheory/ChannelCapacity.lean` (predicted: lines added only, except in the
  module docstring: the import after line 8, the new declarations before line 162, the witnesses
  after line 174; under rule 9's undo of row 163, no hunk), the type-dump `DIFF` line, `git diff --name-only <G> HEAD` (only `records/`), 5d's output
  and 5e's two outputs. Report its sha256. Then stop: claude-ai reviews it before Dustin pushes.

## Done means

- Branch `lean-34` from `02ac649`, clean tree, nothing pushed; its first commit is the records
  commit and holds no `.lean` file; then one commit per module, one for row 70 and one for row 163; then documents;
  then records-only commits.
- The helpers copied, their sha256s logged, their tests run before first use as predicted.
- The five items proved with no `sorry` and no new axiom, as drafted with the Goal list's changes,
  or each narrowing said plainly, or reported not closed and undone by rule 9; 122 and 142
  GENERALIZED and said so.
- Row 163's three theorems proved with no `sorry` and no new axiom, with `r163.lean`'s statements, or
  undone by rule 9 and said so.
- Nine witnesses in rule 2's form, each checked by its review against rule 5, or an item, row 70 or
  row 163 undone by rule 9 and said so.
- The type-dump diff `removed=0 changed=0`, and `proof_only=0` or each PROOF-ONLY record listed and
  explained (rule 3); its `added=` list equal to the census's new constants, apart from differences
  listed and explained under rule 3 and job 3.
- Job 1's statement review and the six module reviews and the documents review saved and
  hash-checked, each ending in a confirming pass where it had findings.
- Every gate as predicted at G, or each miss reported; gate 7 ALL PASSED at G; after G only
  `records/` changed; check_records PASS at the final HEAD.
- The bridge diff reported with how it was checked; real bridges (if any) from row 164;
  the new baseline committed.
- Job 4's documents changed and named (section 6 untouched; the drift check passes).
- 5e: every commit `OK`.
- The plan and the report in `lean/LEAN-34/`, the push-review file in `lean/LEAN-34/data/`, hashes
  matching yours.

Then report in a few plain sentences: what was proved (row 163 too), the GENERALIZED verdicts of 122 and 142, the witnesses, the
gate results beside the predictions, any new bridge, the two files' hashes and the push command.
Dustin reads your replies carefully and is still learning to read code: plain words, and define a
technical term the first time you use it. When you need a decision from him, ask in one line with
your recommended answer first.

## Not in this order

- VACUITY-3 rows 31 and 32 (YuleWalker's two theorems; LEAN-36 with batch 6); plan rows 119 and 120.
- The noisy kernel for item 103's example in FiniteGame (lean/API-CREDIT-CARRY-1.md point 7, an
  optional MINOR; its Dirac kernel gives `0` on both sides).
- 140's `hpos` restated as `Matrix.PosDef` (review r6's minor; a new bridging proof).
- Bridges 160 to 162 and the pair-by-pair read of MERGE-2's and MERGE-3's searches (LEAN-38, plan 2
  ruling 5 and store row 20261021-001; row 163 is this order's last job); the twin search (TWINS-1,
  ruling 6).
- Deleting GitHub branches; any push.

## Revisions

- r1, review pass 1: MAJOR: 142's ruling to move `w` inside the first conjunct dropped (the moved
  form is equivalent, not wider); rule 27's module count taken through the root, not the five
  modules; the push line and the next ROADMAP section given a source in the cut list; unused section variables
  fixed by `omit … in`, with 122's list from the cut. MINOR: 140's `γ` not `0` past a lag; 118's
  arguments named; 144's `[MeasurableSpace ι]` attributed to the pipeline's minor not taken; 142's
  binders and `first`; importers from the cut; the veto's open lines and docstring form, and job 4's
  section-4 line for both cases; rule 9's undo drops the hand-worked parenthesis; w70's docstring
  gives the finiteness reason; gate 7's duration from the cut; rule 23's full clause; the five
  modules' hashes as a stop; 5g's FiniteGame hunks; the Mathlib citation; the credit wording.
- r2, review pass 2: MAJOR: 142's witness hint on `Fin 3` with `k = 2` and an explicit `w`. MINOR:
  140's hint with `n = 2`; the module count run in Setup 5 and 5a; the 122 statement file carries the
  landing's `omit` lines; row 70's three cases in the Scope, 5g and Done-means; 142's `w` described as
  bound for both clauses, used by the first; gate 7's verdict and duration; the module-hash line
  points to the cut; 142's section placement; 118's placement after the proof.
- r3, the confirming pass: expected warnings go in job 1's prediction file, not the plan; 142's `X`
  written out with its cast.
- r4, the cut (claude-ai, 2026-10-21, after MERGE-3 was pushed): the values measured at `02ac649`
  filled by script (`fill-cut.py`); MERGE-3's push note with its anchors; `pgrep -ax lean`; row 163
  added as the last job (Dustin's question of 2026-10-21 15:53 EDT; ruling, store row 20261021-015).
- r5, the cut's review pass 1 (one fresh subagent, 2026-10-21; PASS WITH FINDINGS, 0 BLOCKER, 1 MAJOR,
  12 MINOR; its report saved verbatim, sha256 `a00ec901502c6a61280d99cd94276b6fd931716abc23b52fb3765e40ce3ed43b`): MAJOR: the
  push-note script's assertions given exactly in a fenced block, and the CLAIMS row told from
  LEAN-33's. MINOR: d122's warnings counted from the full output; 122's `omit` list settled, and the
  "Every item" rule names the unused-instance linter; the cut's missed predictions named (they were
  logged); row 163's column-0 entry and the limit's Mathlib names; the veto's reach over every count;
  the undo removes docstring entries, and ChannelCapacity's sentence on its witnesses is updated;
  `r163.lean` copied into the inputs and TwoStateChain's hash checked; no root build in job 2; a date
  on every clock time; row 163's module facts gathered into cut-facts-2.txt, two line slips; how the
  row came to LEAN-38 said without misciting ruling 5; the lane inputs placed before the prompt.
- r6, the confirming pass (a fresh subagent, 2026-10-21; CONFIRMED WITH FINDINGS: 12 of 13 fixed, 1
  in part, 6 new MINOR; saved verbatim, sha256 `b2a5b84a9fff2b1c9e63ead4ec870b2d636a1b9db4210adaef00262dfa6f3c06`): ChannelCapacity's
  witnesses sentence is its line 42 only; the undo of row 163 restores the module docstring; the
  CLAIMS assertion reads the line without its newline; `sum_row_of_mem_rowStochastic` named and the
  Mathlib paths' source said; row 20261021-016 described as the slip it records (and -014's own
  "one show" corrected in the store, row 20261021-025); the `omit` rule limited to section
  variables' instances, a declaration's own binder kept (rule 1). Not reviewed again.
